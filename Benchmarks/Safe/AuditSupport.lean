import Benchmarks.Safe.Bytecode
import Solm.Refine

/-!
Executable differential-audit support, not a proof of refinement. The bytecode side uses EVM
`Xstep`; the AST side uses Solm's expression, storage, dispatch, and ABI implementations. Calls
replay the actual EVM call boundary, checking its kind, arguments, and incoming account map.
Gas witnesses come from the four GAS sites used by execTransaction. Unsupported AST forms and
exhausted test fuel are test failures. No theorem or axiom is introduced by this harness.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe.Audit

structure CallRecord where
  opcode : Operation
  before : State
  after : State

structure Trace where
  result : Except ExecutionException (ExecutionResult State)
  calls : List CallRecord := []
  gas : List (Nat × UInt256) := []

def trace (initial : State) (fuel : Nat := 100000) : Trace := Id.run do
  let jumps := D_J initial.executionEnv.code 0
  let mut state := initial
  let mut calls := []
  let mut gas := []
  for _ in [:fuel] do
    let opcode := (decode state.executionEnv.code state.machineState.pc).map Prod.fst
    match Xstep jumps state with
    | .error e => return { result := .error e, calls := calls.reverse, gas := gas.reverse }
    | .ok (next, halt) =>
      if opcode == some .GAS then
        gas := (state.machineState.pc.toNat, next.machineState.stack.getD 0 ⟨0⟩) :: gas
      if opcode == some .CALL || opcode == some .STATICCALL || opcode == some .DELEGATECALL then
        calls := { opcode := opcode.getD .STOP, before := state, after := next } :: calls
      state := next
      match halt with
      | some (.success, out) =>
        return { result := .ok (.success next out), calls := calls.reverse, gas := gas.reverse }
      | some (.revert, out) =>
        return {
          result := .ok (.revert next.machineState.gasAvailable.toUInt256 out),
          calls := calls.reverse, gas := gas.reverse }
      | none => pure ()
  return { result := .error .OutOfFuel, calls := calls.reverse, gas := gas.reverse }

inductive Stop where
  | returned (values : Option (List Value))
  | reverted
  | staticViolation
  | error (message : String)
  deriving Inhabited

structure Replay where
  frame : Frame
  evm : State
  calls : List CallRecord
  gas : List (Nat × UInt256)
  fuel : Nat := 20000

abbrev ReplayM := ExceptT Stop (StateM Replay)

def fromEval {α : Type} (result : EvalResult α) : ReplayM α :=
  match result with
  | .ok a => pure a
  | .revert => throw .reverted
  | .error e => throw (.error s!"Solm evaluator got stuck: {repr e}")

def eval (expr : Expr) : ReplayM Value := do
  let s ← get
  fromEval (evalExpr? config s.frame s.evm expr)

def evals (exprs : List Expr) : ReplayM (List Value) := do
  let s ← get
  fromEval (evalExprs? config s.frame s.evm exprs)

def boolean (expr : Expr) : ReplayM Bool := do
  let .bool b ← eval expr | throw (.error "expected boolean")
  pure b

def bindLocal (name : Ident) (v : Value) : ReplayM Unit :=
  modify fun s ↦ { s with frame.locals := s.frame.locals.insert name v }

def replayCall (opcode : Operation) (target : EVM.Address) (value : Int)
    (input : ByteArray) : ReplayM (Bool × ByteArray) := do
  let s ← get
  if opcode == .CALL && value != 0 && !s.evm.executionEnv.perm then
    throw .staticViolation
  let record :: rest := s.calls | throw (.error "missing EVM call boundary")
  let stack := record.before.machineState.stack
  let shift := if opcode == .CALL then 1 else 0
  let actualTarget := EVM.address (stack.getD 1 ⟨0⟩).toNat
  let actualValue := if opcode == .CALL then (stack.getD 2 ⟨0⟩).toNat else 0
  let actualInput := record.before.machineState.memory.readWithPadding
    (stack.getD (2 + shift) ⟨0⟩).toNat (stack.getD (3 + shift) ⟨0⟩).toNat
  if record.opcode != opcode || target != actualTarget || value != actualValue ||
      input != actualInput then
    throw (.error s!"call arguments differ at pc {record.before.machineState.pc.toNat}")
  if s.evm.accountMap != record.before.accountMap then
    throw (.error s!"incoming call account map differs at pc {record.before.machineState.pc.toNat}")
  modify fun s ↦ { s with
    calls := rest, evm.accountMap := record.after.accountMap,
    evm.substate := record.after.substate }
  pure (record.after.machineState.stack.getD 0 ⟨0⟩ != ⟨0⟩, record.after.machineState.returnData)

mutual
partial def execBody (body : Body) : ReplayM Unit := do
  for stmt in body do execStmt stmt

partial def execStmt (stmt : Stmt) : ReplayM Unit := do
  let s ← get
  if s.fuel == 0 then throw (.error "AST test fuel exhausted")
  modify fun s ↦ { s with fuel := s.fuel - 1 }
  match stmt with
  | .letDecl name _ expr => bindLocal name (← eval expr)
  | .letGas name =>
    let pc := match name with
      | "gasForCheck" => 3807 | "gasBefore" => 3832 | "txGasLeft" => 3925 | "gasAfter" => 3946
      | _ => 0
    let gas := (s.gas.find? (·.1 == pc)).map Prod.snd |>.getD ⟨0⟩
    bindLocal name (.int gas.toNat)
  | .assign origin ref expr =>
    let value ← eval expr
    let (frame, evm) ← fromEval (assignStorageRef? config s.frame s.evm origin ref value)
    if origin matches .storage then
      if !s.evm.executionEnv.perm then throw .staticViolation
    modify fun s ↦ { s with frame, evm }
  | .require expr => if !(← boolean expr) then throw .reverted
  | .ite cond yes no => execBody (if ← boolean cond then yes else no)
  | .while cond body =>
    if ← boolean cond then
      execBody body
      execStmt stmt
  | .return exprs => throw (.returned (some (← evals exprs)))
  | .emit _ args =>
    let _ ← evals args
    if !s.evm.executionEnv.perm then throw .staticViolation
  | .internalCall name args binder =>
    let values ← evals args
    let some decl := lookupCallable? contract name | throw (.error s!"unknown function {name}")
    let some locals := bindParams? decl.params values | throw (.error s!"bad arguments {name}")
    modify fun s ↦ { s with frame.locals := locals }
    let ret ← try
      execBody decl.body
      pure none
    catch
      | .returned values => pure values
      | stop => throw stop
    modify fun current ↦ { current with frame := resumeAfterInternalCall s.frame binder ret }
  | .lowLevelCall target value input okVar dataVar perm =>
    let .address target ← eval target | throw (.error "call target is not an address")
    let .int value ← eval value | throw (.error "call value is not an integer")
    let .bytes input ← eval input | throw (.error "call input is not bytes")
    let (ok, out) ← replayCall (if perm then .CALL else .STATICCALL) target value input
    bindLocal okVar (.bool ok)
    bindLocal dataVar (.bytes out)
  | .delegateCall target input okVar dataVar =>
    let .address target ← eval target | throw (.error "delegatecall target is not an address")
    let .bytes input ← eval input | throw (.error "delegatecall input is not bytes")
    let (ok, out) ← replayCall .DELEGATECALL target 0 input
    bindLocal okVar (.bool ok)
    bindLocal dataVar (.bytes out)
  | .externalCall target name value args binder perm =>
    let .address target ← eval target | throw (.error "typed call target is not an address")
    let .int value ← eval value | throw (.error "typed call value is not an integer")
    let values ← evals args
    let some input := config.externalABI.encode? name values | throw (.error "encode failed")
    let (ok, out) ← replayCall (if perm then .CALL else .STATICCALL) target value input
    if !ok then throw .reverted
    let some result := config.externalABI.decode? name out | throw .reverted
    bindLocal binder (collapseReturns result)
  | _ => throw (.error s!"unsupported audit statement: {repr stmt}")
end

def runSpec (state : State) (observed : Trace) (constructor : Bool := false) :
    Stop × Replay := Id.run do
  let mut locals : Store := ∅
  let mut body := contract.ctor.body
  let empty : Replay := {
    frame := { contract, locals }, evm := state,
    calls := observed.calls, gas := observed.gas }
  if !constructor then
    match selectorDispatchMsg contract state.executionEnv.calldata with
    | some transition =>
      match decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
          (transition.params.map Param.ty) state.executionEnv.calldata with
      | none => return (.reverted, empty)
      | some args => locals := args; body := transition.body
    | none =>
      if state.executionEnv.calldata.isEmpty then body := receiveTransition.body
      else
        locals := (∅ : Store).insert "calldata" (.bytes state.executionEnv.calldata)
        body := fallbackTransition.body
  let (result, final) := ((execBody body).run { empty with frame.locals := locals })
  return ((match result with | .ok () => .returned none | .error stop => stop), final)

def check (state : State) (constructor : Bool := false) : Except String String := do
  let observed := trace state
  if let .error .OutOfFuel := observed.result then throw "EVM test fuel exhausted"
  -- OOG is an explicit constructor of runtimeRefinementFor, not evidence of AST equivalence.
  if let .error .OutOfGass := observed.result then return "outOfGas"
  let (result, final) := runSpec state observed constructor
  if let .error message := result then throw message
  match observed.result, result with
  | .ok (.revert _ _), .reverted => pure "revert"
  | .error .StaticModeViolation, .staticViolation => pure "staticViolation"
  | .error .InvalidInstruction, .reverted => pure "invalid"
  | .ok (.success evm out), .returned values =>
    if evm.accountMap != final.evm.accountMap then throw "final account maps differ"
    if !final.calls.isEmpty then throw "unconsumed EVM calls on successful AST execution"
    let expected ← if constructor then pure safeBytecode else
      match selectorDispatchMsg contract state.executionEnv.calldata with
      | some t =>
        let vs ← match values with
          | some vs => pure vs
          | none => match t.returnType.mapM defaultAbiValue with
            | some vs => pure vs | none => throw "unsupported default return"
        match ABI.encodeReturnValues? t.returnType vs with
        | some out => pure out | none => throw "ABI return encoding failed"
      | none =>
        if state.executionEnv.calldata.isEmpty then pure ByteArray.empty else
          match values with
          | some [.bytes out] => pure out
          | _ => throw "fallback did not return raw bytes"
    if expected != out then
      throw s!"return bytes differ: EVM {Ethereum.toHex out}, AST {Ethereum.toHex expected}"
    pure "success"
  | _, _ =>
    let evm := match observed.result with
      | .error e => s!"{repr e}" | .ok (.success _ _) => "success" | .ok (.revert _ _) => "revert"
    let ast := match result with
      | .returned _ => "success" | .reverted => "revert" | .staticViolation => "staticViolation"
      | .error message => message
    throw s!"outcomes differ: EVM {evm}, AST {ast}"

end Benchmarks.Safe.Audit
