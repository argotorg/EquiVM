import Solm.Interp

/-!
# EVM traces and the replay oracle

The differential tests run the real bytecode with evmlean and the specification with
`Solm.Interp`.  The relation's call rules quantify the call gas and the input substate
existentially; the EVM run fixes them.  `runTrace` executes the bytecode step by step (exactly
the loop of `Ethereum.EVM.X`) and records every call boundary (`CALL`, `CALLCODE`,
`DELEGATECALL`, `STATICCALL`, `CREATE`, `CREATE2`) and every `GAS` result.  `replayOracle` then
answers the interpreter's call requests from those records: it checks that the specification
issues the same call (kind, target, value, calldata) and hands back the EVM's own result for it,
which is by construction a `Θ`/`Lambda` result for the gas and substate the EVM used.
-/

namespace Solm.DiffTest

open Ethereum Ethereum.EVM Solm.Interp

/-- The EVM state just before and just after a call-family instruction. -/
structure CallBoundary where
  opcode : Operation
  before : EVM.State
  after : EVM.State

/-- The result of running the bytecode, with the raw final state kept for diagnostics. -/
structure Trace where
  result : Except ExecutionException (ExecutionResult EVM.State)
  boundaries : List CallBoundary := []
  gasWords : List UInt256 := []
  steps : Nat := 0

def isCallOpcode : Operation → Bool
  | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL | .CREATE | .CREATE2 => true
  | _ => false

/-- Execute `initial` to completion (the loop of `X`, with its depth bookkeeping), recording
    call boundaries and `GAS` results.  `fuel` bounds the number of steps; `Ξ` uses `g + 1`. -/
def runTrace (initial : EVM.State) (fuel : Nat) : Trace := Id.run do
  let jumps := D_J initial.executionEnv.code 0
  let mut state := initial
  let mut boundaries : Array CallBoundary := #[]
  let mut gasWords : Array UInt256 := #[]
  let mut steps := 0
  for _ in [:fuel] do
    steps := steps + 1
    let opcode := (decode state.executionEnv.code state.machineState.pc).map Prod.fst |>.getD .STOP
    match Xstep jumps state with
    | .error e =>
        return { result := .error e, boundaries := boundaries.toList, gasWords := gasWords.toList, steps }
    | .ok (next, halt) =>
        let next := { next with executionEnv.depth := state.executionEnv.depth }
        if opcode == .GAS then
          gasWords := gasWords.push (next.machineState.stack.getD 0 ⟨0⟩)
        if isCallOpcode opcode then
          boundaries := boundaries.push { opcode, before := state, after := next }
        match halt with
        | some (.success, out) =>
            return { result := .ok (.success next out), boundaries := boundaries.toList,
                     gasWords := gasWords.toList, steps }
        | some (.revert, out) =>
            return { result := .ok (.revert next.machineState.gasAvailable.toUInt256 out),
                     boundaries := boundaries.toList, gasWords := gasWords.toList, steps }
        | none => state := next
  return { result := .error .OutOfFuel, boundaries := boundaries.toList, gasWords := gasWords.toList, steps }

/-- The `Ξ`-shaped result of a trace. -/
def Trace.xiResult (t : Trace) :
    Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate)) :=
  match t.result with
  | .error e => .error e
  | .ok (.success s o) => .ok (.success (s.accountMap, s.machineState.gasAvailable.toUInt256, s.substate) o)
  | .ok (.revert g o) => .ok (.revert g o)

/-! ## The replay oracle -/

/-- Cursor into the recorded boundaries, plus the mismatches found while replaying. -/
structure Replay where
  boundaries : List CallBoundary
  gasWords : List UInt256
  mismatches : List String := []

def Replay.ofTrace (t : Trace) : Replay := { boundaries := t.boundaries, gasWords := t.gasWords }

def word (n : Nat) : UInt256 := .ofNat n

def addressOfWord (w : UInt256) : EVM.Address := AccountAddress.ofUInt256 w

/-- The arguments of the recorded call-family instruction, read off its stack and memory. -/
structure BoundaryArgs where
  kind : Option CallKind     -- `none` for CREATE/CREATE2
  target : EVM.Address
  value : Nat
  input : ByteArray
  salt : Option ByteArray

def boundaryArgs (b : CallBoundary) : BoundaryArgs :=
  let st := b.before.machineState.stack
  let mem := b.before.machineState.memory
  let slice (off len : UInt256) := mem.readWithPadding off.toNat len.toNat
  match b.opcode with
  | .CALL | .CALLCODE =>
      { kind := some .call, target := addressOfWord (st.getD 1 ⟨0⟩), value := (st.getD 2 ⟨0⟩).toNat,
        input := slice (st.getD 3 ⟨0⟩) (st.getD 4 ⟨0⟩), salt := none }
  | .STATICCALL =>
      { kind := some .staticcall, target := addressOfWord (st.getD 1 ⟨0⟩), value := 0,
        input := slice (st.getD 2 ⟨0⟩) (st.getD 3 ⟨0⟩), salt := none }
  | .DELEGATECALL =>
      { kind := some .delegatecall, target := addressOfWord (st.getD 1 ⟨0⟩), value := 0,
        input := slice (st.getD 2 ⟨0⟩) (st.getD 3 ⟨0⟩), salt := none }
  | .CREATE2 =>
      { kind := none, target := EVM.address 0, value := (st.getD 0 ⟨0⟩).toNat,
        input := slice (st.getD 1 ⟨0⟩) (st.getD 2 ⟨0⟩), salt := some (st.getD 3 ⟨0⟩).toByteArray }
  | _ =>  -- CREATE
      { kind := none, target := EVM.address 0, value := (st.getD 0 ⟨0⟩).toNat,
        input := slice (st.getD 1 ⟨0⟩) (st.getD 2 ⟨0⟩), salt := none }

def describeRequest (req : CallRequest) : String :=
  s!"{repr req.kind} to {req.target.val} value {req.value} calldata {Ethereum.toHex req.calldata}"

/-- Check a replayed call request against the recorded boundary. -/
def matchCall (b : CallBoundary) (req : CallRequest) : Except String Unit := do
  let args := boundaryArgs b
  let kindOk := args.kind == some req.kind
  if !kindOk then
    throw s!"call kind differs: spec {repr req.kind}, EVM {repr b.opcode} at pc {b.before.machineState.pc.toNat}"
  if args.target != req.target then
    throw s!"call target differs: spec {req.target.val}, EVM {args.target.val}"
  if req.kind == .call && Int.ofNat args.value != req.value then
    throw s!"call value differs: spec {req.value}, EVM {args.value}"
  if args.input != req.calldata then
    throw s!"call data differs: spec {Ethereum.toHex req.calldata}, EVM {Ethereum.toHex args.input}"

/-- The oracle that replays the EVM's own call results.  Request mismatches are errors (the
    interpreter gets stuck and reports them); a guard-rejected call still consumes its boundary. -/
def replayOracle : Oracle Replay where
  call := fun ω req evm => do
    match ω.boundaries with
    | [] => throw s!"spec makes a call the EVM did not: {describeRequest req}"
    | b :: rest =>
        matchCall b req
        if evm.accountMap != b.before.accountMap then
          throw s!"account map at the call differs from the EVM's (pc {b.before.machineState.pc.toNat})"
        let success := b.after.machineState.stack.getD 0 ⟨0⟩ != ⟨0⟩
        pure (⟨success, b.after.accountMap, b.after.substate, b.after.machineState.returnData⟩,
          { ω with boundaries := rest })
  callNotMade := fun ω req =>
    match ω.boundaries with
    | [] => { ω with mismatches := ω.mismatches ++ [s!"spec rejects a call the EVM never reached: {describeRequest req}"] }
    | b :: rest =>
        let note :=
          if b.after.machineState.stack.getD 0 ⟨0⟩ != ⟨0⟩ then
            [s!"spec rejected a call (balance/depth) that succeeded in the EVM at pc {b.before.machineState.pc.toNat}"]
          else []
        { ω with boundaries := rest, mismatches := ω.mismatches ++ note }
  create := fun ω req evm => do
    match ω.boundaries with
    | [] => throw "spec creates a contract where the EVM made no CREATE"
    | b :: rest =>
        let args := boundaryArgs b
        if args.kind.isSome then throw s!"spec creates a contract; the EVM made a {repr b.opcode}"
        if Int.ofNat args.value != req.value then throw s!"creation value differs: spec {req.value}, EVM {args.value}"
        if args.input != req.initCode then throw "creation code differs"
        if args.salt != req.salt then throw "creation salt differs"
        if evm.accountMap != b.before.accountMap then throw "account map at the creation differs from the EVM's"
        let addrWord := b.after.machineState.stack.getD 0 ⟨0⟩
        pure (⟨addressOfWord addrWord, b.after.accountMap, b.after.substate, addrWord != ⟨0⟩⟩,
          { ω with boundaries := rest })
  createNotMade := fun ω _ =>
    match ω.boundaries with
    | [] => { ω with mismatches := ω.mismatches ++ ["spec rejects a creation the EVM never reached"] }
    | _ :: rest => { ω with boundaries := rest }
  gasLeft := fun ω evm =>
    match ω.gasWords with
    | w :: rest => (w, { ω with gasWords := rest })
    | [] => (evm.machineState.gasAvailable.toUInt256,
             { ω with mismatches := ω.mismatches ++ ["spec reads gasleft() where the EVM executed no GAS"] })

end Solm.DiffTest
