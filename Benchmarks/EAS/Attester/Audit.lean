import Benchmarks.EAS.Attester.Bytecode

/-!
# Executable Attester audit

These differential checks execute the real bytecode with `Ethereum.EVM.Ξ` and evaluate the
canonical surface AST using Solm's expression, assignment, ABI, and external-call operations.
The small fuelled statement runner covers exactly the statements used by this benchmark;
unsupported statements and exhausted test fuel are errors, never successful tests.
This is regression evidence, not a proof of the refinement theorems.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.EAS.Attester.Audit

set_option maxRecDepth 100000

def word (n : Nat) : ByteArray := UInt256.toByteArray (.ofNat n)
def bytes32Value (n : Nat) : Value := .fixedBytes bytes32Width (word n).toList

structure Request where
  target : AccountAddress
  value : Int
  calldata : ByteArray
  deriving BEq

structure Cursor where
  frame : Frame
  evm : State
  calls : List Request := []

/-- A fixed witness for the existential call gas/substate in `callViaEVM`.
    The test callees do not inspect gas or access warmth. -/
def runCall (evm : State) (target : AccountAddress) (value : Int) (payload : ByteArray)
    (perm : Bool) : Bool × State × ByteArray :=
  let valueWord := EVM.wordOfInt value
  if valueWord ≤ (evm.accountMap.get? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
      evm.executionEnv.depth ≠ 1024 then
    let (accounts, _, substate, ok, out) := Θ evm.accountMap evm.σ₀ evm.substate
      evm.executionEnv.codeOwner evm.executionEnv.sender target
      (Ethereum.toExecute evm.accountMap target) (.ofNat 1000000)
      (.ofNat evm.executionEnv.gasPrice) valueWord valueWord payload
      (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
      evm.executionEnv.blocks (perm && evm.executionEnv.perm)
    (ok, { evm with accountMap := accounts, substate := substate }, out)
  else (false, evm, .empty)

def runBody : Nat → Cursor → List Stmt → EvalResult (Cursor × Option (List Value))
  | 0, _, _ => .error .typeError
  | _ + 1, c, [] => .ok (c, none)
  | fuel + 1, c, stmt :: rest => do
    let eval := evalExpr? config c.frame c.evm
    match stmt with
    | .letDecl name _ expr =>
      let v ← eval expr
      runBody fuel { c with frame.locals := c.frame.locals.insert name v } rest
    | .assign origin ref expr =>
      let v ← eval expr
      let (frame, evm) ← assignStorageRef? config c.frame c.evm origin ref v
      runBody fuel { c with frame := frame, evm := evm } rest
    | .setImmutable name expr =>
      let v ← eval expr
      let ty ← EvalResult.ofOption .typeError (immutableType? contract name)
      if elemValueFits ty v then
        runBody fuel { c with frame.immutables := c.frame.immutables.insert name v } rest
      else .error .typeError
    | .require expr =>
      match ← eval expr with
      | .bool true => runBody fuel c rest
      | .bool false => .revert
      | _ => .error .typeError
    | .for init cond post body =>
      runBody fuel c (init ++ [.while cond (body ++ post)] ++ rest)
    | .while cond body =>
      match ← eval cond with
      | .bool false => runBody fuel c rest
      | .bool true => runBody fuel c (body ++ [stmt] ++ rest)
      | _ => .error .typeError
    | .return exprs =>
      let values ← evalExprs? config c.frame c.evm exprs
      pure (c, some values)
    | .externalCall receiver name eth args retVar perm =>
      let .address target ← eval receiver | .error .typeError
      let .int value ← eval eth | .error .typeError
      let values ← evalExprs? config c.frame c.evm args
      let payload ← EvalResult.ofOption .typeError (config.externalABI.encode? name values)
      let (ok, evm, out) := runCall c.evm target value payload perm
      if !ok then .revert else
        match config.externalABI.decode? name out with
        | none => .revert
        | some values =>
          runBody fuel
            { c with evm := evm
                     frame.locals := c.frame.locals.insert retVar (collapseReturns values)
                     calls := c.calls ++ [⟨target, value, payload⟩] } rest
    | .lowLevelCall receiver eth data okVar dataVar perm =>
      let .address target ← eval receiver | .error .typeError
      let .int value ← eval eth | .error .typeError
      let .bytes payload ← eval data | .error .typeError
      let (ok, evm, out) := runCall c.evm target value payload perm
      runBody fuel
        { c with evm := evm
                 frame.locals := (c.frame.locals.insert okVar (.bool ok)).insert dataVar (.bytes out)
                 calls := c.calls ++ [⟨target, value, payload⟩] } rest
    | _ => .error .typeError

/-- Capture the outer CALL immediately before it executes. -/
def beforeCall : Nat → Array UInt256 → State → Option State
  | 0, _, _ => none
  | fuel + 1, jumps, s =>
    if (decode s.executionEnv.code s.machineState.pc).map Prod.fst == some .CALL then some s
    else match Xstep jumps s with
      | .ok (next, none) => beforeCall fuel jumps next
      | _ => none

def beforePC (pc : Nat) : Nat → Array UInt256 → State → Option State
  | 0, _, _ => none
  | fuel + 1, jumps, s =>
    if s.machineState.pc.toNat == pc then some s
    else match Xstep jumps s with
      | .ok (next, none) => beforePC pc fuel jumps next
      | _ => none

def requestAtCall (s : State) : Request :=
  let stack := s.machineState.stack
  let start := (stack.getD 3 ⟨0⟩).toNat
  let len := (stack.getD 4 ⟨0⟩).toNat
  ⟨.ofUInt256 (stack.getD 1 ⟨0⟩), Int.ofNat (stack.getD 2 ⟨0⟩).toNat,
    s.machineState.memory.readWithPadding start len⟩

def push2 (n : Nat) : ByteArray := ⟨#[0x61, UInt8.ofNat (n / 256), UInt8.ofNat n]⟩

/-- Return or revert with exact raw bytes, optionally modifying slot zero first. -/
def callee (out : ByteArray) (reverts := false) (writes := false) : ByteArray :=
  let prelude : ByteArray := if writes then ⟨#[0x60, 1, 0x60, 0, 0x55]⟩ else .empty
  prelude ++ push2 out.size ++ push2 (prelude.size + 15) ++ ⟨#[0x60, 0, 0x39]⟩ ++
    push2 out.size ++ ⟨#[0x60, 0, if reverts then 0xfd else 0xf3]⟩ ++ out

def runtimeState (data calleeCode : ByteArray) (value := 0) (perm := true)
    (depth := 0) (target := 0x200) : State :=
  let code := Immutables.deployedRuntime attesterBytecode
    ((∅ : Store).insert "_eas" (.address (.ofNat target)))
  let accounts : AccountMap := (∅ : AccountMap)
    |>.insert (.ofNat 0x100) { (default : Account) with code := code }
    |>.insert (.ofNat target) { (default : Account) with code := calleeCode }
  { (default : State) with
      accountMap := accounts
      σ₀ := accounts
      executionEnv :=
        { (default : ExecutionEnv) with
            code := code
            calldata := data
            codeOwner := .ofNat 0x100
            source := .ofNat 0x300
            sender := .ofNat 0x300
            weiValue := .ofNat value
            depth := ⟨depth % 1025, Nat.mod_lt _ (by decide)⟩
            perm := perm }
      machineState.gasAvailable := .ofUInt256 (.ofNat 5000000) }

def check (name : String) (data calleeCode : ByteArray) (value := 0) (perm := true)
    (depth := 0) (target := 0x200) : IO Unit := do
  let s := runtimeState data calleeCode value perm depth target
  let source := do
    let t ← EvalResult.ofOption .typeError (selectorDispatchMsg contract data)
    match decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes data with
    | none => .revert
    | some locals =>
      let (c, returned) ← runBody 10000
        { frame := ⟨contract, locals,
            (∅ : Store).insert "_eas" (.address (.ofNat target))⟩, evm := s } t.body
      let out ← EvalResult.ofOption .typeError
        (ABI.encodeReturnValues? t.returnType (returned.getD []))
      pure (c, out)
  let result := Ξ s.accountMap s.σ₀ (.ofNat 5000000) s.substate s.executionEnv
  match source, result with
  | .ok (c, expected), .ok (.success (accounts, _, _) out) =>
    unless expected == out do throw (IO.userError s!"{name}: return bytes differ")
    unless c.evm.accountMap == accounts do throw (IO.userError s!"{name}: account maps differ")
    match c.calls, beforeCall 100000 (D_J s.executionEnv.code 0) s with
    | [request], some atCall =>
      unless request == requestAtCall atCall do
        throw (IO.userError s!"{name}: outbound call differs")
    | [], none => pure ()
    | _, _ => throw (IO.userError s!"{name}: call count differs")
  | .revert, .ok (.revert _ _) => pure ()
  | .error _, .ok (.revert _ _) =>
    if (selectorDispatchMsg contract data).isSome then
      throw (IO.userError s!"{name}: source runner error")
  | _, _ => throw (IO.userError s!"{name}: source and EVM outcomes differ")

def arguments (index : Nat) (values : List Value) : ByteArray :=
  let t := contract.transitions[index]!
  (ABI.encodeCallWithSelector? ((KEC (transitionSigStr t).toUTF8).extract 0 4)
    (transitionSignature t).paramTypes values).get!

def batch (index : Nat) (counts : List Nat) : ByteArray :=
  arguments index
    [.array (counts.map fun n ↦ bytes32Value (n + 0x123)),
     .array (counts.map fun n ↦ .array ((List.range n).map fun i ↦
       if index == 1 then .int (Int.ofNat (i + 42)) else bytes32Value (i + 42)))]

def checkMemoryFormula : IO Unit := do
  for counts in [[1], [2], [1, 1], [2, 3], [1, 4, 2]] do
    let s := runtimeState (batch 1 counts) (callee (word 32 ++ word 0))
    let some atCall := beforeCall 100000 (D_J s.executionEnv.code 0) s
      | throw (IO.userError "multiAttest: no call")
    let fp := (atCall.machineState.lookupMemory ⟨64⟩).toNat
    let expected := 160 + 192 * counts.length + 480 * counts.sum
    unless fp == expected do
      throw (IO.userError s!"allocation formula: {counts}, observed {fp}, expected {expected}")

/-- Exercise the real return allocator at the 64-bit boundary without allocating enormous
    memory: stop just before the accepted allocator writes the array. -/
def checkAllocationGuard : IO Unit := do
  let .require guard := multiAttestTransition.body.reverse[1]!
    | throw (IO.userError "missing allocation guard")
  for q in [0, 1, 2] do
    let s := runtimeState (batch 1 [1])
      (callee (word 32 ++ word q ++ ⟨Array.replicate (32 * q) 0⟩))
    let jumps := D_J s.executionEnv.code 0
    let some decoder := beforePC 3631 100000 jumps s
      | throw (IO.userError "return decoder was not reached")
    for rawSize in [0, 1, 31, 32, 33, 64, 95, 96] do
      let rounded := 32 * ((rawSize + 31) / 32)
      for base in [160, 2^64 - rounded - 32*(q+1) - 1,
          2^64 - rounded - 32*(q+1), 2^64 - 1, 2^64] do
        let probe := { decoder with
          machineState := decoder.machineState.writeWord ⟨64⟩ (.ofNat (base + rounded)) }
        let accepted := (beforePC 3706 200 jumps probe).isSome
        let locals : Store := (∅ : Store)
          |>.insert "allocationEnd" (.int (Int.ofNat base))
          |>.insert "rawReturn" (.bytes ⟨Array.replicate rawSize 0⟩)
          |>.insert "uids" (.array (List.replicate q (bytes32Value 0)))
        match evalExpr? config ⟨contract, locals, ∅⟩ s guard with
        | .ok (.bool allowed) =>
          unless allowed == accepted do throw (IO.userError "allocation guard mismatch")
        | _ => throw (IO.userError "allocation guard expression failed")

def checkConstructor (target value : Nat) : IO Unit := do
  let args := [Value.address (.ofNat target)]
  let code := (config.selfDeployment attesterCreationBytecode args).get!
  let base := runtimeState .empty .empty
  let s := { base with executionEnv :=
    { base.executionEnv with code := code, calldata := .empty, weiValue := .ofNat value } }
  let locals := (bindParams? (constructorDecl.params.map Param.toFunctionParam) args).get!
  let source := runBody 100 ⟨⟨contract, locals, initialImmutables contract⟩, s, []⟩
    constructorDecl.body
  let actual := Ξ s.accountMap s.σ₀ (.ofNat 5000000) s.substate s.executionEnv
  match source, actual with
  | .revert, .ok (.revert _ _) => pure ()
  | .ok (c, none), .ok (.success (accounts, _, _) out) =>
    unless out == Immutables.deployedRuntime attesterBytecode c.frame.immutables &&
        accounts == c.evm.accountMap do
      throw (IO.userError "constructor runtime/immutables/account mismatch")
  | _, _ => throw (IO.userError "constructor outcomes differ")

def replaceWord (data : ByteArray) (offset value : Nat) : ByteArray :=
  data.extract 0 offset ++ word value ++ data.extract (offset + 32) data.size

def checkMalformedConstructor : IO Unit := do
  for tail in [.empty, (word 0x200).extract 1 32, word (2^160)] do
    let s := runtimeState .empty .empty
    let env := { s.executionEnv with code := attesterCreationBytecode ++ tail }
    match Ξ s.accountMap s.σ₀ (.ofNat 5000000) s.substate env with
    | .ok (.revert _ _) => pure ()
    | _ => throw (IO.userError "malformed constructor arguments did not revert")

def run : IO Unit := do
  checkMemoryFormula
  checkAllocationGuard
  for target in [0, 1, 0x200, 2^160 - 1] do
    for value in [0, 1] do checkConstructor target value
  checkMalformedConstructor
  for counts in [[1], [2], [1, 1], [2, 3], [1, 4, 2], [], [0], [1, 0]] do
    check s!"multiAttest {counts}" (batch 1 counts)
      (callee (word 32 ++ word 2 ++ word 0xabc ++ word 0xdef))
    check s!"multiRevoke {counts}" (batch 2 counts) (callee .empty)
  check "attest" (arguments 0 [bytes32Value 1, .int 42]) (callee (word 0xabc))
  check "revoke" (arguments 3 [bytes32Value 1, bytes32Value 2]) (callee .empty)
  let canonical := [arguments 0 [bytes32Value 1, .int (2^256 - 1)], batch 1 [1],
    batch 2 [1], arguments 3 [bytes32Value 1, bytes32Value 2]]
  let returns := [word 0xabc, word 32 ++ word 1 ++ word 0xabc, .empty, .empty]
  for (data, out) in canonical.zip returns do
    -- Every strict prefix includes short selector, truncated head, and truncated tail cases.
    for len in List.range data.size do
      check s!"truncated calldata {len}" (data.extract 0 len) (callee out)
    check "trailing calldata" (data ++ ⟨#[0xff, 0x77, 0x55]⟩) (callee out)
    check "nonpayable" data (callee out) 1
    check "static pure callee" data (callee out) 0 false
    check "state-changing callee" data (callee out false true)
    check "callee writes in static mode" data (callee out false true) 0 false
    check "callee rollback" data (callee out true true)
    check "depth exhausted" data (callee out) 0 true 1024
    check "empty-code address" data .empty
    check "identity precompile" data .empty 0 true 0 4
    for returnBytes in [.empty, ⟨#[1]⟩, (word 0).extract 1 32, word 0,
        word 32, word 32 ++ word 0, word 32 ++ word 1,
        word 32 ++ word 1 ++ word 0xabc,
        word 64 ++ word 0xff ++ word 1 ++ word 0xabc,
        word 33 ++ ⟨#[0xff]⟩ ++ word 1 ++ word 0xabc,
        word 32 ++ word (2^64), word (2^64) ++ word 0,
        word 32 ++ word 1 ++ word 0xabc ++ ⟨#[0xff]⟩] do
      check "raw return decoding" data (callee returnBytes)
    for size in [0, 1, 31, 32] do
      check "callee revert payload" data (callee ⟨Array.replicate size 0xff⟩ true)
  for index in [1, 2] do
    let data := batch index [1]
    let out := if index == 1 then word 32 ++ word 0 else .empty
    let sel := data.extract 0 4
    -- Accepted noncanonical calldata: inner tail aliases the schemas array using ADD wrap.
    let wrapped := sel ++ word 64 ++ word 128 ++ word 1 ++ word 0x123 ++
      word 1 ++ word (2^256 - 96)
    check "wrapped nested offset" wrapped (callee out)
    for offset in [4, 36, 68, 100, 132, 164, 196, 228] do
      for value in [0, 1, 31, 32, 33, 64, 96, 128, 256, 2^64 - 1, 2^64,
          2^255 - 1, 2^255, 2^256 - 1, 2^256 - 96] do
        check s!"mutated calldata {index}/{offset}/{value}"
          (replaceWord data offset value) (callee out)
    -- Positive, negative, unaligned, overlapping, and out-of-bounds nested offsets.
    for delta in List.range 280 do
      check s!"nested offset {delta}" (replaceWord data 164 delta) (callee out)
      check s!"negative nested offset {delta}"
        (replaceWord data 164 (2^256 - delta)) (callee out)
  -- Confirm CALLER/ORIGIN/ADDRESS/CALLVALUE propagation through the call bridge.
  for opcode in [0x33, 0x32, 0x30, 0x34] do
    check "callee environment" canonical[0]!
      ⟨#[UInt8.ofNat opcode, 0x60, 0, 0x52, 0x60, 32, 0x60, 0, 0xf3]⟩
  IO.println "Attester differential audit passed"

#eval run

end Benchmarks.EAS.Attester.Audit
