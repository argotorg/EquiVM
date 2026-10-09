import Benchmarks.EAS.EAS.DiffTarget

/-!
Compare the EAS-local allocation counter with the actual EVM free-memory word,
including repeated UID hashing, storage copies, resolver returns, and refunds.
-/
open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

private def bytes32 (n : Nat) : Value :=
  .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

private def check (accounts : AccountMap) (name : String) (args : List Value)
    (value : Nat := 0) (t : Target := Benchmarks.EAS.EAS.fixtureTarget) : IO (AccountMap × ByteArray) := do
  let some transition := t.contract.transitions.find? (·.name == name)
    | throw (IO.userError s!"missing {name}")
  let selector := (Ethereum.KEC (transitionSigStr transition).toUTF8).extract 0 4
  let some input := ABI.encodeCallWithSelector? selector (transition.params.map Param.ty) args
    | throw (IO.userError "encoding failed")
  let caller := EVM.address 0x6004
  let accounts := transferValue accounts caller t.selfAddress value
  let env := t.env t.runtime caller value input true 1000 16756728
  let gas : UInt256 := .ofNat t.gas
  let trace := runTrace (initialState accounts accounts gas default env) (t.gas + 1)
  let (spec, replay) := solmExecRun t.fuel replayOracle (Replay.ofTrace trace) t.config t.contract
    t.immutables accounts accounts gas default env
  let verdict := compareRuntime trace.xiResult spec
  unless verdict.isSuccess && replay.mismatches.isEmpty && replay.boundaries.isEmpty do
    throw (IO.userError s!"{name}: {verdict.describe}; {replay.mismatches}")
  let .ok (.success state output) := trace.result
    | throw (IO.userError s!"{name}: EVM failed")
  let .ran (.result (.returned frame _ _)) _ := spec
    | throw (IO.userError s!"{name}: spec failed")
  let actual := (ABI.bytesToWord (state.machineState.memory.readWithPadding 64 32).toList).toNat
  let some (.int expected) := frame.locals.get? "$EAS.freeMemory"
    | throw (IO.userError s!"{name}: allocation counter missing")
  unless expected == Int.ofNat actual do
    throw (IO.userError s!"{name}: EVM free pointer {actual}, spec {expected}")
  IO.println s!"{name}: free pointer {actual} agrees"
  return (state.accountMap, output)

private def allocatorBoundaries : IO Unit := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let some fn := t.contract.functions.find? (·.name == "_allocate")
    | throw (IO.userError "missing allocator")
  let code := t.runtime ++ ⟨#[0x5b, 0x00]⟩
  let env := t.env code (EVM.address 0x6004) 0 .empty true
  let initial := initialState t.world t.world (.ofNat t.gas) default env
  for (heap, size) in ([(224, 0), (224, 1), (224, 32), (224, 33),
      (2^64-64, 32), (2^64-64, 33), (2^64-32, 0), (2^64-32, 1),
      (224, 2^256-32), (224, 2^256-31), (224, 2^256-1)] : List (Nat × Nat)) do
    -- Enter the pinned allocator block with its Yul calling convention.
    let evm := { initial with machineState := { initial.machineState with
      pc := .ofNat 4883, stack := [heap, size, t.runtime.size].map UInt256.ofNat } }
    let trace := runTrace evm 100
    let locals : Store := (∅ : Store) |>.insert "size" (.int size)
      |>.insert "$EAS.freeMemory" (.int heap)
    let (spec, _) := execFuncBody 100 replayOracle (Replay.ofTrace trace) t.config
      { contract := t.contract, locals := locals, immutables := t.immutables } initial fn.body
    match trace.result, spec with
    | .ok (.success state _), .result (.returned frame _ _) =>
      let actual := (ABI.bytesToWord (state.machineState.memory.readWithPadding 64 32).toList).toNat
      unless frame.locals.get? "$EAS.freeMemory" == some (.int actual) do
        throw (IO.userError s!"allocator boundary mismatch: {heap}, {size}")
    | .ok (.revert _ _), .result .reverted => pure ()
    | _, _ => throw (IO.userError s!"allocator outcomes differ at {heap}, {size}: {spec.describe}")
  IO.println "allocator: 11 uint64/uint256 boundary cases agree with runtime PCs 4883–4947"

def main : IO UInt32 := do
  allocatorBoundaries
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let mut accounts := t.world
  for name in ["VERSION", "getDomainSeparator", "getSchemaRegistry", "getAttestTypeHash", "getRevokeTypeHash"] do
    let (_, _) ← check accounts name []
  let (_, _) ← check accounts "getAttestation" [bytes32 0]
  let altered := t.immutables.insert "_CACHED_CHAIN_ID" (.int 2)
  let alteredTarget := { t with immutables := altered, runtime := t.codeOf altered }
  let (_, _) ← check alteredTarget.world "getDomainSeparator" [] 0 alteredTarget
  for length in [0, 1, 31, 32, 33, 96] do
    for schema in ([0, 1] : List Nat) do
      let data : Value := .tuple [.address (EVM.address 0x6004), .int 0, .bool true,
        bytes32 0, .bytes ⟨Array.replicate length 7⟩, .int (Int.ofNat schema)]
      let args := [.tuple [bytes32 schema, data]]
      let (next, _) ← check accounts "attest" args 3
      accounts := next
      -- Same timestamp and request: this call must hash again with an incremented bump.
      let (next, uid) ← check accounts "attest" args 3
      accounts := next
      let uid : Value := .fixedBytes ⟨31, by decide⟩ uid.toList
      let (_, _) ← check accounts "getAttestation" [uid]
      let (next, _) ← check accounts "revoke" [.tuple [bytes32 schema, .tuple [uid, .int (Int.ofNat schema)]]] 3
      accounts := next
  let data : Value := .tuple [.address (EVM.address 0x6004), .int 0, .bool true,
    bytes32 0, .bytes (wordBytes 55), .int 1]
  let (next, output) ← check accounts "multiAttest"
    [.array [.tuple [bytes32 1, .array [data, data]], .tuple [bytes32 1, .array [data]]]] 5
  accounts := next
  let some (.array uids) := ABI.decodeReturnValueWithMode? .modern
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) output
    | throw (IO.userError "UID decoding failed")
  let (next, _) ← check accounts "multiRevoke"
    [.array [.tuple [bytes32 1, .array (uids.map fun uid => .tuple [uid, .int 1])]]] 5
  accounts := next
  for name in ["multiAttest", "multiAttestByDelegation", "multiRevoke", "multiRevokeByDelegation",
      "multiTimestamp", "multiRevokeOffchain"] do
    let (_, _) ← check accounts name [.array []]
  -- Both schema-string decoding and nonempty refund returndata advance the pointer.
  let registry := EVM.address 0xa7b39296258348c78294f95b872b282326a97bdf
  let result := wordBytes 32 ++ wordBytes 1 ++ wordBytes 0x6002 ++ wordBytes 1 ++
    wordBytes 128 ++ wordBytes 3 ++ ⟨#[97,98,99]⟩ ++ ⟨Array.replicate 29 0⟩
  accounts := accounts.insert registry { (accounts.get? registry).getD default with code := callee result }
  let caller := EVM.address 0x6004
  accounts := accounts.insert caller { (accounts.get? caller).getD default with code := callee (wordBytes 1) }
  let (_, _) ← check accounts "attest" [.tuple [bytes32 1, data]] 3
  return 0
