import Benchmarks.EAS.EAS.DiffTarget

/-!
Successful ECDSA delegation, nonce consumption, and the post-verification copy guard.
Run with the EVM interpreter's coincurve/pycryptodome/typing-extensions available
and working directory `.lake/packages/evmlean`; see HANDOFF.md.
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


private def signer : Nat := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

private def signature (payload : ByteArray) : IO Value := do
  let domain := wordBytes 0x1b86e1aefca1c2cc067f67f9d06e2f79c85094c488f7c6b8d7bc828a69952348
  let digest := Ethereum.KEC (⟨#[0x19, 0x01]⟩ ++ domain ++ Ethereum.KEC payload)
  let python := "from coincurve import PrivateKey; import sys; print(PrivateKey(bytes.fromhex('00'*31+'01')).sign_recoverable(bytes.fromhex(sys.argv[1]), hasher=None).hex())"
  let out ← IO.Process.output { cmd := "python3", args := #["-c", python, Ethereum.toHex digest] }
  unless out.exitCode == 0 do throw (IO.userError out.stderr)
  let .ok sig := ByteArray.ofBlob out.stdout.trimAscii.toString
    | throw (IO.userError "invalid signature hex")
  unless sig.size == 65 do throw (IO.userError "wrong signature size")
  return .tuple [.int (sig[64]!.toNat + 27),
    .fixedBytes ⟨31, by decide⟩ (sig.extract 0 32).toList,
    .fixedBytes ⟨31, by decide⟩ (sig.extract 32 64).toList]

private def data (payload : Nat) : Value :=
  .tuple [.address (EVM.address 0x6004), .int 0, .bool true, bytes32 0,
    .bytes (wordBytes payload), .int 1]

private def attestSignature (payload nonce : Nat) : IO Value :=
  signature (wordBytes 0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61 ++
    wordBytes 1 ++ wordBytes 0x6004 ++ wordBytes 0 ++ wordBytes 1 ++ wordBytes 0 ++
    Ethereum.KEC (wordBytes payload) ++ wordBytes nonce)

private def revokeSignature (uid : ByteArray) (nonce : Nat) : IO Value :=
  signature (wordBytes 0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650 ++
    wordBytes 1 ++ uid ++ wordBytes nonce)

private def encodeCall (name : String) (args : List Value) : IO ByteArray := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let some transition := t.contract.transitions.find? (·.name == name)
    | throw (IO.userError "missing transition")
  let selector := (Ethereum.KEC (transitionSigStr transition).toUTF8).extract 0 4
  let some input := ABI.encodeCallWithSelector? selector (transition.params.map Param.ty) args
    | throw (IO.userError "encoding failed")
  return input

private def checkRejected (accounts : AccountMap) (input : ByteArray) (calls : Nat) : IO Unit := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let env := t.env t.runtime (EVM.address 0x6004) 0 input true 1000 16756728
  let gas := UInt256.ofNat t.gas
  let trace := runTrace (initialState accounts accounts gas default env) (t.gas + 1)
  let (spec, replay) := solmExecRun t.fuel replayOracle (Replay.ofTrace trace) t.config t.contract
    t.immutables accounts accounts gas default env
  let verdict := compareRuntime trace.xiResult spec
  unless verdict.isAgree && !verdict.isSuccess && replay.boundaries.isEmpty &&
      replay.mismatches.isEmpty && trace.boundaries.length == calls do
    throw (IO.userError s!"delegation rejection: {verdict.describe}, calls {trace.boundaries.length}, pending {replay.boundaries.length}")
  IO.println s!"delegation rejection after {calls} recovery call(s): agrees"

private def wordAt (input : ByteArray) (offset : Nat) : Nat :=
  (ABI.bytesToWord (input.extract offset (offset + 32)).toList).toNat

def main : IO UInt32 := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let attester : Value := .address (EVM.address signer)
  let sig ← attestSignature 101 0
  let single := [.tuple [bytes32 1, data 101, sig, attester]]
  let (accounts, uid) ← check t.world "attestByDelegation" single 3
  -- A repeated signature uses the old nonce and must fail after recovery.
  checkRejected accounts (← encodeCall "attestByDelegation" single) 1
  let sig ← revokeSignature uid 1
  let uidValue : Value := .fixedBytes ⟨31, by decide⟩ uid.toList
  let (accounts, _) ← check accounts "revokeByDelegation"
    [.tuple [bytes32 1, .tuple [uidValue, .int 1], sig, attester]] 3
  let sig2 ← attestSignature 102 2
  let sig3 ← attestSignature 103 3
  let sig4 ← attestSignature 104 4
  let (accounts, output) ← check accounts "multiAttestByDelegation" [.array [
    .tuple [bytes32 1, .array [data 102, data 103], .array [sig2, sig3], attester],
    .tuple [bytes32 1, .array [data 104], .array [sig4], attester]]] 5
  let some (.array uids) := ABI.decodeReturnValueWithMode? .modern
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) output
    | throw (IO.userError "UID decoding failed")
  let mut signatures : List Value := []
  for (uid, nonce) in uids.zip [5, 6, 7] do
    let .fixedBytes _ bytes := uid | throw (IO.userError "bad UID")
    signatures := signatures ++ [← revokeSignature ⟨bytes.toArray⟩ nonce]
  let (accounts, _) ← check accounts "multiRevokeByDelegation" [.array [
    .tuple [bytes32 1, .array (uids.map fun uid => .tuple [uid, .int 1]),
      .array signatures, attester]]] 5
  let (_, output) ← check accounts "getNonce" [attester]
  unless output == wordBytes 8 do throw (IO.userError "wrong final nonce")
  let sig ← attestSignature 105 8
  let canonical ← encodeCall "multiAttestByDelegation" [.array [
    .tuple [bytes32 1, .array [data 105], .array [sig], attester]]]
  let row := 68 + wordAt canonical 68
  let oldHeads := row + wordAt canonical (row + 32) + 32
  let datum := oldHeads + wordAt canonical oldHeads
  let newHeads := canonical.size + 32
  let backward := replaceWord canonical (row + 32) (canonical.size - row) ++
    wordBytes 1 ++ wordBytes (2^256 + datum - newHeads)
  -- Direct calldata verification accepts the backward reference. The subsequent
  -- memory copy has a uint64 offset cap and must revert only after recovery.
  checkRejected accounts backward 1
  return 0
