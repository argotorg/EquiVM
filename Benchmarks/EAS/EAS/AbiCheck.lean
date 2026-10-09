import Benchmarks.EAS.EAS.DiffTarget

/-!
Reproduce the calldata-tail mismatch found during the EAS audit.

`lake env lean --run Benchmarks/EAS/EAS/AbiCheck.lean` checks the pinned EAS
runtime against Solm, including the formerly disagreeing backward tuple tail.
Every case must agree; there is no expected-failure exception to refinement.

With `--probes DIR`, check the compiler probes produced by `abi_offset_probe.py`
instead. They distinguish direct calldata access from materialization in memory.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

private def calldataWords (signature : String) (words : List Nat) : ByteArray :=
  words.foldl (fun acc n => acc ++ wordBytes n)
    ((Ethereum.KEC signature.toUTF8).extract 0 4)

private def checkEAS : IO UInt32 := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let sig := "multiRevoke((bytes32,(bytes32,uint256)[])[])"
  let mut failed := false
  for (name, words, succeeds) in [
      ("canonical empty request", [32, 1, 32, 0, 64, 0], true),
      ("forward offset with gap", [32, 1, 64, 0, 0, 64, 0], true),
      ("tail aliases schema word", [32, 1, 32, 0, 0], true),
      ("backward tuple tail (-32)", [32, 1, 64, 0, 0, 2 ^ 256 - 32], true),
      ("negative absolute tail then memory copy", [32, 1, 64, 0, 0, 2 ^ 256 - 256], false),
      ("tail beyond calldata", [32, 1, 64, 0, 0, 256], false),
      ("oversized top-level offset", [2 ^ 256 - 32, 1, 64, 0, 0, 0], false)] do
    let calldata := calldataWords sig words
    let result := runCase t
      { label := name, σ := t.world,
        I := t.env t.runtime (EVM.address 0x6004) 0 calldata true 1000 16756728 }
    IO.println s!"EAS {name}: {result.verdict.describe}"
    let expectedEVM := match result.evmResult with
      | .ok (.success _ out) => succeeds && out.isEmpty
      | .ok (.revert _ _) => !succeeds
      | _ => false
    unless expectedEVM do
      IO.eprintln s!"unexpected EVM outcome: {describeEvm result.evmResult}"
      failed := true
    unless result.verdict.isAgree do failed := true
  return if failed then 1 else 0

private def checkProbes (dir : System.FilePath) : IO UInt32 := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let mut count := 0
  for version in ["0.8.18-ir", "0.8.18-legacy", "0.8.32-ir", "0.8.32-legacy"] do
    let runtime ← IO.FS.readBinFile (dir / s!"{version}.bin")
    for name in ["direct", "copied", "memoryArg"] do
      for (label, words) in [
          ("canonical", [32, 1, 32, 0, 64, 0]),
          ("backward", [32, 1, 64, 0, 0, 2 ^ 256 - 32]),
          ("negative absolute tail", [32, 1, 64, 0, 0, 2 ^ 256 - 256]),
          ("out of bounds", [32, 1, 64, 0, 0, 256])] do
        let calldata := calldataWords s!"{name}((bytes32,uint256[])[])" words
        let world := t.world runtime
        let I := t.env runtime (EVM.address 0x6004) 0 calldata true 1000 16756728
        let trace := runTrace (initialState world world (.ofNat t.gas) default I) (t.gas + 1)
        let succeeds := label == "canonical" || (name == "direct" && label != "out of bounds")
        let expected := match trace.result with
          | .ok (.success _ out) => succeeds && out == wordBytes 0
          | .ok (.revert _ _) => !succeeds
          | _ => false
        IO.println s!"{version} {name} {label}: {describeEvm trace.xiResult}"
        unless expected do
          IO.eprintln "unexpected compiler-probe result"
          return (1 : UInt32)
        let plan : ABI.CalldataPlan := match name with
          | "direct" => { materialize := [] }
          | "copied" => { materialize := [[.element]] }
          | _ => {}
        let selector := (ABI.bytesToWord (calldata.toList.take 4)).toNat
        let mode : ABI.DecodeMode := .solc08Calldata [(selector, [plan])]
        let ty : ABI.ABIType := .dynamicArray (.tuple [
          .elem (.bytes ⟨31, by decide⟩), .dynamicArray (.elem (.int (.uint ⟨256, by decide⟩)))])
        let decoded := ABI.decodeCalldata ["r"] [ty] calldata mode
        unless decoded.isSome == succeeds do
          IO.eprintln "decoder acceptance differs from compiler execution"
          return (1 : UInt32)
        if let some store := decoded then
          let expectedValue : Value := .array [.tuple [
            .fixedBytes ⟨31, by decide⟩ (wordBytes 0).toList, .array []]]
          unless store.get? "r" == some expectedValue do
            IO.eprintln "decoder produced the wrong value"
            return (1 : UInt32)
        count := count + 1
  IO.println s!"ABI compiler probes: {count}/{count} EVM/decoder agreements"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => checkEAS
  | ["--probes", dir] => checkProbes dir
  | _ =>
    IO.eprintln "usage: AbiCheck.lean [--probes DIR]"
    return 2
