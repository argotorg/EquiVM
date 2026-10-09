import Benchmarks.EAS.EAS.DiffTarget

/-!
Regression for the synthetic dynamic-bytes state that exposed SOL-2025-1.
Solidity 0.8.32 attempts the required clear and exhausts the finite gas budget;
0.8.18 incorrectly skipped it and returned successfully. Do not execute Solm's
astronomically large clear loop: EVM out-of-gas is unconstrained by refinement.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

def main : IO UInt32 := do
  let t := Benchmarks.EAS.EAS.fixtureTarget
  let some transition := t.contract.transitions.find? (·.name == "attest")
    | IO.eprintln "missing attest"; return 1
  let fixed (n : Nat) : Value := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList
  let args := [Value.tuple [fixed 0, .tuple [.address (EVM.address 0x6004), .int 0,
    .bool true, fixed 0, .bytes (wordBytes 20), .int 0]]]
  let selector := (Ethereum.KEC (transitionSigStr transition).toUTF8).extract 0 4
  let some calldata := ABI.encodeCallWithSelector? selector (transition.params.map Param.ty) args
    | IO.eprintln "encoding failed"; return 1
  let I := t.env t.runtime (EVM.address 0x6004) 0 calldata true 1000 16756728
  let state := initialState t.world t.world (.ofNat t.gas) default I
  let header : UInt256 := .ofNat 0xe1dd08ae1d49638eeebb9516e97ee6462554046cf5bb65ab4d47fa4880d6d241
  let sentinel : UInt256 := .ofNat 0xfc31f757e98c880f46418b05b4aab95bb2927be9207cc32019e95fdc499767a1
  let oldHeader : UInt256 := .ofNat (2 ^ 256 - 1)
  let .ok oldLength := solidityDecodeBytesLengthHeader oldHeader
    | IO.eprintln "old header did not decode"; return 1
  let oldWords := solidityBytesDataWordCount oldLength
  let dataBase := solidityBytesDataSlot header 0
  let endSlot := dataBase + UInt256.ofNat oldWords
  unless oldWords == 2 ^ 250 && solidityBytesDataSlot header 1 == sentinel &&
      endSlot.toNat < sentinel.toNat do
    IO.eprintln "clear bounds did not wrap"; return 1
  let state := EVM.storageStore state t.selfAddress header oldHeader
  let state := EVM.storageStore state t.selfAddress sentinel (.ofNat 42)
  let trace := runTrace state (t.gas + 1)
  match trace.result with
  | .error .OutOfGass =>
    IO.println "Solidity 0.8.32 storage-wrap regression: EVM runs out of gas instead of skipping the clear"
    return 0
  | _ =>
    IO.eprintln "Expected out of gas while clearing the synthetic enormous bytes value"
    return 1
