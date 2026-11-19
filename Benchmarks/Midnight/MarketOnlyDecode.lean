import Benchmarks.Midnight.MarketEntryDecode

/-! The external ABI for a single Market argument. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def marketOnlyArguments (m : MarketData) : Store :=
  ((∅ : Store).insert "market" m.value).insert "market" (Model.marketValue m.value)

theorem midnightDecodeMarketOnly_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 32 = true) :
    config.externalABI.decodeCalldata? ["market"] [Model.marketABI] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI] = some 32 := by
    simp [abiTupleHeadSize?, hd]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, hd, Bool.true_or, decodeArgs?, List.isEmpty_cons, Bool.false_eq_true,
    hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcMarketOnly {bytes : ByteArray}
    (h36 : 36 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 32 = false) :
    decodeCalldataWithMode Model.calldataMode ["market"] [Model.marketABI] bytes = (do
      let market ← decodeCalldataMarket bytes 4
      pure ((∅ : Store).insert "market" market.value)) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI] = some 32 := by
    simp [abiTupleHeadSize?, hd]
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, List.any_cons, List.any_nil, hd, Bool.true_or,
    decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, hhead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false :=
    beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, solcDecodeFields_market (plans := []) rfl (by omega) hsize]
  simp only [Nat.add_zero, List.tail_nil, decodeFields?, bind, Option.bind]
  cases hm : decodeCalldataMarket bytes 4 <;> rfl

theorem midnightDecodeMarketOnly {bytes : ByteArray}
    (h36 : 36 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 32 = false) :
    config.externalABI.decodeCalldata? ["market"] [Model.marketABI] bytes = (do
      let market ← decodeCalldataMarket bytes 4
      if 1120 + 160 * market.collaterals.length < 2^64 then
        pure (marketOnlyArguments market)
      else none) := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMarketOnly h36 hsize hselector hcheck]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    simp only [bind, Option.bind]
    by_cases hf : 1120 + 160 * market.collaterals.length < 2^64 <;>
      simp only [Nat.reducePow] at hf <;>
      simp [Model.inputSizesFit, Model.collateralCount?, MarketData.value,
        marketOnlyArguments, hf]

end Benchmarks.Midnight
