import Benchmarks.Midnight.MarketEntryDecode

/-! The external ABI for a market and an account. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def marketUserArguments (market : MarketData) (user : AccountAddress) : Store :=
  (((∅ : Store).insert "market" market.value).insert "user" (.address user)).insert
    "market" (Model.marketValue market.value)

theorem midnightDecodeMarketUser_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 64 = true) :
    config.externalABI.decodeCalldata? ["market", "user"]
      [Model.marketABI, Model.addr] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.addr] = some 64 := by
    simp [abiTupleHeadSize?, hd, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, hd, Bool.true_or, decodeArgs?, List.isEmpty_cons, Bool.false_eq_true,
    hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcMarketUser {bytes : ByteArray}
    (h68 : 68 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 64 = false) :
    decodeCalldataWithMode Model.calldataMode ["market", "user"]
      [Model.marketABI, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 36).toNat < EVM.addressModulus then
          pure (((∅ : Store).insert "market" market.value).insert "user"
            (.address (AccountAddress.ofNat (calldataWord bytes 36).toNat)))
        else none) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.addr] = some 64 := by
    simp [abiTupleHeadSize?, hd, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, List.any_cons, List.any_nil, hd, Bool.true_or,
    decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, hhead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false := by
    exact beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, solcDecodeFields_market (plans := []) rfl (by omega) hsize]
  simp only [Nat.add_zero, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 32) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 36).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, decodeFields?, decodeCalldata.insertValues]
      rfl
    · simp only [hu, if_false, bind, Option.bind]

theorem midnightDecodeMarketUser {bytes : ByteArray}
    (h68 : 68 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 64 = false) :
    config.externalABI.decodeCalldata? ["market", "user"]
      [Model.marketABI, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 36).toNat < EVM.addressModulus ∧
            1120 + 160 * market.collaterals.length < 2^64 then
          pure (marketUserArguments market
            (AccountAddress.ofNat (calldataWord bytes 36).toNat))
        else none) := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMarketUser h68 hsize hselector hcheck]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 36).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, true_and]
      by_cases hf : 1120 + 160 * market.collaterals.length < 2^64 <;>
        simp only [Nat.reducePow] at hf <;>
        simp [Model.inputSizesFit, Model.collateralCount?, MarketData.value,
          marketUserArguments, Std.HashMap.getElem_insert, hf]
    · simp only [hu, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
