import Benchmarks.Midnight.MarketEntryDecode

/-! Decoding the market, collateral index, amount, and beneficiary of a collateral supply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def marketIndexAmountArguments (market : MarketData) (index amount : UInt256) (user : AccountAddress) : Store :=
  (((((∅ : Store).insert "market" market.value).insert "collateralIndex" (.int index.toNat)).insert
    "assets" (.int amount.toNat)).insert "onBehalf" (.address user)).insert "market" (Model.marketValue market.value)

theorem midnightDecodeMarketIndexAmount_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 128 = true) :
    config.externalABI.decodeCalldata? ["market", "collateralIndex", "assets", "onBehalf"]
      [Model.marketABI, Model.u256, Model.u256, Model.addr] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.u256, Model.u256, Model.addr] = some 128 := by
    simp [abiTupleHeadSize?, hd, Model.u256, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, hd, Bool.true_or, decodeArgs?, List.isEmpty_cons, Bool.false_eq_true,
    hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcMarketIndexAmount {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    decodeCalldataWithMode Model.calldataMode ["market", "collateralIndex", "assets", "onBehalf"]
      [Model.marketABI, Model.u256, Model.u256, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 100).toNat < EVM.addressModulus then
          pure (((((∅ : Store).insert "market" market.value).insert "collateralIndex"
            (.int (calldataWord bytes 36).toNat)).insert "assets"
              (.int (calldataWord bytes 68).toNat)).insert "onBehalf"
              (.address (AccountAddress.ofNat (calldataWord bytes 100).toNat)))
        else none) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.u256, Model.u256, Model.addr] = some 128 := by
    simp [abiTupleHeadSize?, hd, Model.u256, Model.addr, staticABIEncodedSize?, isDynamicABIType]
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
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 32) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 96) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 100).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, decodeFields?, decodeCalldata.insertValues]
      rfl
    · simp only [hu, if_false, bind, Option.bind]

set_option maxHeartbeats 500000 in
theorem midnightDecodeMarketIndexAmount
    {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    config.externalABI.decodeCalldata? ["market", "collateralIndex", "assets", "onBehalf"]
      [Model.marketABI, Model.u256, Model.u256, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 100).toNat < EVM.addressModulus ∧
            1120 + 160 * market.collaterals.length < 2^64 then
          pure (marketIndexAmountArguments market (calldataWord bytes 36) (calldataWord bytes 68)
            (AccountAddress.ofNat (calldataWord bytes 100).toNat))
        else none) := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMarketIndexAmount h132 hsize hselector hcheck]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 100).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, true_and]
      by_cases hf : 1120 + 160 * market.collaterals.length < 2^64 <;>
        simp only [Nat.reducePow] at hf <;>
        simp only [Model.inputSizesFit, Std.HashMap.getElem?_insert,
          show ("onBehalf" == "market") = false from rfl,
          show ("assets" == "market") = false from rfl,
          show ("collateralIndex" == "market") = false from rfl,
          show ("onBehalf" == "offer") = false from rfl,
          show ("assets" == "offer") = false from rfl,
          show ("collateralIndex" == "offer") = false from rfl,
          show ("market" == "offer") = false from rfl,
          beq_self_eq_true, Bool.false_eq_true, if_false, if_true,
          Std.HashMap.getElem?_empty, Model.collateralCount?, MarketData.value,
          List.length_map, bind, pure, hf, decide_true, decide_false,
          marketIndexAmountArguments, Nat.reducePow, Bool.not_false, Bool.not_true,
          Id.run, Bool.true_eq_false]
    · simp only [hu, false_and, if_false, bind, Option.bind]


end Benchmarks.Midnight
