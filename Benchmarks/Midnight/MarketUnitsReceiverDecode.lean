import Benchmarks.Midnight.MarketEntryDecode

/-! Decoding the market, units, owner, and receiver of a withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def marketUnitsReceiverArguments (market : MarketData) (units : UInt256)
    (user receiver : AccountAddress) : Store :=
  (((((∅ : Store).insert "market" market.value).insert "units" (.int units.toNat)).insert
    "onBehalf" (.address user)).insert "receiver" (.address receiver)).insert
      "market" (Model.marketValue market.value)

theorem midnightDecodeMarketUnitsReceiver_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 128 = true) :
    config.externalABI.decodeCalldata? ["market", "units", "onBehalf", "receiver"]
      [Model.marketABI, Model.u256, Model.addr, Model.addr] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.u256, Model.addr, Model.addr] = some 128 := by
    simp [abiTupleHeadSize?, hd, Model.u256, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, hd, Bool.true_or, decodeArgs?, List.isEmpty_cons, Bool.false_eq_true,
    hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcMarketUnitsReceiver {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    decodeCalldataWithMode Model.calldataMode ["market", "units", "onBehalf", "receiver"]
      [Model.marketABI, Model.u256, Model.addr, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 68).toNat < EVM.addressModulus ∧
            (calldataWord bytes 100).toNat < EVM.addressModulus then
          pure (((((∅ : Store).insert "market" market.value).insert "units"
            (.int (calldataWord bytes 36).toNat)).insert "onBehalf"
              (.address (AccountAddress.ofNat (calldataWord bytes 68).toNat))).insert "receiver"
              (.address (AccountAddress.ofNat (calldataWord bytes 100).toNat)))
        else none) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.u256, Model.addr, Model.addr] = some 128 := by
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
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 96) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 68).toNat < EVM.addressModulus
    · by_cases hr : (calldataWord bytes 100).toNat < EVM.addressModulus
      · simp only [hu, hr, and_self, if_true, bind, Option.bind, decodeFields?,
          decodeCalldata.insertValues]
        rfl
      · simp only [hu, hr, true_and, if_false, if_true, bind, Option.bind]
    · simp only [hu, false_and, if_false, bind, Option.bind]

set_option maxHeartbeats 500000 in
theorem midnightDecodeMarketUnitsReceiver
    {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    config.externalABI.decodeCalldata? ["market", "units", "onBehalf", "receiver"]
      [Model.marketABI, Model.u256, Model.addr, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 68).toNat < EVM.addressModulus ∧
            (calldataWord bytes 100).toNat < EVM.addressModulus ∧
            1120 + 160 * market.collaterals.length < 2^64 then
          pure (marketUnitsReceiverArguments market (calldataWord bytes 36)
            (AccountAddress.ofNat (calldataWord bytes 68).toNat)
            (AccountAddress.ofNat (calldataWord bytes 100).toNat))
        else none) := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMarketUnitsReceiver h132 hsize hselector hcheck]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    let decodedArgs : Store := ((((∅ : Store).insert "market" market.value).insert "units"
      (.int (calldataWord bytes 36).toNat)).insert "onBehalf" (.address (AccountAddress.ofNat (calldataWord bytes 68).toNat))).insert "receiver"
      (.address (AccountAddress.ofNat (calldataWord bytes 100).toNat))
    have hmarket : decodedArgs["market"]? = some market.value := by simp [decodedArgs, Std.HashMap.getElem_insert]
    have hoffer : decodedArgs["offer"]? = none := by simp [decodedArgs]
    have hnewOffer : (decodedArgs.insert "market" (Model.marketValue market.value))["offer"]? = none := by
      simp only [Std.HashMap.getElem?_insert, show ("market" == "offer") = false from rfl,
        Bool.false_eq_true, if_false, hoffer]
    have hfit : Model.inputSizesFit decodedArgs = decide (1120 + 160 * market.collaterals.length < 2^64) := by
      simp only [Model.inputSizesFit, hmarket, hoffer, Model.collateralCount?, MarketData.value,
        List.length_map]
      split <;> simp_all
    by_cases hu : (calldataWord bytes 68).toNat < EVM.addressModulus
    · by_cases hr : (calldataWord bytes 100).toNat < EVM.addressModulus
      · simp only [hu, hr, and_self, if_true, bind, Option.bind, true_and]
        rw [hfit, hmarket, hnewOffer]
        by_cases hcap : 1120 + 160 * market.collaterals.length < 2^64
        · simp only [hcap, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
          rfl
        · simp only [hcap, decide_false, Bool.not_false, if_true, if_false]
      · simp only [hu, hr, false_and, true_and, if_false, bind, Option.bind]
    · simp only [hu, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
