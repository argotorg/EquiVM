import Benchmarks.Midnight.MarketEntryDecode
import Benchmarks.Midnight.CalldataDynamicValues
import Benchmarks.Midnight.BoolDecode

/-! External decoding for liquidation's market, scalar arguments, and callback data. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateNames : List Ident :=
  ["market", "collateralIndex", "seizedAssets", "repaidUnits", "borrower", "postMaturityMode",
    "receiver", "callback", "data"]

def liquidateTypes : List ABIType :=
  [Model.marketABI, Model.u256, Model.u256, Model.u256, Model.addr, .elem .bool,
    Model.addr, Model.addr, .bytes]

def liquidateRawArguments (market : MarketData) (index seized repaid : UInt256)
    (borrower : AccountAddress) (mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Store :=
  (((((((((∅ : Store).insert "market" market.value).insert "collateralIndex" (.int index.toNat)).insert
    "seizedAssets" (.int seized.toNat)).insert "repaidUnits" (.int repaid.toNat)).insert
    "borrower" (.address borrower)).insert "postMaturityMode" (wordToElem .bool mode)).insert
    "receiver" (.address receiver)).insert "callback" (.address callback)).insert "data" (.bytes data)

def liquidateArguments (market : MarketData) (index seized repaid : UInt256)
    (borrower : AccountAddress) (mode : UInt256) (receiver callback : AccountAddress)
    (data : ByteArray) : Store :=
  (liquidateRawArguments market index seized repaid borrower mode receiver callback data).insert
    "market" (Model.marketValue market.value)

def LiquidateScalarsValid (bytes : ByteArray) : Prop :=
  (calldataWord bytes 132).toNat < EVM.addressModulus ∧
    (calldataWord bytes 164 = ⟨0⟩ ∨ calldataWord bytes 164 = ⟨1⟩) ∧
    (calldataWord bytes 196).toNat < EVM.addressModulus ∧
    (calldataWord bytes 228).toNat < EVM.addressModulus

instance (bytes : ByteArray) : Decidable (LiquidateScalarsValid bytes) := by
  unfold LiquidateScalarsValid
  infer_instance

def decodeLiquidateArguments (bytes : ByteArray) : Option Store := do
  let market ← decodeCalldataMarket bytes 4
  if LiquidateScalarsValid bytes ∧ 1120 + 160 * market.collaterals.length < 2^64 then
    let data ← decodeCalldataBytes bytes 260
    some (liquidateArguments market (calldataWord bytes 36) (calldataWord bytes 68)
      (calldataWord bytes 100) (AccountAddress.ofNat (calldataWord bytes 132).toNat)
      (calldataWord bytes 164) (AccountAddress.ofNat (calldataWord bytes 196).toNat)
      (AccountAddress.ofNat (calldataWord bytes 228).toNat) data)
  else none

theorem liquidateTupleHead : abiTupleHeadSize? liquidateTypes = some 288 := by
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  simp [liquidateTypes, abiTupleHeadSize?, hd, Model.u256, Model.addr,
    staticABIEncodedSize?, isDynamicABIType]

theorem midnightDecodeLiquidate_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 288 = true) :
    config.externalABI.decodeCalldata? liquidateNames liquidateTypes bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, liquidateNames,
    show liquidateTypes.any isDynamicABIType = true from by simp [liquidateTypes, hd],
    decodeArgs?, show liquidateTypes.isEmpty = false from rfl, Bool.false_eq_true,
    liquidateTupleHead, bind, Option.bind, hcheck, if_true, ite_self]

set_option maxHeartbeats 800000 in
theorem decodeSolcLiquidate {bytes : ByteArray}
    (h292 : 292 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 288 = false) :
    decodeCalldataWithMode Model.calldataMode liquidateNames liquidateTypes bytes = (do
      let market ← decodeCalldataMarket bytes 4
      if LiquidateScalarsValid bytes then
        let data ← decodeCalldataBytes bytes 260
        some (liquidateRawArguments market (calldataWord bytes 36) (calldataWord bytes 68)
          (calldataWord bytes 100) (AccountAddress.ofNat (calldataWord bytes 132).toNat)
          (calldataWord bytes 164) (AccountAddress.ofNat (calldataWord bytes 196).toNat)
          (AccountAddress.ofNat (calldataWord bytes 228).toNat) data)
      else none) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  conv_lhs =>
    simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
      if_false, Model.calldataMode, liquidateNames,
      show liquidateTypes.any isDynamicABIType = true from by simp [liquidateTypes, hd],
      decodeArgs?, show liquidateTypes.isEmpty = false from rfl, Bool.false_eq_true,
      liquidateTupleHead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false :=
    beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, liquidateTypes, solcDecodeFields_market (plans := []) rfl (by omega) hsize]
  simp only [Nat.add_zero, List.tail_nil]
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 32) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 96) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 128) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word (.elem .bool) (base := 4) (cursor := 160) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_bool]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 192) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 224) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_bytes (cursor := 256) (by omega) hsize]
  simp only [Nat.reduceAdd]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    generalize hb : decodeCalldataBytes bytes 260 = decoded
    unfold LiquidateScalarsValid
    by_cases hu : (calldataWord bytes 132).toNat < EVM.addressModulus <;>
      by_cases hb : calldataWord bytes 164 = ⟨0⟩ ∨ calldataWord bytes 164 = ⟨1⟩ <;>
      by_cases hr : (calldataWord bytes 196).toNat < EVM.addressModulus <;>
      by_cases hc : (calldataWord bytes 228).toNat < EVM.addressModulus <;>
      simp only [hu, hb, hr, hc, and_self, true_and, false_and, and_false, if_true, if_false,
        bind, Option.bind, decodeFields?, decodeCalldata.insertValues]
    cases decoded <;> rfl

set_option maxHeartbeats 800000 in
theorem midnightDecodeLiquidate {bytes : ByteArray}
    (h292 : 292 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 288 = false) :
    config.externalABI.decodeCalldata? liquidateNames liquidateTypes bytes =
      decodeLiquidateArguments bytes := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcLiquidate h292 hsize hselector hcheck]
  unfold decodeLiquidateArguments
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    generalize hb : decodeCalldataBytes bytes 260 = decoded
    by_cases hv : LiquidateScalarsValid bytes
    · simp only [hv, true_and, if_true, bind, Option.bind]
      cases decoded with
      | none => simp only [bind, Option.bind, ite_self]
      | some data =>
        let args := liquidateRawArguments market (calldataWord bytes 36) (calldataWord bytes 68)
          (calldataWord bytes 100) (AccountAddress.ofNat (calldataWord bytes 132).toNat)
          (calldataWord bytes 164) (AccountAddress.ofNat (calldataWord bytes 196).toNat)
          (AccountAddress.ofNat (calldataWord bytes 228).toNat) data
        have hmarket : args["market"]? = some market.value := by
          simp [args, liquidateRawArguments, Std.HashMap.getElem_insert]
        have hoffer : args["offer"]? = none := by simp [args, liquidateRawArguments]
        have hnew : (args.insert "market" (Model.marketValue market.value))["offer"]? = none := by
          simp only [Std.HashMap.getElem?_insert, show ("market" == "offer") = false from rfl,
            Bool.false_eq_true, if_false, hoffer]
        have hfit : Model.inputSizesFit args =
            decide (1120 + 160 * market.collaterals.length < 2^64) := by
          simp only [Model.inputSizesFit, hmarket, hoffer, Model.collateralCount?, MarketData.value,
            List.length_map]
          split <;> simp_all
        simp only [bind, Option.bind]
        rw [hfit, hmarket, hnew]
        by_cases hcap : 1120 + 160 * market.collaterals.length < 2^64
        · simp only [hcap, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
          rfl
        · simp only [hcap, decide_false, Bool.not_false, if_true, if_false]
    · simp only [hv, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
