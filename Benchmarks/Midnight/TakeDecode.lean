import Benchmarks.Midnight.OfferCalldataHead

/-! External decoding for take, including all materialized input allocations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeNames : List Ident :=
  ["offer", "ratifierData", "units", "taker", "receiverIfTakerIsSeller", "takerCallback",
    "takerCallbackData"]

def takeTypes : List ABIType :=
  [Model.offerABI, .bytes, Model.u256, Model.addr, Model.addr, Model.addr, .bytes]

def takeRawArguments (offer : OfferData) (ratifierData : ByteArray) (units : UInt256)
    (taker receiver callback : AccountAddress) (data : ByteArray) : Store :=
  (((((((∅ : Store).insert "offer" offer.value).insert "ratifierData" (.bytes ratifierData)).insert
    "units" (.int units.toNat)).insert "taker" (.address taker)).insert
    "receiverIfTakerIsSeller" (.address receiver)).insert "takerCallback" (.address callback)).insert
    "takerCallbackData" (.bytes data)

def takeArguments (offer : OfferData) (ratifierData : ByteArray) (units : UInt256)
    (taker receiver callback : AccountAddress) (data : ByteArray) : Store :=
  (takeRawArguments offer ratifierData units taker receiver callback data).insert
    "offer" (Model.offerValue offer.value)

def TakeScalarsValid (bytes : ByteArray) : Prop :=
  (calldataWord bytes 100).toNat < EVM.addressModulus ∧
    (calldataWord bytes 132).toNat < EVM.addressModulus ∧
    (calldataWord bytes 164).toNat < EVM.addressModulus

instance (bytes : ByteArray) : Decidable (TakeScalarsValid bytes) := by
  unfold TakeScalarsValid
  infer_instance

def takeInputSize (offer : OfferData) (ratifierData data : ByteArray) : Nat :=
  1696 + 160 * offer.market.collaterals.length + paddedSize offer.callbackData.size +
    paddedSize ratifierData.size + paddedSize data.size

def decodeTakeRawArguments (bytes : ByteArray) : Option Store := do
  let offer ← decodeCalldataOffer bytes 4
  let ratifierData ← decodeCalldataBytes bytes 36
  if TakeScalarsValid bytes then
    let data ← decodeCalldataBytes bytes 196
    pure (takeRawArguments offer ratifierData (calldataWord bytes 68)
      (AccountAddress.ofNat (calldataWord bytes 100).toNat)
      (AccountAddress.ofNat (calldataWord bytes 132).toNat)
      (AccountAddress.ofNat (calldataWord bytes 164).toNat) data)
  else none

def decodeTakeArguments (bytes : ByteArray) : Option Store := do
  let offer ← decodeCalldataOffer bytes 4
  let ratifierData ← decodeCalldataBytes bytes 36
  if TakeScalarsValid bytes then
    let data ← decodeCalldataBytes bytes 196
    if takeInputSize offer ratifierData data < 2^64 then
      pure (takeArguments offer ratifierData (calldataWord bytes 68)
        (AccountAddress.ofNat (calldataWord bytes 100).toNat)
        (AccountAddress.ofNat (calldataWord bytes 132).toNat)
        (AccountAddress.ofNat (calldataWord bytes 164).toNat) data)
    else none
  else none

theorem takeTupleHead : abiTupleHeadSize? takeTypes = some 224 := by
  have hd : isDynamicABIType Model.offerABI = true := by decide +kernel
  simp [takeTypes, abiTupleHeadSize?, hd, Model.u256, Model.addr,
    staticABIEncodedSize?, isDynamicABIType]

theorem midnightDecodeTake_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 224 = true) :
    config.externalABI.decodeCalldata? takeNames takeTypes bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]
    rfl
  have hd : isDynamicABIType Model.offerABI = true := by decide +kernel
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, takeNames,
    show takeTypes.any isDynamicABIType = true from by simp [takeTypes, hd],
    decodeArgs?, show takeTypes.isEmpty = false from rfl, Bool.false_eq_true,
    takeTupleHead, bind, Option.bind, hcheck, if_true, ite_self]

set_option maxHeartbeats 800000 in
theorem decodeSolcTake {bytes : ByteArray}
    (h228 : 228 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 224 = false) :
    decodeCalldataWithMode Model.calldataMode takeNames takeTypes bytes =
      decodeTakeRawArguments bytes := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]
    rfl
  have hd : isDynamicABIType Model.offerABI = true := by decide +kernel
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, takeNames,
    show takeTypes.any isDynamicABIType = true from by simp [takeTypes, hd],
    decodeArgs?, show takeTypes.isEmpty = false from rfl, Bool.false_eq_true,
    takeTupleHead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false :=
    beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, takeTypes, solcDecodeFields_offer (plans := []) rfl (by omega) hsize]
  simp only [Nat.add_zero, List.tail_nil]
  rw [solcDecodeFields_bytes (cursor := 32) (by omega) hsize]
  simp only [Nat.reduceAdd]
  rw [solcDecodeFields_word Model.u256 (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_u256]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 96) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 128) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 160) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_bytes (cursor := 192) (by omega) hsize]
  simp only [Nat.reduceAdd]
  unfold decodeTakeRawArguments
  cases decodeCalldataOffer bytes 4 with
  | none => rfl
  | some offer =>
    cases decodeCalldataBytes bytes 36 with
    | none => rfl
    | some ratifierData =>
      generalize hb : decodeCalldataBytes bytes 196 = decoded
      unfold TakeScalarsValid
      by_cases ht : (calldataWord bytes 100).toNat < EVM.addressModulus <;>
        by_cases hr : (calldataWord bytes 132).toNat < EVM.addressModulus <;>
        by_cases hc : (calldataWord bytes 164).toNat < EVM.addressModulus <;>
        simp only [ht, hr, hc, and_self, false_and, and_false, if_true, if_false,
          bind, Option.bind, decodeFields?, decodeCalldata.insertValues]
      cases decoded <;> rfl

theorem takeArguments_inputSizes (offer : OfferData) (ratifierData : ByteArray) (units : UInt256)
    (taker receiver callback : AccountAddress) (data : ByteArray) :
    Model.inputSizesFit (takeRawArguments offer ratifierData units taker receiver callback data) =
      decide (takeInputSize offer ratifierData data < 2^64) := by
  simp [Model.inputSizesFit, takeRawArguments, OfferData.value, Model.collateralCount?,
    MarketData.value, takeInputSize, Std.HashMap.getElem_insert]
  split <;> simp_all [takeInputSize, Nat.not_lt]

set_option maxHeartbeats 800000 in
theorem midnightDecodeTake {bytes : ByteArray}
    (h228 : 228 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 224 = false) :
    config.externalABI.decodeCalldata? takeNames takeTypes bytes = decodeTakeArguments bytes := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcTake h228 hsize hselector hcheck]
  unfold decodeTakeRawArguments decodeTakeArguments
  cases decodeCalldataOffer bytes 4 with
  | none => rfl
  | some offer =>
    cases decodeCalldataBytes bytes 36 with
    | none => rfl
    | some ratifierData =>
      generalize hb : decodeCalldataBytes bytes 196 = decoded
      by_cases hv : TakeScalarsValid bytes
      · simp only [hv, if_true, bind, Option.bind]
        cases decoded with
        | none => rfl
        | some data =>
          let args := takeRawArguments offer ratifierData (calldataWord bytes 68)
            (AccountAddress.ofNat (calldataWord bytes 100).toNat)
            (AccountAddress.ofNat (calldataWord bytes 132).toNat)
            (AccountAddress.ofNat (calldataWord bytes 164).toNat) data
          have hmarket : args["market"]? = none := by simp [args, takeRawArguments]
          have hoffer : args["offer"]? = some offer.value := by
            simp [args, takeRawArguments, Std.HashMap.getElem_insert]
          simp only [bind, Option.bind]
          rw [takeArguments_inputSizes, hmarket, hoffer]
          by_cases hfit : takeInputSize offer ratifierData data < 2^64
          · simp only [hfit, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
            rfl
          · simp only [hfit, decide_false, Bool.not_false, if_true, if_false]
      · simp only [hv, if_false, bind, Option.bind]

end Benchmarks.Midnight
