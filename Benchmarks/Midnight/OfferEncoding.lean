import Benchmarks.Midnight.OfferEncoder
import Benchmarks.Midnight.FlashLoanCallbackABI
import Reasoning.ABIViews

/-! The canonical ABI byte sequence of an offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the ABI encoding of an already canonical boolean word.
theorem encodeBoolWord (word : UInt256) (hc : word = ⟨0⟩ ∨ word = ⟨1⟩) :
    encodeABIValue? (.elem .bool) (wordToElem .bool word) = some (EVM.Word.toBytesBE word) := by
  rcases hc with h | h
  · rw [h, wordToElemBool]
    exact encodeABIValue_bool false
  · rw [h, wordToElemBool]
    exact encodeABIValue_bool true

def offerEncodedBytes (offer : OfferData) : ByteArray :=
  wordArrayBytes (offer.words (UInt256.ofNat 480) (UInt256.ofNat (offerCallbackOffset offer))) ++
    wordArrayBytes (offer.market.words (UInt256.ofNat 256) ++
      UInt256.ofNat offer.market.collaterals.length ::
        offer.market.collaterals.flatMap CollateralData.words) ++
    (UInt256.ofNat offer.callbackData.size).toByteArray ++ offer.callbackData ++
    ByteArray.zeroes (paddedSize offer.callbackData.size - offer.callbackData.size)

theorem offerEncodedBytes_size (offer : OfferData) :
    (offerEncodedBytes offer).size = offerEncodedSize offer := by
  have hlo := nat_le_paddedSize offer.callbackData.size
  have hw (marketPtr callbackPtr : UInt256) : (offer.words marketPtr callbackPtr).length = 15 := rfl
  simp only [offerEncodedBytes, ByteArray.size_append, wordArrayBytes_size, toByteArray_size,
    ByteArray_zeroes_size, List.length_append, List.length_cons, collateralWords_length,
    hw,
    show (offer.market.words (UInt256.ofNat 256)).length = 8 from rfl,
    offerEncodedSize, offerCallbackOffset]
  omega

set_option maxHeartbeats 800000 in
theorem OfferData.encodeValue (offer : OfferData) (hc : OfferCanonical offer) :
    encodeABIValue? Model.offerABI offer.value = some (offerEncodedBytes offer).toList := by
  have hmarket := offer.market.encodeValue
  have hbuy := encodeBoolWord offer.buy hc.buy
  have hmaker := encodeABIValue_accountAddress offer.maker
  have hstart := encodeABIValue_uint256 offer.start
  have hexpiry := encodeABIValue_uint256 offer.expiry
  have htick := encodeABIValue_uint256 offer.tick
  have hgroup := encodeABIValue_bytes32_word offer.group
  have hcallback := encodeABIValue_accountAddress offer.callback
  have hbytes : encodeABIValue? .bytes (.bytes offer.callbackData) =
      some (natBytes offer.callbackData.size ++ padRightToWord offer.callbackData.toList) := by
    simp only [encodeABIValue?]
  have hreceiver := encodeABIValue_accountAddress offer.receiverIfMakerIsSeller
  have hratifier := encodeABIValue_accountAddress offer.ratifier
  have hreduce := encodeBoolWord offer.reduceOnly hc.reduceOnly
  have hunits := encodeUIntWord ⟨128, by decide⟩ offer.maxUnits hc.maxUnits
  have hassets := encodeUIntWord ⟨128, by decide⟩ offer.maxAssets hc.maxAssets
  have hcap := encodeABIValue_uint256 offer.continuousFeeCap
  simp only [Int.ofNat_eq_natCast] at hstart hexpiry htick hunits hassets hcap
  change encodeABIValue? Model.addr (.address offer.maker) = _ at hmaker
  change encodeABIValue? Model.u256 (.int offer.start.toNat) = _ at hstart
  change encodeABIValue? Model.u256 (.int offer.expiry.toNat) = _ at hexpiry
  change encodeABIValue? Model.u256 (.int offer.tick.toNat) = _ at htick
  change encodeABIValue? Model.addr (.address offer.callback) = _ at hcallback
  change encodeABIValue? Model.addr (.address offer.receiverIfMakerIsSeller) = _ at hreceiver
  change encodeABIValue? Model.addr (.address offer.ratifier) = _ at hratifier
  change encodeABIValue? Model.u128 (.int offer.maxUnits.toNat) = _ at hunits
  change encodeABIValue? Model.u128 (.int offer.maxAssets.toNat) = _ at hassets
  change encodeABIValue? Model.u256 (.int offer.continuousFeeCap.toNat) = _ at hcap
  change encodeABIValue? Model.b32 (wordBytes32Value offer.group) = _ at hgroup
  rw [Model.offerABI, OfferData.value, encodeABIValue?, encodeABIValues?]
  have hhead : abiTupleHeadSize?
      [Model.marketABI, .elem .bool, Model.addr, Model.u256, Model.u256, Model.u256,
        Model.b32, Model.addr, .bytes, Model.addr, Model.addr, .elem .bool,
        Model.u128, Model.u128, Model.u256] = some 480 := by
    simp only [abiTupleHeadSize?, Model.u256, Model.u128, Model.addr, Model.b32,
      show isDynamicABIType Model.marketABI = true from rfl, isDynamicABIType,
      staticABIEncodedSize?, Bool.false_eq_true, if_true, if_false, bind, Option.bind]
  rw [hhead]
  dsimp only [bind, Option.bind]
  rw [encodeABIValuesFrom?, hmarket]
  simp only [bind, Option.bind, show isDynamicABIType (Model.marketABI) = true from rfl,
    if_true]
  rw [encodeABIValuesFrom?, hbuy]
  simp only [bind, Option.bind, show isDynamicABIType (.elem .bool) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hmaker]
  simp only [bind, Option.bind, show isDynamicABIType (Model.addr) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hstart]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u256) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hexpiry]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u256) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, htick]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u256) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hgroup]
  simp only [bind, Option.bind, show isDynamicABIType (Model.b32) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hcallback]
  simp only [bind, Option.bind, show isDynamicABIType (Model.addr) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hbytes]
  simp only [bind, Option.bind, show isDynamicABIType (.bytes) = true from rfl,
    if_true]
  rw [encodeABIValuesFrom?, hreceiver]
  simp only [bind, Option.bind, show isDynamicABIType (Model.addr) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hratifier]
  simp only [bind, Option.bind, show isDynamicABIType (Model.addr) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hreduce]
  simp only [bind, Option.bind, show isDynamicABIType (.elem .bool) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hunits]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u128) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hassets]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u128) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?, hcap]
  simp only [bind, Option.bind, show isDynamicABIType (Model.u256) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [encodeABIValuesFrom?]
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, Nat.reduceAdd]
  have hl (data : ByteArray) : data.toList.length = data.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [List.length_append, hl, wordArrayBytes_size, List.length_append, List.length_cons,
    collateralWords_length, show (offer.market.words (UInt256.ofNat 256)).length = 8 from rfl]
  have hoff : 480 + 32 * (8 + (4 * offer.market.collaterals.length + 1)) =
      offerCallbackOffset offer := by unfold offerCallbackOffset; omega
  rw [hoff]
  simp only [offerEncodedBytes, OfferData.words, wordArrayBytes, byteArray_toList_append,
    natBytes, word_toBytesBE_eq_toByteArray_toList, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc]
  simp only [padRightToWord, hl, byteArray_toList_eq, byteArray_zeroes_toList, zeroBytes,
    show ByteArray.empty.data.toList = [] from rfl, List.nil_append, List.append_assoc]
  rfl

end Benchmarks.Midnight
