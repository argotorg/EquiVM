import Benchmarks.Midnight.OfferEncoding
import Benchmarks.Midnight.MarketIdSource

/-! Exact ratifier-call calldata and bytes32 response decoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem OfferData.abiOfferValue (offer : OfferData) :
    Model.abiValue (Model.offerValue offer.value) = offer.value := by
  simp only [OfferData.value, Model.offerValue, List.zip_cons_cons, List.zip_nil_right,
    Model.abiValue, Model.abiFields, offer.market.abiMarketValue, wordToElemBool, wordBytes32Value]

def ratifierArguments (offer : OfferData) (data : ByteArray) (taker : AccountAddress) : List Value :=
  [Model.offerValue offer.value, .bytes data, .address taker]

def ratifierCalldata (offer : OfferData) (data : ByteArray) (taker : AccountAddress) : ByteArray :=
  ⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ ++
    wordArrayBytes [UInt256.ofNat 96, UInt256.ofNat (96 + offerEncodedSize offer),
      UInt256.ofNat taker.val] ++ offerEncodedBytes offer ++
    (UInt256.ofNat data.size).toByteArray ++ data ++
    ByteArray.zeroes (paddedSize data.size - data.size)

def ratifierCalldataSize (offer : OfferData) (data : ByteArray) : Nat :=
  132 + offerEncodedSize offer + paddedSize data.size

theorem ratifierCalldata_size (offer : OfferData) (data : ByteArray) (taker : AccountAddress) :
    (ratifierCalldata offer data taker).size = ratifierCalldataSize offer data := by
  have hp := nat_le_paddedSize data.size
  simp only [ratifierCalldata, ByteArray.size_append, wordArrayBytes_size, toByteArray_size,
    ByteArray_zeroes_size, List.length_cons, List.length_nil, offerEncodedBytes_size,
    show (ByteArray.mk #[0x22, 0x3c, 0x4e, 0xd6]).size = 4 from rfl, ratifierCalldataSize]
  omega

theorem encodeRatifierCall (offer : OfferData) (data : ByteArray) (taker : AccountAddress)
    (hc : OfferCanonical offer) :
    config.externalABI.encode? "isRatified" (ratifierArguments offer data taker) =
      some (ratifierCalldata offer data taker) := by
  change encodeCallWithSelector? ⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ [Model.offerABI, .bytes, abiAddress]
    [Model.abiValue (Model.offerValue offer.value), .bytes data, .address taker] = _
  rw [offer.abiOfferValue]
  have ho := offer.encodeValue hc
  have ht := encodeABIValue_accountAddress taker
  have hd : encodeABIValue? .bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) := by simp only [encodeABIValue?]
  have hl (bytes : ByteArray) : bytes.toList.length = bytes.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    show isDynamicABIType Model.offerABI = true from rfl,
    staticABIEncodedSize?, isDynamicABIType, Bool.false_eq_true, if_true, if_false, bind, Option.bind,
    encodeABIValuesFrom?, ho, hd, ht, List.nil_append, List.append_nil,
    List.length_nil, Nat.add_zero, Nat.reduceAdd]
  simp only [hl, offerEncodedBytes_size, natBytes, word_toBytesBE_eq_toByteArray_toList,
    List.toByteArray_append, byteArray_toList_toByteArray, padRightToWord_toByteArray,
    ratifierCalldata, wordArrayBytes, ByteArray.append_empty, ByteArray.append_assoc]
  rfl

theorem decodeRatifierCall {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "isRatified" out =
      some [wordBytes32Value (calldataWord out 0)] := decodeFlashLoanCallback h32

theorem decodeRatifierCall_short {out : ByteArray} (h32 : out.size < 32) :
    config.externalABI.decode? "isRatified" out = none := decodeFlashLoanCallback_short h32

end Benchmarks.Midnight
