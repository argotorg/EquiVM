import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketABI

/-! Static tuple encoding and the single-word result of the rate-model call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: tuple encoding and canonical unsigned/address scalar encoders.
theorem encodeTupleValue (types : List ABIType) (values : List Value) :
    encodeABIValue? (.tuple types) (.tuple values) = encodeABIValues? types values := by
  simp only [encodeABIValue?]

theorem encodeUnsignedWord (bits : ABI.BitWidth) (word : UInt256)
    (hbits : bits.val ≠ 0) (hfit : word.toNat < 2 ^ bits.val) :
    encodeABIValue? (.elem (.int (.uint bits))) (uint256Value word) =
      some word.toByteArray.toList := by
  have hw : EVM.word word.toNat = word := u256_ofNat_toNat word
  simp [encodeABIValue?, encodeABIWord?, uint256Value, EVM.twoPow, hw, hbits,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]
  rw [if_pos (by exact_mod_cast hfit)]
  rfl

theorem encodeAddressWord (address : AccountAddress) :
    encodeABIValue? abiAddress (.address address) =
      some (UInt256.ofNat address.toNat).toByteArray.toList := by
  simp [abiAddress, encodeABIValue?, encodeABIWord?,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]
  rfl

def marketParamsTypes : List ABIType :=
  [abiAddress, abiAddress, abiAddress, abiAddress, abiUInt256]

def rateParamsFields (p : MarketParamsData) : List Value :=
  [.address p.loanToken, .address p.collateralToken, .address p.oracle, .address p.irm,
    uint256Value p.lltv]

theorem marketParamsTupleEncode (p : MarketParamsData) :
    encodeABIValue? (.tuple marketParamsTypes) (.tuple (rateParamsFields p)) =
      some p.bytes.toList := by
  have hh : abiTupleHeadSize? marketParamsTypes = some 160 := by
    simp [marketParamsTypes, abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiAddress, abiUInt256]
  rw [encodeTupleValue, encodeABIValues?, hh]
  simp only [marketParamsTypes, rateParamsFields,
    encodeABIValuesFrom?, encodeAddressWord, encodeABIValue_uint256_word,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, MarketParamsData.bytes,
    MarketParamsData.words, wordBytes, byteArray_toList_append, ByteArray.append_empty,
    List.nil_append, List.append_nil, List.append_assoc, uint256Value]

def marketWords (out : ByteArray) : List UInt256 :=
  [calldataWord out 0, calldataWord out 32, calldataWord out 64,
    calldataWord out 96, calldataWord out 128, calldataWord out 160]

theorem marketTupleEncode (out : ByteArray) (hc : MarketChecks out) :
    encodeABIValue? (.tuple (List.replicate 6 marketUInt128)) (.tuple (marketFields out)) =
      some (wordBytes (marketWords out)).toList := by
  have hh : abiTupleHeadSize? (List.replicate 6 marketUInt128) = some 192 := by
    simp [List.replicate, marketUInt128, abiTupleHeadSize?, isDynamicABIType,
      staticABIEncodedSize?]
  have henc (off : Nat) (hfit : (calldataWord out off).toNat < 2 ^ 128) :=
    encodeUnsignedWord ⟨128, by decide⟩ (calldataWord out off) (by decide) hfit
  rw [encodeTupleValue, encodeABIValues?, hh]
  simp only [List.replicate, marketFields,
    encodeABIValuesFrom?, marketUInt128, henc 0 hc.2.1, henc 32 hc.2.2.1,
    henc 64 hc.2.2.2.1, henc 96 hc.2.2.2.2.1, henc 128 hc.2.2.2.2.2.1,
    henc 160 hc.2.2.2.2.2.2, isDynamicABIType, bind, Option.bind,
    Bool.false_eq_true, if_false, marketWords, wordBytes, byteArray_toList_append,
    ByteArray.append_empty, List.nil_append, List.append_nil, List.append_assoc]

def borrowRateSelector : ByteArray := ⟨#[0x8c, 0x00, 0xbf, 0x6b]⟩

def borrowRateSelectorWord : UInt256 := UInt256.shiftLeft ⟨2348859243⟩ ⟨224⟩

def borrowRateCalldata (p : MarketParamsData) (market : ByteArray) : ByteArray :=
  borrowRateSelector ++ wordBytes (p.words ++ marketWords market)

theorem borrowRateCalldata_size (p : MarketParamsData) (market : ByteArray) :
    (borrowRateCalldata p market).size = 356 := by
  simp only [borrowRateCalldata, ByteArray.size_append, wordBytes_size, List.length_append,
    MarketParamsData.words, marketWords, List.length_cons, List.length_nil]
  rfl

theorem borrowRateEncode (p : MarketParamsData) (market : ByteArray) (hc : MarketChecks market) :
    config.externalABI.encode? "borrowRateView" [p.value, marketValue market] =
      some (borrowRateCalldata p market) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x8c00bf6b).toBytesBE.drop 28).toArray)
    [.tuple marketParamsTypes, .tuple (List.replicate 6 marketUInt128)]
    [.tuple (rateParamsFields p), .tuple (marketFields market)] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x8c00bf6b).toBytesBE.drop 28).toArray =
    borrowRateSelector from by decide +kernel]
  have hh : abiTupleHeadSize?
      [.tuple marketParamsTypes, .tuple (List.replicate 6 marketUInt128)] = some 352 :=
    by simp [marketParamsTypes, marketUInt128, List.replicate, abiTupleHeadSize?,
      isDynamicABIType, isDynamicABITypeList, staticABIEncodedSize?, staticABIEncodedSizeList?,
      abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?,
    marketParamsTupleEncode, marketTupleEncode market hc,
    show isDynamicABIType (.tuple marketParamsTypes) = false from rfl,
    show isDynamicABIType (.tuple (List.replicate 6 marketUInt128)) = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    borrowRateCalldata, wordBytes_append, MarketParamsData.bytes]
  rw [List.toByteArray_append, byteArray_toList_toByteArray, byteArray_toList_toByteArray]

theorem borrowRateDecode {out : ByteArray} (hh : out.size < 2 ^ 255) :
    config.externalABI.decode? "borrowRateView" out =
      if 32 ≤ out.size then some [uint256Value (calldataWord out 0)] else none := by
  change (decodeReturnValues? [abiUInt256] out).bind some = _
  by_cases hl : 32 ≤ out.size
  · rw [if_pos hl, decodeReturnValues_uint256_ok hl hh]
    simp only [Option.bind_some]
    congr 3
    rw [← calldataWord_bytes hl, fromByteArrayBigEndian_toByteArray]
  · rw [if_neg hl, decodeReturnValues_uint256_none_short (by omega)]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
