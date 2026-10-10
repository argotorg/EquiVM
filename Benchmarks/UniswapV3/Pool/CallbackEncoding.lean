import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: an ABI tuple containing two scalar words and a byte array.
def wordPairBytesPayload (a b : UInt256) (data : ByteArray) : ByteArray :=
  a.toByteArray ++ b.toByteArray ++ (UInt256.ofNat 96).toByteArray ++
    (UInt256.ofNat data.size).toByteArray ++ data ++ ByteArray.zeroes (paddedSize data.size - data.size)

theorem wordPairBytesEncoding (ty0 ty1 : ABIType) (v0 v1 : Value) (a b : UInt256)
    (data : ByteArray) (hd0 : isDynamicABIType ty0 = false) (hd1 : isDynamicABIType ty1 = false)
    (hs0 : staticABIEncodedSize? ty0 = some 32) (hs1 : staticABIEncodedSize? ty1 = some 32)
    (he0 : encodeABIValue? ty0 v0 = some (EVM.Word.toBytesBE a))
    (he1 : encodeABIValue? ty1 v1 = some (EVM.Word.toBytesBE b)) :
    encodeReturnValues? [ty0,ty1,.bytes] [v0,v1,.bytes data] =
      some (wordPairBytesPayload a b data) := by
  have hhead : abiTupleHeadSize? [ty0,ty1,.bytes] = some 96 := by
    simp only [abiTupleHeadSize?, hd0, hd1, Bool.false_eq_true, if_false, hs0, hs1,
      isDynamicABIType, if_true, bind, Option.bind]
  have heD : encodeABIValue? .bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) := by rw [encodeABIValue?]
  rw [encodeReturnValues?, encodeABIValues?, hhead]
  simp only [bind, Option.bind, encodeABIValuesFrom?, he0, he1, heD, hd0, hd1,
    Bool.false_eq_true, if_false, isDynamicABIType, if_true, List.length_nil, Nat.add_zero,
    List.nil_append, List.append_nil]
  rw [mk_toArray_eq]
  simp only [List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    natBytes_toByteArray, padRightToWord_toByteArray, wordPairBytesPayload, ByteArray.append_assoc]

def flashCallbackCalldata (fee0 fee1 : UInt256) (data : ByteArray) : ByteArray :=
  selectorBytes 0xe9 0xcb 0xaf 0xb0 ++ wordPairBytesPayload fee0 fee1 data

theorem flashCallbackEncode (fee0 fee1 : UInt256) (data : ByteArray) :
    externalABI.encode? "uniswapV3FlashCallback"
      [.int (Int.ofNat fee0.toNat), .int (Int.ofNat fee1.toNat), .bytes data] =
      some (flashCallbackCalldata fee0 fee1 data) :=
  encodeCall_of_encodeReturn (selectorBytes 0xe9 0xcb 0xaf 0xb0)
    (wordPairBytesEncoding abiUInt256 abiUInt256 _ _ fee0 fee1 data rfl rfl rfl rfl
      (encodeABIValue_uint256 fee0) (encodeABIValue_uint256 fee1))

theorem flashCallbackDecode (out : ByteArray) :
    externalABI.decode? "uniswapV3FlashCallback" out = some [] := rfl

theorem wordPairBytesPayload_size (a b : UInt256) (data : ByteArray) :
    (wordPairBytesPayload a b data).size = 128 + paddedSize data.size := by
  simp only [wordPairBytesPayload, ByteArray.size_append, toByteArray_size, ByteArray_zeroes_size]
  have hb : data.size ≤ paddedSize data.size := by unfold paddedSize; omega
  omega

theorem flashCallbackCalldata_size (a b : UInt256) (data : ByteArray) :
    (flashCallbackCalldata a b data).size = 132 + paddedSize data.size := by
  rw [flashCallbackCalldata, ByteArray.size_append, wordPairBytesPayload_size]
  change 4 + (128 + paddedSize data.size) = 132 + paddedSize data.size
  omega

end Benchmarks.UniswapV3.Pool
