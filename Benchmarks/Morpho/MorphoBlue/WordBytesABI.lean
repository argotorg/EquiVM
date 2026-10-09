import Benchmarks.Morpho.MorphoBlue.SafeTransferABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: callback arguments consisting of a full-width word and dynamic bytes.
def wordBytesArguments (word : UInt256) (data : ByteArray) : ByteArray :=
  (returnWordBytes [word, UInt256.ofNat 64, UInt256.ofNat data.size] ++ data) ++
    ByteArray.zeroes (paddedSize data.size - data.size)

def wordBytesCalldata (selector : ByteArray) (word : UInt256) (data : ByteArray) : ByteArray :=
  selector ++ wordBytesArguments word data

theorem wordBytesArguments_encode (word : UInt256) (data : ByteArray) :
    encodeReturnValues? [abiUInt256, .bytes] [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesArguments word data) := by
  have hh : abiTupleHeadSize? [abiUInt256, .bytes] = some 64 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256]
  simp only [encodeReturnValues?, encodeABIValues?, hh, bind, Option.bind,
    encodeABIValuesFrom?, encodeABIValue_uint256,
    show isDynamicABIType abiUInt256 = false from rfl,
    show isDynamicABIType ABIType.bytes = true from rfl,
    show encodeABIValue? ABIType.bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) from by rw [encodeABIValue?],
    Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hlen : data.toList.length = data.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [List.toList_toArray]
  rw [← byteArray_toList_eq]
  simp only [wordBytesArguments, byteArray_toList_append, returnWordBytes_toList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, byteArray_zeroes_toList,
    natBytes, padRightToWord, zeroBytes, hlen, List.append_assoc]
  simp only [byteArray_toList_eq, byteArray_zeroes_toList]
  rfl

theorem wordBytesArguments_size (word : UInt256) (data : ByteArray) :
    (wordBytesArguments word data).size = 96 + paddedSize data.size := by
  have hp := nat_le_paddedSize data.size
  simp only [wordBytesArguments, ByteArray.size_append, returnWordBytes_size,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, ByteArray_zeroes_size]
  omega

end Benchmarks.Morpho.MorphoBlue
