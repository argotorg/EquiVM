import Benchmarks.Safe.AddressArrayEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def wordBufferReturnBytes (words : List UInt256) : ByteArray :=
  wordBytes (⟨32⟩ :: UInt256.ofNat (32 * words.length) :: words)

-- LIBRARY CANDIDATE: whole words need no padding when returned as dynamic bytes.
theorem wordBufferReturnEncoding (words : List UInt256) :
    encodeReturnValues? [.bytes] [.bytes (wordBytes words)] =
      some (wordBufferReturnBytes words) := by
  have hp : ABI.paddedSize (wordBytes words).size = (wordBytes words).size := by
    rw [wordBytes_size, ABI.paddedSize]
    omega
  rw [wordBytes_size] at hp
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    encodeABIValuesFrom?, encodeABIValue?, bind, Option.bind, pure, List.length_nil,
    Nat.add_zero, List.nil_append, List.append_nil, byteArray_mk_toArray_eq_toByteArray,
    list_toByteArray_append, natBytes_toByteArray, padRightToWord_toByteArray, hp,
    Nat.sub_self, zeroes_zero rfl,
    ByteArray.append_empty, wordBytes_size, Bool.true_eq, ite_true]
  rfl

end Benchmarks.Safe
