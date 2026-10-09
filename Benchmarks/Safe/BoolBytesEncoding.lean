import Benchmarks.Safe.MemoryBytesEncodingInto

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: ABI return data consisting of a bool and dynamic bytes.
def boolBytesReturnBytes (z : Bool) (out : ByteArray) : ByteArray :=
  z.toUInt256.toByteArray ++ (⟨64⟩ : UInt256).toByteArray ++
    (UInt256.ofNat out.size).toByteArray ++ out ++
    ByteArray.zeroes (ABI.paddedSize out.size - out.size)

theorem boolBytesReturnEncoding (z : Bool) (out : ByteArray) :
    encodeReturnValues? [.elem .bool, .bytes] [.bool z, .bytes out] =
      some (boolBytesReturnBytes z out) := by
  have hz := encodeABIValue_bool z
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, hz, encodeABIValue?, bind, Option.bind,
    pure, List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
    byteArray_mk_toArray_eq_toByteArray, list_toByteArray_append, natBytes_toByteArray,
    padRightToWord_toByteArray, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false]
  simp only [boolBytesReturnBytes, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]
  rfl

def boolBytesHeaderMemory (mem : ByteArray) (dst : Nat) (z : Bool) : ByteArray :=
  writeWords mem dst [z.toUInt256, ⟨64⟩]

theorem boolBytesHeaderMemory_size (mem : ByteArray) (dst : Nat) (z : Bool) :
    (boolBytesHeaderMemory mem dst z).size = max mem.size (dst + 64) := by
  simp only [boolBytesHeaderMemory, writeWords, writeWord_sparse_size]
  omega

theorem boolBytesEncodedRead (mem : ByteArray) (dst len : Nat) (words : List UInt256)
    (z : Bool) (out : ByteArray) (hn : words.length = (len + 31) / 32)
    (hl : out.size = len) (hw : (wordBytes words).extract 0 len = out) :
    (memoryBytesEncodedInto (boolBytesHeaderMemory mem dst z) (dst + 64) len words).readWithPadding
      dst (96 + 32 * words.length) = boolBytesReturnBytes z out := by
  have hsize : dst + (96 + 32 * words.length) ≤
      (memoryBytesEncodedInto (boolBytesHeaderMemory mem dst z) (dst + 64) len words).size := by
    rw [memoryBytesEncodedInto_size _ _ _ _ hn, hn]
    omega
  have hh : (boolBytesHeaderMemory mem dst z).readWithPadding dst 64 =
      z.toUInt256.toByteArray ++ (⟨64⟩ : UInt256).toByteArray := by
    have hr := WordArrayMemory.read (boolBytesHeaderMemory mem dst z) dst [z.toUInt256, ⟨64⟩]
      (writeWords_view _ _ _) (by rw [boolBytesHeaderMemory_size]; simp)
    simpa only [List.length_cons, List.length_nil, wordBytes, ByteArray.append_empty] using hr
  rw [show 96 + 32 * words.length = 64 + (32 + 32 * words.length) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) (by omega),
    memoryBytesEncodedInto_preserved _ _ _ _ _ _
      (by rw [boolBytesHeaderMemory_size]; omega) (by omega), hh,
    memoryBytesEncodedInto_read _ _ _ _ hn, hw]
  simp only [boolBytesReturnBytes, hl, ABI.paddedSize, hn, ByteArray.append_assoc,
    Nat.mul_comm]

end Benchmarks.Safe
