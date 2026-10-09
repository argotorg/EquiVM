import Benchmarks.Safe.Memory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a four-byte selector followed by two static ABI words.
def selectorWordPairMemory (mem : ByteArray) (ptr : Nat) (sel a b : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem ptr sel) (ptr + 4) a) (ptr + 36) b

theorem selectorWordPairMemory_size (mem : ByteArray) (ptr : Nat) (sel a b : UInt256) :
    (selectorWordPairMemory mem ptr sel a b).size = max mem.size (ptr + 68) := by
  simp only [selectorWordPairMemory, writeWord_sparse_size]
  omega

theorem selectorWordPairMemory_free (mem : ByteArray) (ptr : Nat) (sel a b : UInt256)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (selectorWordPairMemory mem ptr sel a b) = memLoad ⟨64⟩ mem := by
  have hr : (selectorWordPairMemory mem ptr sel a b).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
    rw [selectorWordPairMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        simp only [writeWord_sparse_size]; omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        simp only [writeWord_sparse_size]; omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hp, hm⟩)]
  have hs : 96 ≤ (selectorWordPairMemory mem ptr sel a b).size := by
    rw [selectorWordPairMemory_size]; omega
  simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    if_neg (show ¬ 64 ≥ (selectorWordPairMemory mem ptr sel a b).size by omega),
    if_neg (show ¬ 64 ≥ mem.size by omega), hr]

theorem selectorWordPairMemory_read (mem : ByteArray) (ptr : Nat) (sel a b : UInt256) :
    (selectorWordPairMemory mem ptr sel a b).readWithPadding ptr 68 =
      sel.toByteArray.extract 0 4 ++ a.toByteArray ++ b.toByteArray := by
  let m₁ := writeWord mem ptr sel
  let m₂ := writeWord m₁ (ptr + 4) a
  have hs₁ : ptr + 32 ≤ m₁.size := by
    dsimp [m₁]; rw [writeWord_sparse_size]; omega
  have hs₂ : ptr + 36 ≤ m₂.size := by
    dsimp [m₂]; rw [writeWord_sparse_size]; omega
  have hgap₂ : ptr + 4 - m₁.size < USize.size := by
    have hu := lt_usize 0 (by decide); omega
  have hgap₃ : ptr + 36 - m₂.size < USize.size := by
    have hu := lt_usize 0 (by decide); omega
  have hsel : (selectorWordPairMemory mem ptr sel a b).readWithPadding ptr 4 =
      sel.toByteArray.extract 0 4 := by
    change (writeWord m₂ (ptr + 36) b).readWithPadding ptr 4 = _
    rw [writeWord_read_preserved_len _ _ _ _ _ hgap₃
      (.inl ⟨by omega, by omega⟩) (by decide) (by decide)]
    rw [show m₂ = writeWord m₁ (ptr + 4) a from rfl,
      writeWord_read_preserved_len _ _ _ _ _ hgap₂
        (.inl ⟨by omega, by omega⟩) (by decide) (by decide)]
    simpa only [Nat.add_zero, Nat.zero_add] using
      writeWord_sparse_read_window mem ptr 0 4 sel (by decide) (by decide) (by decide)
  have ha : (selectorWordPairMemory mem ptr sel a b).readWithPadding (ptr + 4) 32 =
      a.toByteArray := by
    change (writeWord m₂ (ptr + 36) b).readWithPadding (ptr + 4) 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by omega⟩)]
    exact writeWord_sparse_read_back _ _ _
  have hb : (selectorWordPairMemory mem ptr sel a b).readWithPadding (ptr + 36) 32 =
      b.toByteArray := writeWord_sparse_read_back _ _ _
  have hs : ptr + 68 ≤ (selectorWordPairMemory mem ptr sel a b).size := by
    rw [selectorWordPairMemory_size]; omega
  rw [show 68 = 4 + (32 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 4 64 (by decide) (by decide) hs,
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide) (by omega),
    show ptr + 4 + 32 = ptr + 36 by omega, hsel, ha, hb, ByteArray.append_assoc]

-- LIBRARY CANDIDATE: external calls with bytes32 and bool arguments have two static words.
theorem encodeBytes32BoolCall (sel : ByteArray) (hash : UInt256) (z : Bool)
    (hs : sel.size = 4) :
    ABI.encodeCallWithSelector? sel [.elem (.bytes abiBytes32Width), .elem .bool]
      [.fixedBytes abiBytes32Width (EVM.Word.toBytesBE hash), .bool z] =
      some (sel ++ hash.toByteArray ++ z.toUInt256.toByteArray) := by
  have hh := encodeABIValue_bytes32_word hash
  have hb := encodeABIValue_bool z
  simp only [encodeCallWithSelector?, hs, beq_self_eq_true, Bool.not_true, ite_false,
    encodeABIValues?, abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
    encodeABIValuesFrom?, hh, hb, bind, Option.bind, pure, List.nil_append,
    List.append_nil, Bool.false_eq_true]
  simp only [byteArray_mk_toArray_eq_toByteArray, list_toByteArray_append,
    byteArray_toList_toByteArray, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

end Benchmarks.Safe
