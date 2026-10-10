import Benchmarks.UniswapV3.Pool.SafeTransferMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def safeTransferArgsMem (mem : ByteArray) (p recipientWord value : UInt256) : ByteArray :=
  writeWord (writeWord mem (p.toNat + 36) recipientWord) (p.toNat + 68) value

def safeTransferHeadMem (mem : ByteArray) (p recipientWord value : UInt256) : ByteArray :=
  writeWord (writeWord (safeTransferArgsMem mem p recipientWord value) p.toNat ⟨68⟩)
    64 (p + ⟨100⟩)

def safeTransferBuildMem (mem : ByteArray) (p recipientWord value : UInt256) : ByteArray :=
  writeWord (safeTransferHeadMem mem p recipientWord value) (p.toNat + 32)
    (transferSelectorPatchedWord (memLoad (p + ⟨32⟩) (safeTransferHeadMem mem p recipientWord value)))

theorem safeTransferArgsMem_size (mem : ByteArray) (p recipientWord value : UInt256) :
    (safeTransferArgsMem mem p recipientWord value).size = max mem.size (p.toNat + 100) := by
  simp only [safeTransferArgsMem, writeWord_sparse_size]
  omega

theorem safeTransferHeadMem_size (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    (safeTransferHeadMem mem p recipientWord value).size = max mem.size (p.toNat + 100) := by
  simp only [safeTransferHeadMem, writeWord_sparse_size, safeTransferArgsMem_size]
  omega

theorem safeTransferBuildMem_size (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    (safeTransferBuildMem mem p recipientWord value).size = max mem.size (p.toNat + 100) := by
  simp only [safeTransferBuildMem, writeWord_sparse_size, safeTransferHeadMem_size _ _ _ _ hp]
  omega

theorem safeTransferArgsMem_load64 {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipientWord value : UInt256) :
    memLoad (UInt256.ofNat 64) (safeTransferArgsMem mem p recipientWord value) = p := by
  have hp := hm.lower
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [safeTransferArgsMem_size]; have hp := hm.lower; omega
  · change (safeTransferArgsMem mem p recipientWord value).readWithPadding 64 32 = _
    unfold safeTransferArgsMem
    rw [writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by omega, by
      rw [writeWord_sparse_size]; have hs := hm.size; omega⟩),
      writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨by have hp := hm.lower; omega, hm.size⟩)]
    exact hm.free

theorem safeTransferHeadMem_read64 (mem : ByteArray) (p recipientWord value : UInt256) :
    (safeTransferHeadMem mem p recipientWord value).readWithPadding 64 32 =
      (p + ⟨100⟩).toByteArray := writeWord_sparse_read_back _ _ _

theorem safeTransferHeadMem_read_length (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    (safeTransferHeadMem mem p recipientWord value).readWithPadding p.toNat 32 =
      (⟨68⟩ : UInt256).toByteArray := by
  unfold safeTransferHeadMem
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by
    rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem safeTransferHeadMem_read_args {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipientWord value : UInt256) :
    (safeTransferHeadMem mem p recipientWord value).readWithPadding (p.toNat + 36) 32 =
      recipientWord.toByteArray ∧
    (safeTransferHeadMem mem p recipientWord value).readWithPadding (p.toNat + 68) 32 =
      value.toByteArray := by
  have hp := hm.lower
  have hg := hm.gap
  have hu := lt_usize 68 (by decide)
  constructor
  · change (writeCascade mem [(p.toNat + 36, recipientWord), (p.toNat + 68, value),
        (p.toNat, ⟨68⟩), (64, p + ⟨100⟩)]).readWithPadding (p.toNat + 36) 32 = _
    apply writeCascade_read_word_of_head
    · omega
    · simp [WindowDisjointFromWrites, Nat.add_assoc]; omega
  · change (writeCascade (writeWord mem (p.toNat + 36) recipientWord)
        [(p.toNat + 68, value), (p.toNat, ⟨68⟩), (64, p + ⟨100⟩)]).readWithPadding (p.toNat + 68) 32 = _
    apply writeCascade_read_word_of_head
    · rw [writeWord_sparse_size]; omega
    · rw [writeWord_sparse_size]
      simp [WindowDisjointFromWrites, Nat.add_assoc]; omega

theorem safeTransferBuildMem_read64 (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    (safeTransferBuildMem mem p recipientWord value).readWithPadding 64 32 =
      (p + ⟨100⟩).toByteArray := by
  unfold safeTransferBuildMem
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
    rw [safeTransferHeadMem_size _ _ _ _ hp]; omega⟩), safeTransferHeadMem_read64]

theorem safeTransferBuildMem_load_length (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    memLoad p (safeTransferBuildMem mem p recipientWord value) = ⟨68⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [safeTransferBuildMem_size _ _ _ _ hp]; omega
  · unfold safeTransferBuildMem
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
      rw [safeTransferHeadMem_size _ _ _ _ hp]; omega⟩), safeTransferHeadMem_read_length _ _ _ _ hp]

theorem safeTransferBuildMem_load64 (mem : ByteArray) (p recipientWord value : UInt256)
    (hp : 128 ≤ p.toNat) :
    memLoad (UInt256.ofNat 64) (safeTransferBuildMem mem p recipientWord value) = p + ⟨100⟩ := by
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [safeTransferBuildMem_size _ _ _ _ hp]; omega
  · exact safeTransferBuildMem_read64 _ _ _ _ hp

theorem safeTransferBuildMem_prefix (mem : ByteArray) (p recipientWord value : UInt256) :
    MemoryPrefix mem (safeTransferBuildMem mem p recipientWord value) p.toNat := by
  unfold safeTransferBuildMem safeTransferHeadMem safeTransferArgsMem
  refine (memoryPrefix_sparse_writeWord mem (p.toNat + 36) p.toNat recipientWord
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ (p.toNat + 68) p.toNat value
    (Or.inl (by omega))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ p.toNat p.toNat ⟨68⟩
    (Or.inl (le_refl _))).trans ?_
  refine (memoryPrefix_sparse_writeWord _ 64 p.toNat (p + ⟨100⟩)
    (Or.inr (by decide))).trans ?_
  exact memoryPrefix_sparse_writeWord _ (p.toNat + 32) p.toNat _ (Or.inl (by omega))

theorem safeTransferBuildMem_calldata {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (recipient : AccountAddress) (value : UInt256)
    (hbound : p.toNat + 100 < UInt256.size) :
    (safeTransferBuildMem mem p (EVM.word recipient.val) value).readWithPadding
      (p.toNat + 32) 68 = safeTransferCalldata recipient value := by
  obtain ⟨hto, hvalue⟩ := safeTransferHeadMem_read_args hm (EVM.word recipient.val) value
  exact transferSelectorPatch_read _ p _ _ hbound
    (by rw [safeTransferHeadMem_size _ _ _ _ hm.lower]; omega) hto hvalue

end Benchmarks.UniswapV3.Pool
