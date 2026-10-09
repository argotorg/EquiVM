import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsABI
import Reasoning.HeapMemory

/-! The selector, offset, length, and singleton payload in the `extSloads` call buffer. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: a word write above an in-bounds load preserves the loaded value.
theorem memLoad_write_above (mem : ByteArray) (read : UInt256) (off : Nat) (word : UInt256)
    (hin : read.toNat + 32 ≤ mem.size) (hbelow : read.toNat + 32 ≤ off) :
    memLoad read (writeWord mem off word) = memLoad read mem := by
  unfold memLoad
  rw [if_neg (by rw [writeWord_sparse_size]; omega), if_neg (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hbelow, hin⟩)]

-- GENERALIZES writeCascade_read_window_of_head: sparse first writes need no gap bound.
theorem sparseCascade_read_window (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (rest : List (Nat × UInt256))
    (hlater : WindowDisjointFromWrites (max mem.size (off + 32)) (off + start) len rest)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding (off + start) len =
      word.toByteArray.extract start (start + len) := by
  rw [writeCascade_cons, writeCascade_read_preserved_len _ _ _ _
    (by simpa only [writeWord_sparse_size] using hlater) hpos hlen64]
  exact writeWord_sparse_read_window mem off start len word hwithin hpos hlen64

def extSloadsSelectorWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 0x7784c685) ⟨224⟩

def extSloadsCallMem (mem : ByteArray) (ptr : Nat) (slot : UInt256) : ByteArray :=
  writeCascade mem [(ptr, extSloadsSelectorWord), (ptr + 4, ⟨32⟩),
    (ptr + 36, ⟨1⟩), (ptr + 68, slot)]

theorem extSloadsCallMem_size (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).size = max mem.size (ptr + 100) := by
  simp only [extSloadsCallMem, writeCascade_cons, writeCascade_nil, writeWord_sparse_size]
  omega

theorem extSloadsCallMem_selector (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).readWithPadding ptr 4 = extSloadsSelector := by
  have hu := lt_usize 0 (by decide)
  have h := sparseCascade_read_window mem ptr 0 4 extSloadsSelectorWord
    [(ptr + 4, ⟨32⟩), (ptr + 36, ⟨1⟩), (ptr + 68, slot)]
    (by
      simp only [WindowDisjointFromWrites, Nat.add_zero]
      refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
        ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega)
    (by decide) (by decide) (by decide)
  have hselector : extSloadsSelectorWord.toByteArray.extract 0 4 = extSloadsSelector :=
    by decide +kernel
  simpa only [Nat.add_zero, Nat.zero_add, hselector] using h

theorem extSloadsCallMem_offset (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).readWithPadding (ptr + 4) 32 =
      (⟨32⟩ : UInt256).toByteArray := by
  apply sparseCascade_read_word _ _ _ [(ptr + 36, ⟨1⟩), (ptr + 68, slot)]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> omega

theorem extSloadsCallMem_length (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).readWithPadding (ptr + 36) 32 =
      (⟨1⟩ : UInt256).toByteArray := by
  apply sparseCascade_read_word _ _ _ [(ptr + 68, slot)]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl
  omega

theorem extSloadsCallMem_slot (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).readWithPadding (ptr + 68) 32 = slot.toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem extSloadsCallMem_read (mem : ByteArray) (ptr : Nat) (slot : UInt256) :
    (extSloadsCallMem mem ptr slot).readWithPadding ptr 100 = extSloadsCalldata slot := by
  have hs := extSloadsCallMem_size mem ptr slot
  have hlast : (extSloadsCallMem mem ptr slot).readWithPadding (ptr + 36) 64 =
      (⟨1⟩ : UInt256).toByteArray ++ slot.toByteArray := by
    rw [byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide)
      (by omega), extSloadsCallMem_length, show ptr + 36 + 32 = ptr + 68 from by omega,
      extSloadsCallMem_slot]
  have hargs : (extSloadsCallMem mem ptr slot).readWithPadding (ptr + 4) 96 =
      (⟨32⟩ : UInt256).toByteArray ++ ((⟨1⟩ : UInt256).toByteArray ++ slot.toByteArray) := by
    rw [byteArray_readWithPadding_split_unbounded _ _ 32 64 (by decide) (by decide)
      (by omega), extSloadsCallMem_offset, show ptr + 4 + 32 = ptr + 36 from by omega, hlast]
  rw [byteArray_readWithPadding_split_unbounded _ _ 4 96 (by decide) (by decide)
    (by omega), extSloadsCallMem_selector, hargs]
  rfl

theorem extSloadsCallMem_free (mem : ByteArray) (ptr : Nat) (slot : UInt256)
    (hin : 96 ≤ mem.size) (hptr : 96 ≤ ptr) :
    (extSloadsCallMem mem ptr slot).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  apply sparseCascade_read_below _ _ _ hin
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> omega

end Benchmarks.Morpho.MetaMorphoV1_1
