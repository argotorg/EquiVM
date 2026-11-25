import Benchmarks.Midnight.CalldataWordArrayEncoder
import Benchmarks.Midnight.ByteCopyMemory

/-! The word contents and preserved regions of a bulk-encoded calldata array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem calldataArrayCopyMemory_size (mem bytes : ByteArray) (output ptr n : Nat)
    (hs : ptr + 32 * n ≤ bytes.size) :
    (calldataArrayCopyMemory mem output bytes ptr n).size =
      max mem.size (output + 32 + 32 * n) := by
  by_cases hn : n = 0
  · subst n
    simp only [calldataArrayCopyMemory, Nat.mul_zero, ByteArray.write, if_true,
      writeWord_sparse_size, Nat.add_zero]
  · rw [calldataArrayCopyMemory, copyWindow_size _ _ _ _ _ (by omega) hs
      (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
    omega

theorem calldataArrayCopyMemory_read_preserved (mem bytes : ByteArray)
    (output ptr n read : Nat) (hs : ptr + 32 * n ≤ bytes.size)
    (hin : read + 32 ≤ mem.size)
    (hd : read + 32 ≤ output ∨ output + 32 + 32 * n ≤ read) :
    (calldataArrayCopyMemory mem output bytes ptr n).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hn : n = 0
  · subst n
    simp only [calldataArrayCopyMemory, Nat.mul_zero, ByteArray.write, if_true]
    exact writeWord_sparse_read_preserved _ _ _ _ (by
      rcases hd with hd | hd
      · exact Or.inl ⟨hd, hin⟩
      · exact Or.inr ⟨by omega, hin⟩)
  · rw [calldataArrayCopyMemory, copyWindow_read_preserved _ _ _ _ _ _ (by omega) hs
      (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega)
      (by rcases hd with hd | hd <;> omega)]
    exact writeWord_sparse_read_preserved _ _ _ _ (by
      rcases hd with hd | hd
      · exact Or.inl ⟨hd, hin⟩
      · exact Or.inr ⟨by omega, hin⟩)

theorem calldataArrayCopyMemory_load_preserved (mem bytes : ByteArray)
    (output ptr n : Nat) (read : UInt256) (hs : ptr + 32 * n ≤ bytes.size)
    (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ output ∨ output + 32 + 32 * n ≤ read.toNat) :
    memLoad read (calldataArrayCopyMemory mem output bytes ptr n) = memLoad read mem := by
  have hsize := calldataArrayCopyMemory_size mem bytes output ptr n hs
  unfold memLoad
  rw [if_neg (by rw [hsize]; omega), if_neg (by omega),
    calldataArrayCopyMemory_read_preserved _ _ _ _ _ _ hs hin hd]

theorem calldataArrayCopyMemory_words (mem bytes : ByteArray) (output ptr n : Nat)
    (hs : ptr + 32 * n ≤ bytes.size) (hb : output + 32 + 32 * n < UInt256.size) :
    MemoryWords (calldataArrayCopyMemory mem output bytes ptr n) output
      (UInt256.ofNat n :: calldataArrayWords bytes n ptr) := by
  have hl : (UInt256.ofNat n :: calldataArrayWords bytes n ptr).length = n + 1 := by
    simp only [List.length_cons, calldataArrayWords_length]
  have hsize := calldataArrayCopyMemory_size mem bytes output ptr n hs
  refine ⟨by rw [hl]; omega, by rw [hl, hsize]; omega, fun i ↦ ?_⟩
  have hi : i.val < n + 1 := by simpa only [hl] using i.isLt
  have hoff : (UInt256.ofNat (output + 32 * i.val)).toNat = output + 32 * i.val :=
    UInt256.toNat_ofNat_of_lt (by omega)
  apply mloadWordValue_of_readWithPadding (by rw [hoff, hsize]; omega)
  rw [hoff]
  rcases i with ⟨i, hi'⟩
  cases i with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    by_cases hn : n = 0
    · subst n
      simp only [calldataArrayCopyMemory, Nat.mul_zero, ByteArray.write, if_true]
      exact writeWord_sparse_read_back _ _ _
    · rw [calldataArrayCopyMemory, copyWindow_read_preserved _ _ _ _ _ _ (by omega) hs
        (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega)
        (Or.inl le_rfl)]
      exact writeWord_sparse_read_back _ _ _
  | succ i =>
    have hin : i < (calldataArrayWords bytes n ptr).length := by
      rw [calldataArrayWords_length]
      omega
    change _ = ((calldataArrayWords bytes n ptr)[(⟨i, hin⟩ : Fin _)]).toByteArray
    rw [calldataArrayWords_get]
    dsimp only
    rw [calldataWord_bytes_at (by omega)]
    have he : output + 32 * (i + 1) = output + 32 + 32 * i := by omega
    rw [he, calldataArrayCopyMemory, copyWindow_read_word _ _ _ _ _ _ (by omega) hs
      (by rw [writeWord_sparse_size]; omega) (by omega)]
    exact readWithPadding_eq_extract _ _ (by omega)

theorem calldataArrayCopyMemory_prefix (mem bytes : ByteArray) (output ptr n limit : Nat)
    (hs : ptr + 32 * n ≤ bytes.size) (hlimit : limit ≤ output) :
    MemoryPrefix mem (calldataArrayCopyMemory mem output bytes ptr n) limit := by
  refine ⟨by rw [calldataArrayCopyMemory_size _ _ _ _ _ hs]; omega, fun read _ hlim hin ↦ ?_⟩
  exact calldataArrayCopyMemory_read_preserved _ _ _ _ _ _ hs hin (Or.inl (by omega))

theorem MemoryWords.calldataArrayCopy {mem bytes : ByteArray} {output ptr n base : Nat}
    {words : List UInt256} (h : MemoryWords mem base words) (hs : ptr + 32 * n ≤ bytes.size)
    (hd : base + 32 * words.length ≤ output ∨ output + 32 + 32 * n ≤ base) :
    MemoryWords (calldataArrayCopyMemory mem output bytes ptr n) base words := by
  apply h.preserve (by rw [calldataArrayCopyMemory_size _ _ _ _ _ hs]; omega)
  intro read hlo hhi
  exact calldataArrayCopyMemory_load_preserved _ _ _ _ _ _ hs (hhi.trans h.size)
    (by rcases hd with hd | hd <;> omega)

theorem calldataArrayCopyMemory_read_before (mem bytes : ByteArray)
    (output ptr n read count : Nat) (hs : ptr + 32 * n ≤ bytes.size)
    (hc : 0 < count) (hc64 : count < 2^64)
    (hin : read + count ≤ mem.size) (hl : read + count ≤ output) :
    (calldataArrayCopyMemory mem output bytes ptr n).readWithPadding read count =
      mem.readWithPadding read count := by
  by_cases hz : n = 0
  · subst n
    simp only [calldataArrayCopyMemory, Nat.mul_zero, ByteArray.write, if_true]
    exact writeWord_sparse_read_preserved_len _ _ _ _ _ hin (Or.inl hl) hc hc64
  · rw [calldataArrayCopyMemory, copySparse_read_before _ _ _ _ _ _ _ (by omega) hs hc
        (by rw [writeWord_sparse_size]; omega) (by omega),
      writeWord_sparse_read_preserved_len _ _ _ _ _ hin (Or.inl hl) hc hc64]

end Benchmarks.Midnight
