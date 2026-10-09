import Reasoning.Solc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: MLOAD/MSTORE round-trip in the generated block-summary vocabulary.
theorem memLoad_write_same (mem : ByteArray) (off : Nat) (read word : UInt256)
    (heq : read.toNat = off) :
    memLoad read (word.toByteArray.write 0 mem off 32) = word := by
  subst off
  apply mloadWordValue_of_readWithPadding
  · change read.toNat < (writeWord mem read.toNat word).size
    rw [writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back mem read.toNat word

-- LIBRARY CANDIDATE: a disjoint MSTORE preserves an existing MLOAD word.
theorem memLoad_write_disjoint (mem : ByteArray) (off : Nat) (read word : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hdis : read.toNat + 32 ≤ off ∨ off + 32 ≤ read.toNat) :
    memLoad read (word.toByteArray.write 0 mem off 32) = memLoad read mem := by
  have hsize : (word.toByteArray.write 0 mem off 32).size =
      max mem.size (off + 32) := writeWord_sparse_size mem off word
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show (word.toByteArray.write 0 mem off 32).readWithPadding read.toNat 32 =
      mem.readWithPadding read.toNat 32 from
    writeWord_sparse_read_preserved mem off read.toNat word
      (hdis.elim (fun h ↦ .inl ⟨h, hin⟩) (fun h ↦ .inr ⟨h, hin⟩))]

-- LIBRARY CANDIDATE: expose word-write size without unfolding byte-array operations.
theorem wordWrite_size (mem : ByteArray) (off : Nat) (word : UInt256) :
    (word.toByteArray.write 0 mem off 32).size = max mem.size (off + 32) :=
  writeWord_sparse_size mem off word

-- LIBRARY CANDIDATE: canonical address words are unchanged by Solidity cleanup.
theorem easWord_mask (eas : EVM.Address) :
    UInt256.land solcAddrMask (UInt256.ofNat eas.val) = UInt256.ofNat eas.val := by
  apply solcAddrMask_clean_left
  rw [ulit_toNat' _ (by
    have ha := eas.isLt
    change eas.val < 2 ^ 256
    change eas.val < 2 ^ 160 at ha
    omega)]
  exact eas.isLt

-- LIBRARY CANDIDATE: recover an in-bounds byte window from its MLOAD value.
theorem readWord_of_memLoad (mem : ByteArray) (off : Nat) (word : UInt256)
    (hin : off + 32 ≤ mem.size) (hoff : off < UInt256.size)
    (hload : memLoad (UInt256.ofNat off) mem = word) :
    mem.readWithPadding off 32 = word.toByteArray := by
  rw [← hload]
  have hlt : off < mem.size := by omega
  simp only [memLoad, ulit_toNat' _ hoff, Nat.not_le_of_gt hlt, if_false]
  simpa only [uInt256OfByteArray_eq] using read32_roundtrip mem off hin

-- LIBRARY CANDIDATE: splitting an in-bounds read also permits empty pieces.
theorem readWithPadding_split (mem : ByteArray) (off n m : Nat)
    (hin : off + n + m ≤ mem.size) :
    mem.readWithPadding off (n + m) =
      mem.readWithPadding off n ++ mem.readWithPadding (off + n) m := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.zero_add, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.empty_append]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
  exact byteArray_readWithPadding_split_unbounded mem off n m (by omega) (by omega) hin

-- LIBRARY CANDIDATE: assemble adjacent ABI words from individual memory reads.
theorem readWithPadding_words (mem : ByteArray) (off : Nat) (words : List UInt256)
    (hin : off + 32 * words.length ≤ mem.size)
    (hwords : ∀ i : Fin words.length,
      mem.readWithPadding (off + 32 * i.val) 32 = words[i].toByteArray) :
    mem.readWithPadding off (32 * words.length) =
      (words.map UInt256.toByteArray).foldr (· ++ ·) ByteArray.empty := by
  induction words generalizing off with
  | nil => simp only [List.length_nil, Nat.mul_zero, byteArray_readWithPadding_zero,
      List.map_nil, List.foldr_nil]
  | cons word words ih =>
      have hlen : 32 * (word :: words).length = 32 + 32 * words.length := by simp; omega
      rw [hlen, readWithPadding_split _ _ _ _ (by rw [hlen] at hin; omega)]
      have hhead := hwords ⟨0, by simp⟩
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at hhead
      rw [hhead, ih (off + 32) (by simp only [List.length_cons] at hin; omega)]
      · rfl
      · intro i
        simpa only [List.getElem_cons_succ,
          show off + 32 * (i.val + 1) = off + 32 + 32 * i.val by omega] using
            hwords ⟨i.val + 1, by simp only [List.length_cons]; omega⟩

end Reasoning.Theory
