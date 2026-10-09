import Benchmarks.Safe.Common
import Benchmarks.Safe.PaddedWordMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a word write exactly at the current end appends its encoding.
theorem writeWordAtEnd (mem : ByteArray) (w : UInt256) {off : ℕ}
    (hsize : mem.size = off) :
    w.toByteArray.write 0 mem off 32 = mem ++ w.toByteArray := by
  rw [toByteArray_write_eq _ _ _ (by omega)
      (by simp only [hsize, Nat.sub_self]; exact lt_usize _ (by norm_num)),
    hsize, Nat.sub_self]
  rw [zeroes_zero rfl, ByteArray.append_empty]

-- GENERALIZES word-load reconstruction to words stored entirely in implicit zero memory.
theorem memLoad_of_wordRead (mem : ByteArray) (off value : UInt256)
    (hr : mem.readWithPadding off.toNat 32 = value.toByteArray) : memLoad off mem = value := by
  by_cases hi : off.toNat < mem.size
  · exact mloadWordValue_of_readWithPadding hi hr
  · have hz := readPastMemory mem off.toNat 32 (by omega)
    rw [hz, show ByteArray.zeroes 32 = (⟨0⟩ : UInt256).toByteArray from by decide +kernel] at hr
    have heq := congrArg (fun b ↦ UInt256.ofNat (fromByteArrayBigEndian b)) hr
    simp only [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat] at heq
    simpa [memLoad, show mem.size ≤ off.toNat by omega] using heq

-- LIBRARY CANDIDATE: copying implicit zero bytes beyond stored memory leaves its buffer unchanged.
theorem writePastSourceAtMemoryEnd (src mem : ByteArray) (len : Nat) :
    src.write src.size mem mem.size len = mem := by
  by_cases hz : len = 0
  · subst len
    exact byteArray_write_zero_length _ _ _ _
  · simp only [ByteArray.write, hz, if_false, Nat.le_refl, if_true,
      Nat.sub_self, Nat.min_zero, Nat.min_self]
    apply ByteArray.ext
    simp [ByteArray.data_copySlice, -ByteArray.size_data, ByteArray.size]

end Benchmarks.Safe
