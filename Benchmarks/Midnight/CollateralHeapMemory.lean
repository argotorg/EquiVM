import Benchmarks.Midnight.CollateralLoopMemory
import Benchmarks.Midnight.MemoryWords

/-! Preservation of previously decoded collateral records through the remaining loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem collateralStepMemory_preserved {mem : ByteArray} {ptr writePtr read : UInt256}
    (c : CollateralData) (hlo : 96 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hp : read.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 128 ≤ read.toNat)
    (hw : read.toNat + 32 ≤ writePtr.toNat ∨ writePtr.toNat + 32 ≤ read.toNat) :
    memLoad read (collateralStepMemory mem ptr writePtr c) = memLoad read mem := by
  have hs : mem.size ≤ (writeWord mem 64 (ptr + UInt256.ofNat 128)).size := by
    rw [writeWord_sparse_size]; omega
  have hs' := writeWordArray_size_ge (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat c.words
  rw [collateralStepMemory, collateralCopyMemory,
    memLoad_writeWord_preserved _ _ _ _ (by omega) hw,
    memLoad_writeWordArray_preserved _ _ read c.words (hin.trans hs) (by
      simpa only [CollateralData.words, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceMul] using hp),
    memLoad_writeWord_preserved _ _ _ _ hin (Or.inr hlo)]

theorem collateralLoopMemory_size {mem : ByteArray} {ptr writePtr : UInt256}
    (cs : List CollateralData) : mem.size ≤ (collateralLoopMemory mem ptr writePtr cs).size := by
  induction cs generalizing mem ptr writePtr with
  | nil => exact le_rfl
  | cons c cs ih => exact (collateralStepMemory_size c).trans (ih (mem := _) (ptr := _) (writePtr := _))

theorem collateralLoopMemory_preserved {mem : ByteArray} {ptr writePtr read : UInt256}
    (cs : List CollateralData)
    (hfit : ptr.toNat + 128 * cs.length < 2^64)
    (harray : writePtr.toNat + 32 * cs.length ≤ ptr.toNat)
    (hwrite : 96 ≤ writePtr.toNat)
    (hlo : 96 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hp : read.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 128 * cs.length ≤ read.toNat)
    (hw : read.toNat + 32 ≤ writePtr.toNat ∨ writePtr.toNat + 32 * cs.length ≤ read.toNat) :
    memLoad read (collateralLoopMemory mem ptr writePtr cs) = memLoad read mem := by
  induction cs generalizing mem ptr writePtr with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at hfit harray hp hw
    have hptr : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hwp : (writePtr + UInt256.ofNat 32).toNat = writePtr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    rw [collateralLoopMemory, ih (by rw [hptr]; omega) (by rw [hptr, hwp]; omega)
      (by rw [hwp]; omega) (hin.trans (collateralStepMemory_size c))
      (by rw [hptr]; omega) (by rw [hwp]; omega)]
    exact collateralStepMemory_preserved c hlo hin (by omega) (by omega)

def CollateralListStored (mem : ByteArray) (writePtr : UInt256) (limit : Nat) : List CollateralData → Prop
  | [] => True
  | c :: cs => ∃ ptr, 96 ≤ writePtr.toNat ∧ writePtr.toNat + 32 ≤ limit ∧
      writePtr.toNat + 32 ≤ mem.size ∧ memLoad writePtr mem = ptr ∧
      writePtr.toNat + 32 ≤ ptr.toNat ∧ ptr.toNat + 128 ≤ limit ∧ MemoryWords mem ptr.toNat c.words ∧
      CollateralListStored mem (writePtr + UInt256.ofNat 32) limit cs

theorem CollateralListStored.preserve {before after : ByteArray} {writePtr : UInt256}
    {limit : Nat} {cs : List CollateralData}
    (h : CollateralListStored before writePtr limit cs) (hp : MemoryPrefix before after limit) :
    CollateralListStored after writePtr limit cs := by
  induction cs generalizing writePtr with
  | nil => trivial
  | cons c cs ih =>
    rcases h with ⟨ptr, hwlo, hwlim, hwin, hw, hplo, hplim, hm, ht⟩
    refine ⟨ptr, hwlo, hwlim, hwin.trans hp.size, (hp.load writePtr hwlo hwlim hwin).trans hw,
      hplo, hplim, ?_, ih ht⟩
    apply hm.preserve hp.size
    intro read hlo hhi
    exact hp.load read (by omega) (by change read.toNat + 32 ≤ ptr.toNat + 32 * 4 at hhi; omega)
      (hhi.trans hm.size)

theorem CollateralListStored.writeWord_below {mem : ByteArray} {writePtr : UInt256}
    {limit off : Nat} {cs : List CollateralData}
    (h : CollateralListStored mem writePtr limit cs) (word : UInt256)
    (hlimit : limit < 2^64) (hbelow : off + 32 ≤ writePtr.toNat) :
    CollateralListStored (writeWord mem off word) writePtr limit cs := by
  induction cs generalizing writePtr with
  | nil => trivial
  | cons c cs ih =>
    rcases h with ⟨ptr, hwlo, hwlim, hwin, hw, hplo, hplim, hm, ht⟩
    refine ⟨ptr, hwlo, hwlim, by rw [writeWord_sparse_size]; omega, ?_, hplo, hplim,
      hm.writeWord word (Or.inr (by omega)), ?_⟩
    · rw [memLoad_writeWord_preserved _ _ _ _ hwin (Or.inr hbelow), hw]
    · exact ih ht (by
        rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
        omega)

theorem CollateralListStored.writeWords_below {mem : ByteArray} {writePtr : UInt256}
    {limit off : Nat} {cs : List CollateralData}
    (h : CollateralListStored mem writePtr limit cs) (words : List UInt256)
    (hlimit : limit < 2^64) (hbelow : off + 32 * words.length ≤ writePtr.toNat) :
    CollateralListStored (writeWordArray mem off words) writePtr limit cs := by
  induction words generalizing mem off with
  | nil => exact h
  | cons word words ih =>
    simp only [List.length_cons] at hbelow
    exact ih (h.writeWord_below word hlimit (by omega)) (by omega)

theorem collateralStepMemory_stored {mem : ByteArray} {ptr writePtr : UInt256}
    (c : CollateralData) (hfit : ptr.toNat + 128 < 2^64)
    (harray : writePtr.toNat + 32 ≤ ptr.toNat) :
    memLoad writePtr (collateralStepMemory mem ptr writePtr c) = ptr ∧
      MemoryWords (collateralStepMemory mem ptr writePtr c) ptr.toNat c.words := by
  refine ⟨memLoad_writeWord _ writePtr ptr, ?_⟩
  apply (MemoryWords.of_writeWordArray (writeWord mem 64 (ptr + UInt256.ofNat 128))
    ptr.toNat c.words (by
      change ptr.toNat + 32 * 4 < 2^256
      omega) (by simp [CollateralData.words])).writeWord _ (Or.inr harray)

theorem collateralLoopMemory_stored {mem : ByteArray} {ptr writePtr : UInt256}
    (cs : List CollateralData)
    (hfit : ptr.toNat + 128 * cs.length < 2^64)
    (harray : writePtr.toNat + 32 * cs.length ≤ ptr.toNat)
    (hwrite : 96 ≤ writePtr.toNat) :
    CollateralListStored (collateralLoopMemory mem ptr writePtr cs) writePtr
      (ptr.toNat + 128 * cs.length) cs := by
  induction cs generalizing mem ptr writePtr with
  | nil => trivial
  | cons c cs ih =>
    simp only [List.length_cons] at hfit harray
    have hptr : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hwp : (writePtr + UInt256.ofNat 32).toNat = writePtr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hf : (ptr + UInt256.ofNat 128).toNat + 128 * cs.length < 2^64 := by rw [hptr]; omega
    have ha : (writePtr + UInt256.ofNat 32).toNat + 32 * cs.length ≤
        (ptr + UInt256.ofNat 128).toNat := by rw [hptr, hwp]; omega
    have hw : 96 ≤ (writePtr + UInt256.ofNat 32).toNat := by rw [hwp]; omega
    have hs := collateralStepMemory_stored (mem := mem) (ptr := ptr) (writePtr := writePtr)
      c (by omega) (by omega)
    simp only [collateralLoopMemory, CollateralListStored]
    refine ⟨ptr, hwrite, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · have hs := collateralLoopMemory_size (mem := collateralStepMemory mem ptr writePtr c)
        (ptr := ptr + UInt256.ofNat 128) (writePtr := writePtr + UInt256.ofNat 32) cs
      simp only [collateralStepMemory, collateralCopyMemory, writeWord_sparse_size] at hs ⊢
      omega
    · rw [collateralLoopMemory_preserved cs hf ha hw hwrite (by
        simp only [collateralStepMemory, collateralCopyMemory, writeWord_sparse_size]
        omega) (by rw [hptr]; omega) (by rw [hwp]; omega), hs.1]
    · simp only [List.length_cons]; omega
    · apply hs.2.preserve (collateralLoopMemory_size cs)
      intro read hlo hhi
      have hin := hhi.trans hs.2.size
      change read.toNat + 32 ≤ ptr.toNat + 32 * 4 at hhi
      exact collateralLoopMemory_preserved cs hf ha hw (by omega) hin
        (by rw [hptr]; omega) (by rw [hwp]; omega)
    · have he : (ptr + UInt256.ofNat 128).toNat + 128 * cs.length =
          ptr.toNat + 128 * (c :: cs).length := by rw [hptr]; simp only [List.length_cons]; omega
      simpa only [he] using ih hf ha hw

end Benchmarks.Midnight
