import Benchmarks.Morpho.MorphoBlue.AccrueHeap
import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a write in reserved memory preserves the cursor and allocated prefix.
theorem MorphoHeap.writeAbove {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (off : Nat) (value : UInt256)
    (hlo : fp.toNat ≤ off) (hhi : off ≤ fp.toNat + spare) :
    MorphoHeap (writeWord mem off value) fp spare ∧ MemoryPrefix mem (writeWord mem off value) fp.toNat := by
  have hg : off - mem.size < USize.size := by have hh := hm.gap; omega
  have hs : (writeWord mem off value).size = max mem.size (off + 32) := writeWord_size _ _ _ hg
  refine ⟨⟨?_, ?_, hm.lower, ?_, hm.space⟩, memoryPrefix_writeWord _ _ _ _ hg (.inl hlo)⟩
  · rw [hs]; have hh := hm.size; omega
  · rw [memLoad_writeWord_disjoint mem off value (UInt256.ofNat 64) hg hm.size (Or.inl (by change 96 ≤ off; have hh := hm.lower; omega))]
    exact hm.free
  · rw [hs]; have hh := hm.gap; omega

def twoWordEventMem (mem : ByteArray) (fp x y : UInt256) : ByteArray :=
  writeWord (writeWord mem fp.toNat x) (fp + UInt256.ofNat 32).toNat y

theorem MorphoHeap.twoWordEvent {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (hb : 32 ≤ spare) (x y : UInt256) :
    MorphoHeap (twoWordEventMem mem fp x y) fp spare ∧ MemoryPrefix mem (twoWordEventMem mem fp x y) fp.toNat := by
  obtain ⟨hm1, hp1⟩ := hm.writeAbove fp.toNat x (le_refl _) (by omega)
  have hadd : (fp + UInt256.ofNat 32).toNat = fp.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by have hh := hm.space; change _ < 2 ^ 256; omega)
  obtain ⟨hm2, hp2⟩ := hm1.writeAbove (fp + UInt256.ofNat 32).toNat y (by omega) (by omega)
  exact ⟨hm2, hp1.trans hp2⟩

end Benchmarks.Morpho.MorphoBlue
