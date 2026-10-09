import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a sequence of reserved writes preserves the heap and earlier memory.
theorem MorphoHeap.wordWrites {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (ws : List UInt256) (off : Nat)
    (hlo : fp.toNat ≤ off) (hhi : off + 32 * ws.length ≤ fp.toNat + spare) :
    MorphoHeap (writeCascade mem (returnWordWrites off ws)) fp spare ∧
      MemoryPrefix mem (writeCascade mem (returnWordWrites off ws)) fp.toNat := by
  induction ws generalizing mem off with
  | nil => exact ⟨hm, .refl _ _⟩
  | cons w ws ih =>
    have hhi' : off + 32 * (ws.length + 1) ≤ fp.toNat + spare := hhi
    obtain ⟨hm1, hp1⟩ := hm.writeAbove off w hlo (by omega)
    obtain ⟨hm2, hp2⟩ := ih hm1 (off + 32) (by omega) (by omega)
    exact ⟨hm2, hp1.trans hp2⟩

end Benchmarks.Morpho.MorphoBlue
