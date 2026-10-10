import Benchmarks.CompoundIII.Comet.MemoryLoadPreservation
import Benchmarks.CompoundIII.Comet.ReentrancyMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_078
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

theorem absorbDebtEventMemory {mem : ByteArray} {free paid value : UInt256}
    (hf : memLoad ⟨64⟩ mem = free) (hb : free.toNat + 32 < UInt256.size) :
    cometWithExtendedAssetList_block_17410_taken_memory (mem := mem) (x0 := value) (x2 := paid) =
      pairEventMem mem free paid value := by
  have ha : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
    addWord_toNat free ⟨32⟩ hb
  simp only [cometWithExtendedAssetList_block_17410_taken_memory,
    show memLoad (UInt256.ofNat 64) mem = free from hf, pairEventMem, ha, Reasoning.Theory.writeWord]

theorem absorbDebtEventMemory_free {mem : ByteArray} {free paid value : UInt256}
    (hf : memLoad ⟨64⟩ mem = free) (hl : 96 ≤ free.toNat) (hm : free.toNat ≤ mem.size) :
    memLoad ⟨64⟩ (pairEventMem mem free paid value) = free ∧
      mem.size ≤ (pairEventMem mem free paid value).size := by
  have hsz := writeWord_sparse_size mem free.toNat paid
  constructor
  · rw [pairEventMem, memLoad_writeWord_preserved _ _ _ _ (by change 64 + 32 ≤ _; omega)
        (Or.inl (by change 64 + 32 ≤ _; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by change 64 + 32 ≤ _; omega)
        (Or.inl (by change 64 + 32 ≤ _; omega)), hf]
  · rw [pairEventMem, writeWord_sparse_size]; omega

theorem absorbTransferCopyMemory_free (v : CometWithExtendedAssetListImmutables)
    (mem : ByteArray) (hm : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (cometWithExtendedAssetList_block_17493_memory
      (immWords := wordsOf (immStore v)) (mem := mem)) = memLoad ⟨64⟩ mem ∧
    (cometWithExtendedAssetList_block_17493_memory
      (immWords := wordsOf (immStore v)) (mem := mem)).size = mem.size := by
  have hs : 18482 + 32 ≤ (deployedRuntime v).size := by rw [reentrancyCode_size]; decide
  have hsz := copyWindow_size (deployedRuntime v) mem 18482 0 32 (by decide) hs (by omega)
  change memLoad ⟨64⟩ (writeWord ((deployedRuntime v).write 18482 mem 0 32) 0
      (memLoad ⟨0⟩ mem)) = _ ∧ _
  constructor
  · rw [memLoad_writeWord_preserved _ _ _ _ (by change 64 + 32 ≤ _; omega)
        (Or.inr (by decide))]
    exact memLoad_copyWindow_preserved _ _ 18482 0 32 ⟨64⟩ (by decide) hs (by omega) hm
      (Or.inr (by decide))
  · change (writeWord ((deployedRuntime v).write 18482 mem 0 32) 0 _).size = _
    rw [writeWord_sparse_size, hsz]; omega

end Benchmarks.CompoundIII.Comet
