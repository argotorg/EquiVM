import Benchmarks.CompoundIII.Comet.LiquidatorPointsMemory
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_075

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem liquidatorPointsLoad_memory (ee : ExecutionEnv) (σ : AccountMap)
    (mem : ByteArray) (ptr slot : UInt256) :
    cometWithExtendedAssetList_block_16582_memory
      (ee := ee) (σ := σ) (mem := mem) (x0 := ptr) (x2 := slot) =
    wordStructStore mem ptr 4
      (liquidatorPointsWords (liquidatorPointsData (solcSlotWordAt slot σ ee))) := by
  rw [wordStructStore_succ, wordStructStore_succ, wordStructStore_succ,
    wordStructStore_succ, wordStructStore_zero]
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right, liquidatorPointsWords, liquidatorPointsData]
  obtain ⟨h0, h1, h2, h3⟩ := liquidatorFieldWords (solcSlotWordAt slot σ ee)
  rw [h0, h1, h2, h3]
  simp only [cometWithExtendedAssetList_block_16582_memory, Reasoning.Theory.writeWord,
    u256_land_comm]
  rfl

theorem cometAllocateLiquidatorPoints {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr slot ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hb : ptr.toNat + 128 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16567⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      LiquidatorPointsMemory (liquidatorPointsAllocatedMemory mem ptr (solcSlotWordAt slot σ ee))
        ptr (liquidatorPointsData (solcSlotWordAt slot σ ee)) ∧
      RD (deployedRuntime v) ee g s0 ret (ptr :: R)
        (liquidatorPointsAllocatedMemory mem ptr (solcSlotWordAt slot σ ee)) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_16567
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_16567_stack, hfree] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocateBounded (v := v) (bound := 4)
    (by change R.length + 3 + 6 ≤ 1024; omega) (by decide) hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_16582
    (immWords := wordsOf (immStore v)) (by omega) hret r2
  rw [liquidatorPointsLoad_memory] at r3
  refine ⟨_, k3, C3, ?_, r3⟩
  exact liquidatorPointsAllocatedMemory_correct _ _ _ (by
    change ptr.toNat + 128 < 2^256; omega)

end Benchmarks.CompoundIII.Comet
