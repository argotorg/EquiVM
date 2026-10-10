import Benchmarks.UniswapV4PoolManager.AllocationCostTrace
import Benchmarks.UniswapV4PoolManager.BytesReturnHeadTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

abbrev unlockRawEnd (out : ByteArray) : UInt256 := allocationEnd ⟨160⟩ (UInt256.ofNat out.size)
abbrev unlockReturnLength (out : ByteArray) : UInt256 := calldataWord out (calldataWord out 0).toNat

/-- Copy and inspect a callback reply, retaining the first allocation's failure and all gas costs. -/
theorem unlockReturnPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw saved : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hout : out.size < 2^138) (hmem : 160 ≤ mem.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9242⟩ (⟨160⟩ :: saved :: R) mem aw out σ k C) :
    (¬AllocationBounds ⟨160⟩ (UInt256.ofNat out.size) ∧ ∃ k' C',
      C+98+3*((out.size+31)/32)+Cₘ (M aw ⟨160⟩ (UInt256.ofNat out.size)) ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨7857⟩
        (unlockRawEnd out :: ⟨9259⟩ :: UInt256.ofNat out.size :: ⟨160⟩ :: R)
        (out.write 0 mem 160 out.size) (M aw ⟨160⟩ (UInt256.ofNat out.size)) out σ k' C') ∨
    (¬BytesReturnBounds out ∧ RDrev (deployedRuntime v) g s0) ∨
    (AllocationBounds ⟨160⟩ (UInt256.ofNat out.size) ∧ BytesReturnHeadBounds out ∧ ∃ aw' k' C',
      C+293+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat ≤ aw'.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨11822⟩
        (unlockRawEnd out :: bytesAllocationSize (unlockReturnLength out) :: ⟨9374⟩ ::
          (⟨160⟩+UInt256.ofNat out.size) :: (⟨160⟩+calldataWord out 0) ::
          unlockReturnLength out :: unlockRawEnd out :: R)
        (copiedReturnMemory out mem 160 (unlockRawEnd out)) aw' out σ k' C') := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have rd1 := poolManager_block_9242 (by omega)
    (by change 0+(UInt256.ofNat out.size).toNat ≤ out.size; rw [ho]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [poolManager_block_9242_stack, poolManager_block_9242_memory] at rd1
  rw [ho] at rd1
  rcases allocateCheckedTrace v (by simp only [List.length_cons]; omega)
      (by rw [deployedRuntime_jumps]; jump_dest) rd1 with ⟨hbad, rd⟩ | ⟨hb, rd2⟩
  · refine .inl ⟨hbad, _, _, ?_, rd⟩
    dsimp only [memExpansionCost]
    omega
  · change RD _ _ _ _ ⟨9259⟩ (UInt256.ofNat out.size :: ⟨160⟩ :: R)
      (copiedReturnMemory out mem 160 (unlockRawEnd out)) _ _ _ _ _ at rd2
    rcases bytesReturnHeadTrace (ptr := ⟨160⟩) (mem := mem) v (by omega) hout (by decide) (by decide) hmem rd2 with
      ⟨hbad, hr⟩ | ⟨hh, aw', k', C', hc, ha, rd3⟩
    · exact .inr (.inl ⟨hbad, hr⟩)
    · have rd4 := poolManager_block_9321 hstack
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      dsimp only [poolManager_block_9321_stack] at rd4
      have hf : memLoad (UInt256.ofNat 64) (copiedReturnMemory out mem (⟨160⟩ : UInt256).toNat (unlockRawEnd out)) =
          unlockRawEnd out := copiedReturnMemory_free _ _ _ _
      rw [hf] at rd4
      refine .inr (.inr ⟨hb, hh, _, _, _, ?_, ?_, rd4⟩)
      · dsimp only [memExpansionCost] at hc ⊢
        omega
      · exact (memoryWords_ge_active _ _ _).trans (ha.trans (memoryWords_ge_active _ _ _))

end Benchmarks.UniswapV4PoolManager
