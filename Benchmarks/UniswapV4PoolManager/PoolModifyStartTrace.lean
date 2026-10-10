import Benchmarks.UniswapV4PoolManager.Allocate128Trace
import Benchmarks.UniswapV4PoolManager.PoolModifyStateMemory
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyAllocateCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr x0 x1 x2 : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hp : memLoad (UInt256.ofNat 64) mem = ptr) (hf : ptr.toNat+128 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨5680⟩ (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', Cₘ aw'+C ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨5692⟩ (x2 :: x0 :: x1 :: ptr :: R)
      (writeWord mem 64 (ptr+⟨128⟩)) aw' rdata σ k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_5680 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_5680_stack, hp] at rd1
  have rd2 := allocate128CostTrace v (by simp only [List.length_cons]; omega) hf
    (by rw [deployedRuntime_jumps]; jump_dest) rd1
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  omega

theorem poolModifyAllocateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr x0 x1 x2 : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hp : memLoad (UInt256.ofNat 64) mem = ptr) (hf : ptr.toNat+128 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨5680⟩ (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5692⟩ (x2 :: x0 :: x1 :: ptr :: R)
      (writeWord mem 64 (ptr+⟨128⟩)) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, rd⟩ := poolModifyAllocateCostTrace v hstack hp hf h
  exact ⟨aw', k', C', rd⟩

theorem poolModifyInitialMemory_eq (mem : ByteArray) (ptr : UInt256)
    (hf : ptr.toNat+128 < UInt256.size) :
    poolManagerBlocks.poolManager_block_5692_taken_memory (mem := mem) (x3 := ptr) =
      poolModifyStateMemory mem ptr := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  simp only [poolManagerBlocks.poolManager_block_5692_taken_memory, poolModifyStateMemory,
    wordSequenceMemory, Reasoning.Theory.writeWord, h32, h64, h96, Nat.add_assoc]

theorem poolModifyInitialCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr x0 x1 x2 x4 x5 upper lower : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hf : ptr.toNat+128 < UInt256.size) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨5692⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', Cₘ aw'+C ≤ C'+Cₘ aw ∧ ptr.toNat+128 ≤ aw'.toNat*32 ∧ RD (deployedRuntime v) I g s0 (if delta ≠ 0 then ⟨6949⟩ else ⟨5722⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      (poolModifyStateMemory mem ptr) aw' rdata σ k' C' := by
  have hc : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  have he := poolModifyInitialMemory_eq mem ptr hf
  by_cases hz : delta ≠ 0
  · rw [if_pos hz]
    have rd1 := poolManagerBlocks.poolManager_block_5692_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hc]; exact fun hh => hz ((wordOfInt_eq_zero_iff (signedFits128_int256 hd)).mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨_, _, _, ?_, ?_, he ▸ rd1⟩
    · dsimp only [memExpansionCost]; omega
    · have h96 := uadd_word_ofNat_toNat ptr 96 (by omega)
      have hspan := memoryWords_ge_span
        (M (M (M aw ptr ⟨32⟩) (ptr+UInt256.ofNat 32) ⟨32⟩) (ptr+UInt256.ofNat 64) ⟨32⟩)
        (ptr+UInt256.ofNat 96) ⟨32⟩ (by decide)
      change ((ptr+UInt256.ofNat 96).toNat+32+31)/32 ≤ _ at hspan
      rw [h96] at hspan
      omega
  · rw [if_neg hz]
    have rd1 := poolManagerBlocks.poolManager_block_5692_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [hc]; exact (wordOfInt_eq_zero_iff (signedFits128_int256 hd)).mpr (by omega)) h
    have he' : poolManagerBlocks.poolManager_block_5692_fallthrough_memory (mem := mem) (x3 := ptr) =
        poolModifyStateMemory mem ptr := he
    refine ⟨_, _, _, ?_, ?_, he' ▸ rd1⟩
    · dsimp only [memExpansionCost]; omega
    · have h96 := uadd_word_ofNat_toNat ptr 96 (by omega)
      have hspan := memoryWords_ge_span
        (M (M (M aw ptr ⟨32⟩) (ptr+UInt256.ofNat 32) ⟨32⟩) (ptr+UInt256.ofNat 64) ⟨32⟩)
        (ptr+UInt256.ofNat 96) ⟨32⟩ (by decide)
      change ((ptr+UInt256.ofNat 96).toNat+32+31)/32 ≤ _ at hspan
      rw [h96] at hspan
      omega

theorem poolModifyInitialTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr x0 x1 x2 x4 x5 upper lower : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hf : ptr.toNat+128 < UInt256.size) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨5692⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (if delta ≠ 0 then ⟨6949⟩ else ⟨5722⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      (poolModifyStateMemory mem ptr) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, _, rd⟩ := poolModifyInitialCostTrace v hstack hf hd h
  exact ⟨aw', k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
