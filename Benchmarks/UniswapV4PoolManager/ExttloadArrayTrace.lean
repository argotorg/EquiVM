import Benchmarks.UniswapV4PoolManager.ExttloadArrayLoop
import Benchmarks.UniswapV4PoolManager.WordArrayTraceLoop
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_009
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

def exttloadTraceValue (I : ExecutionEnv) (σ : AccountMap) (i : Nat) : UInt256 :=
  codeOwnerTransientWord I σ (wordArraySlot I i)

abbrev exttloadArrayStack := wordArrayTraceStack
abbrev exttloadArrayExitStack := wordArrayTraceExitStack

theorem exttloadArrayTraceStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n i : Nat} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : n ≤ solcMaxU64)
    (ho : (calldataWord I.calldata 4).toNat ≤ solcMaxU64) (hi : i ≤ n)
    (h : RD (deployedRuntime v) I g s0 ⟨2914⟩ (exttloadArrayStack I n i R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if i+1 < n then ⟨2914⟩ else ⟨2508⟩)
      (if i+1 < n then exttloadArrayStack I n (i+1) R else exttloadArrayExitStack I n (i+1) R)
      (writeWord mem (224+32*i) (exttloadTraceValue I σ i)) aw' rdata σ k' C' := by
  have houtfit : 224+32*(i+1) < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have hendfit : 224+32*n < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
  have hcdfit : 36 + (calldataWord I.calldata 4).toNat + 32*i < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hn ho ⊢; omega
  have houtadd := wordArrayStepWord 224 i
  have hcdadd := wordArrayStepWord (36 + (calldataWord I.calldata 4).toNat) i
  have hmemory : poolManagerBlocks.poolManager_block_2914_taken_memory (ee := I) (σ := σ)
      (mem := mem) (x0 := UInt256.ofNat (224+32*i))
      (x3 := UInt256.ofNat (36 + (calldataWord I.calldata 4).toNat + 32*i)) =
      writeWord mem (224+32*i) (exttloadTraceValue I σ i) := by
    change (codeOwnerTransientWord I σ (calldataWord I.calldata
      (UInt256.ofNat (36 + (calldataWord I.calldata 4).toNat + 32*i)).toNat)).toByteArray.write 0 mem
      (UInt256.ofNat (224+32*i)).toNat 32 = _
    rw [UInt256.toNat_ofNat_of_lt hcdfit, UInt256.toNat_ofNat_of_lt (by omega : 224+32*i < UInt256.size)]
    have he : 36 + (calldataWord I.calldata 4).toNat + 32*i =
        4 + (calldataWord I.calldata 4).toNat + 32 + 32*i := by omega
    rw [he]; rfl
  unfold exttloadArrayStack wordArrayTraceStack wordReadTraceStack wordArrayTraceCursor at h
  by_cases hnext : i+1 < n
  · simp only [if_pos hnext]
    obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_2914_fallthrough_packed hstack
      (by rw [houtadd, ult_one (by rw [UInt256.toNat_ofNat_of_lt houtfit,
        UInt256.toNat_ofNat_of_lt hendfit]; omega)]; rfl) h
    change RD _ _ _ _ ⟨2933⟩
      (UInt256.ofNat 160 :: (UInt256.ofNat (224+32*i) + UInt256.ofNat 32) ::
        (UInt256.ofNat (36 + (calldataWord I.calldata 4).toNat + 32*i) + UInt256.ofNat 32) ::
        UInt256.ofNat (224+32*n) :: UInt256.ofNat (160+32*n) :: UInt256.ofNat 160 :: R)
      (poolManagerBlocks.poolManager_block_2914_taken_memory (ee := I) (σ := σ) (mem := mem)
        (x0 := UInt256.ofNat (224+32*i)) (x3 := UInt256.ofNat (36 + (calldataWord I.calldata 4).toNat + 32*i)))
      _ _ _ _ _ at rd
    rw [houtadd, hcdadd, hmemory] at rd
    obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_2933_packed
      (by simp; omega) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw2, k2, C2, rd2⟩
  · simp only [if_neg hnext]
    obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_2914_taken_packed hstack
      (by rw [houtadd, ult_zero (by rw [UInt256.toNat_ofNat_of_lt houtfit,
        UInt256.toNat_ofNat_of_lt hendfit]; omega)]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [poolManagerBlocks.poolManager_block_2914_taken_stack, houtadd, hcdadd,
      hmemory, exttloadArrayExitStack, wordArrayTraceExitStack, wordReadTraceExitStack, wordArrayTraceCursor] using rd

/-- The positive-length loop writes exactly the requested consecutive words. -/
theorem exttloadArrayTraceLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {σ : AccountMap} {R : List UInt256} {n : Nat}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024)
    (hn : n ≤ solcMaxU64) (ho : (calldataWord I.calldata 4).toNat ≤ solcMaxU64)
    (remaining : Nat) :
    ∀ i mem aw k C, i + remaining + 1 = n →
      RD (deployedRuntime v) I g s0 ⟨2914⟩ (exttloadArrayStack I n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2508⟩ (exttloadArrayExitStack I n n R)
        (wordSequenceMemory mem (224+32*i) (wordArrayWords (exttloadTraceValue I σ) i (remaining+1)))
        aw' rdata σ k' C' := by
  exact wordArrayTraceLoop
    (fun _ _ _ _ _ hi h => exttloadArrayTraceStep v hstack hn ho hi h) remaining

end Benchmarks.UniswapV4PoolManager
