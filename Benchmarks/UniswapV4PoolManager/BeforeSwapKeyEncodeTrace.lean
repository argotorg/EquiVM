import Benchmarks.UniswapV4PoolManager.BeforeSwapKeyEncodeMemory
import Benchmarks.UniswapV4PoolManager.NatSubBounds
import Benchmarks.UniswapV4PoolManager.EntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeSwapKeyEncodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len hook : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15230⟩
      (src :: len :: paramsPtr :: hook :: keyPtr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', C+229+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨15382⟩
      (paramsPtr :: UInt256.ofNat 15436 :: len :: src :: UInt256.ofNat 14575 :: free ::
        UInt256.ofNat 15456 :: free :: UInt256.ofNat 15462 :: hook :: keyPtr :: R)
      (wordCallMemory mem (free.toNat+32) beforeSwapSelectorWord (accountWord I.source :: poolKeyWordList key))
      aw' rdata σ k' C' := by
  have hm1 : poolManager_block_15230_memory (ee := I) (mem := mem) (x4 := keyPtr) =
      beforeSwapKeyPrefixMemory mem free keyPtr (accountWord I.source) := by
    simp only [poolManager_block_15230_memory, hfree]
    rfl
  have hs1 : poolManager_block_15230_stack (ee := I) (mem := mem) (x0 := src) (x1 := len)
      (x2 := paramsPtr) (x3 := hook) (x4 := keyPtr) (R := R) =
      UInt256.signextend ⟨2⟩ (memLoad (keyPtr+UInt256.ofNat 96)
        (beforeSwapKeyPrefixMemory mem free keyPtr (accountWord I.source))) ::
      keyPtr :: UInt256.ofNat 128 :: solcAddrMask :: UInt256.ofNat 128 ::
      (free+UInt256.ofNat 68) :: UInt256.ofNat 15382 :: paramsPtr :: UInt256.ofNat 15436 :: len :: src ::
      UInt256.ofNat 14575 :: free :: UInt256.ofNat 15456 :: free :: UInt256.ofNat 15462 :: hook :: keyPtr :: R := by
    simp only [poolManager_block_15230_stack, hfree]
    rfl
  have rd1 := poolManager_block_15230 hstack h
  rw [hm1, hs1] at rd1
  have rd2 := poolManager_block_15370 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hm2 := beforeSwapKeyEncodeMemory (sender := accountWord I.source) hk hc hb hf
  rw [poolManager_block_15370_stack, hm2] at rd2
  refine ⟨_, _, _, ?_, rd2⟩
  dsimp only [memExpansionCost]
  rw [hfree]
  nat_sub_bounds
  omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
