import Benchmarks.UniswapV4PoolManager.DonateEventMemory
import Benchmarks.UniswapV4PoolManager.NatSubBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateEventTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {mem rdata : ByteArray} {aw free id keyPtr src amount0 amount1 len delta junk : UInt256}
    {hook : AccountAddress} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hw : accountWord hook = key.hooks)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+32 < UInt256.size)
    (hperm : I.perm = true) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10297⟩
      (id :: (keyPtr+UInt256.ofNat 128) :: keyPtr :: src :: amount1 :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 (if I.source = hook then ⟨10381⟩ else ⟨10391⟩)
        (accountWord hook :: amount1 :: keyPtr :: src :: accountWord hook :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
        (donateEventMemory mem free amount0 amount1) aw' rdata σ k' C' := by
  have hm : poolManagerBlocks.poolManager_block_10297_taken_memory
      (mem := mem) (x4 := amount1) (x5 := amount0) (x8 := ⟨32⟩) = donateEventMemory mem free amount0 amount1 :=
    donateEventMemory_compiled hf hfree
  have hkey := hk.donateEvent free amount0 amount1 hb
  have hload : memLoad (keyPtr+UInt256.ofNat 128)
      (amount1.toByteArray.write 0 (amount0.toByteArray.write 0 mem
        (memLoad (UInt256.ofNat 64) mem).toNat 32)
        ((memLoad (UInt256.ofNat 64) mem)+(⟨32⟩ : UInt256)).toNat 32) = accountWord hook := by
    change memLoad _ (poolManagerBlocks.poolManager_block_10297_taken_memory
      (mem := mem) (x4 := amount1) (x5 := amount0) (x8 := ⟨32⟩)) = _
    rw [hm, hkey.load (i := 4) rfl, ← hw]
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  by_cases hself : I.source = hook
  · rw [if_pos hself]
    have rd := poolManagerBlocks.poolManager_block_10297_fallthrough
      (by simp only [List.length_cons]; omega) hperm
      (by rw [hload, hclean]; change UInt256.sub (accountWord I.source) (accountWord hook) = ⟨0⟩
          exact u256_sub_eq_zero_iff_eq.mpr (heq.mp hself)) h
    have hm' : poolManagerBlocks.poolManager_block_10297_fallthrough_memory
        (mem := mem) (x4 := amount1) (x5 := amount0) (x8 := ⟨32⟩) = _ := hm
    simp only [poolManagerBlocks.poolManager_block_10297_fallthrough_stack, hload, hclean, hm'] at rd
    refine ⟨_, _, _, ?_, rd⟩
    dsimp only [memExpansionCost]
    nat_sub_bounds
    omega -splitNatSub
  · rw [if_neg hself]
    have rd := poolManagerBlocks.poolManager_block_10297_taken
      (by simp only [List.length_cons]; omega) hperm
      (by rw [hload, hclean]; change UInt256.sub (accountWord I.source) (accountWord hook) ≠ ⟨0⟩
          exact fun he => hself (heq.mpr (u256_sub_eq_zero_iff_eq.mp he)))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_10297_taken_stack, hload, hclean, hm] at rd
    refine ⟨_, _, _, ?_, rd⟩
    dsimp only [memExpansionCost]
    nat_sub_bounds
    omega -splitNatSub

end Benchmarks.UniswapV4PoolManager
