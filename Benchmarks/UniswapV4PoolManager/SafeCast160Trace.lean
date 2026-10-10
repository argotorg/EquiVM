import Benchmarks.UniswapV4PoolManager.SafeCast160Source
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_067
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem uintToUint160CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret w : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23963⟩ (w :: ret :: R) mem aw rdata σ k C) :
    if w.toNat < 2^160 then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (w :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : w.toNat < 2^160
  · rw [if_pos hfit]
    have hm := solcAddrMask_clean hfit
    have rd1 := poolManagerBlocks.poolManager_block_23963_fallthrough hstack
      (u256_sub_eq_zero_iff_eq.mpr hm) h
    have rd2 := poolManagerBlocks.poolManager_block_23995
      (by simp only [List.length_cons]; omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_23995_stack] at rd2
    change RD _ _ _ _ ret (UInt256.land w solcAddrMask :: R) mem aw rdata σ _ _ at rd2
    rw [hm] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · rw [if_neg hfit]
    have hm : UInt256.sub (UInt256.land w solcAddrMask) w ≠ ⟨0⟩ :=
      fun he => hfit ((landMask_eq_iff w solcAddrMask (bits := 160) rfl).mp
        (u256_sub_eq_zero_iff_eq.mp he))
    have rd1 := poolManagerBlocks.poolManager_block_23963_taken hstack hm
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+4 ≤ 1024; exact hstack) rd1

end Benchmarks.UniswapV4PoolManager
