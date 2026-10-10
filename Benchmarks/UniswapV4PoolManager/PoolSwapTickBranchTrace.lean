import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapTickBranchAW (aw step state : UInt256) : UInt256 :=
  M (M aw state ⟨32⟩) (step+UInt256.ofNat 96) ⟨32⟩

theorem poolSwapTickBranchTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw step state price next x0 tag x1 params remaining calculated fee protocol amount dir pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hpc : price.toNat < 2^160) (hnc : next.toNat < 2^160)
    (hp : memLoad state mem = price) (hn : memLoad (step+UInt256.ofNat 96) mem = next)
    (h : RD (deployedRuntime v) I g s0 ⟨19833⟩
      ([x0, tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 (if price = next then ⟨19894⟩ else ⟨20162⟩)
      ([price, tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
      mem (poolSwapTickBranchAW aw step state) rdata σ k' C' := by
  have hpm : UInt256.land price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price :=
    u256LandMaskCleanOfToNat _ _ rfl hpc
  have hnm : UInt256.land next (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = next :=
    u256LandMaskCleanOfToNat _ _ rfl hnc
  by_cases he : price = next
  · rw [if_pos he]
    have rd := poolManagerBlocks.poolManager_block_19833_fallthrough hstack
      (by rw [hp, hn, hpm, hnm, he, uInt256_eq_self]; decide) h
    simp only [poolManagerBlocks.poolManager_block_19833_fallthrough_stack, hp, hpm] at rd
    exact ⟨_, _, by omega, rd⟩
  · rw [if_neg he]
    have he0 : UInt256.eq price next = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun hone => he (uInt256_eq_one_eq hone))
    have rd := poolManagerBlocks.poolManager_block_19833_taken hstack
      (by rw [hp, hn, hpm, hnm, he0]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19833_taken_stack, hp, hpm] at rd
    exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
