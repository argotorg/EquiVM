import Benchmarks.UniswapV4PoolManager.PoolSwapLoopCondition
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapConditionAW (aw state params remaining : UInt256) : UInt256 :=
  if remaining = ⟨0⟩ then aw else M (M aw state ⟨32⟩) (params+UInt256.ofNat 96) ⟨32⟩

theorem poolSwapLoopConditionTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {p : PoolSwapParamsWords} {q : PoolSwapLoopWords}
    {aw step state params id tag x1 fee protocol : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hm : PoolSwapMemoryView mem step state params q.step q.result p)
    (hprice : q.result.price.toNat < 2^160) (hlimit : p.priceLimit.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨19155⟩
      (poolSwapLoopStack q p id step state params x1 tag fee protocol R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if poolSwapLoopContinues p q then ⟨19169⟩ else ⟨21536⟩)
      (poolSwapLoopStack q p id step state params x1 tag fee protocol R)
      mem (poolSwapConditionAW aw state params q.remaining) rdata σ k' C' := by
  by_cases hz : q.remaining = ⟨0⟩
  · have hstop : ¬poolSwapLoopContinues p q := fun hh => hh.1 hz
    rw [if_neg hstop, poolSwapConditionAW, if_pos hz]
    have hzero : UInt256.isZero q.remaining = ⟨1⟩ := by rw [hz]; rfl
    have rd1 := poolManagerBlocks.poolManager_block_19155_fallthrough
      (by change R.length+11+4 ≤ 1024; omega) (by rw [hzero]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_19155_fallthrough_stack, hzero] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_19164_taken
      (by change R.length+12+2 ≤ 1024; omega) (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_19164_taken_stack] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · have hzero : UInt256.isZero q.remaining = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have rd1 := poolManagerBlocks.poolManager_block_19155_taken
      (by change R.length+11+4 ≤ 1024; omega) (by rw [hzero]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19155_taken_stack] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_21882 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hcp := solcAddrMask_clean hprice
    have hcl := solcAddrMask_clean hlimit
    change UInt256.land q.result.price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = q.result.price at hcp
    change UInt256.land p.priceLimit (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = p.priceLimit at hcl
    simp only [poolManagerBlocks.poolManager_block_21882_stack, hm.price, hm.limit, hcp, hcl] at rd2
    by_cases hp : q.result.price = p.priceLimit
    · have hstop : ¬poolSwapLoopContinues p q := fun hh => hh.2 hp
      rw [if_neg hstop, poolSwapConditionAW, if_neg hz]
      have heq : UInt256.eq p.priceLimit q.result.price = ⟨1⟩ := by rw [hp, uInt256_eq_self]
      rw [heq] at rd2
      have rd3 := poolManagerBlocks.poolManager_block_19164_taken
        (by change R.length+12+2 ≤ 1024; omega) (by decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      simp only [poolManagerBlocks.poolManager_block_19164_taken_stack] at rd3
      exact ⟨_, _, by omega, rd3⟩
    · have hgo : poolSwapLoopContinues p q := ⟨hz, hp⟩
      rw [if_pos hgo, poolSwapConditionAW, if_neg hz]
      have heq : UInt256.eq p.priceLimit q.result.price = ⟨0⟩ :=
        uInt256_eq_zero_of_ne (fun he => hp (uInt256_eq_one_eq he).symm)
      rw [heq] at rd2
      have rd3 := poolManagerBlocks.poolManager_block_19164_fallthrough
        (by change R.length+12+2 ≤ 1024; omega) rfl rd2
      simp only [poolManagerBlocks.poolManager_block_19164_fallthrough_stack] at rd3
      exact ⟨_, _, by omega, rd3⟩

end Benchmarks.UniswapV4PoolManager
