import Benchmarks.UniswapV4PoolManager.NextAmount0RoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount0SubRoundTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw n product price ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23782⟩ (n :: product :: price :: ret :: R) mem aw rdata σ k C) :
    (nextAmount0RoundFits n price (UInt256.sub n product) true → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret
        (nextAmount0RoundWord n price (UInt256.sub n product) true :: R) mem aw rdata σ k' C') ∧
    (¬nextAmount0RoundFits n price (UInt256.sub n product) true → RDrev (deployedRuntime v) g s0) := by
  have rd1 := poolManagerBlocks.poolManager_block_23782 (by change R.length+7 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := nextAmount0RoundTrace (n := n) (price := price) (d := UInt256.sub n product)
    (ret := ret) (R := R) v true hstack hret rd1
  constructor
  · intro hf
    rw [if_pos hf] at hr
    obtain ⟨k2, C2, hC2, rd2⟩ := hr
    exact ⟨k2, C2, by omega, rd2⟩
  · intro hf
    rw [if_neg hf] at hr
    exact hr

theorem nextAmount0SubTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23697⟩ (price :: liquidity :: amount :: ret :: R) mem aw rdata σ k C) :
    if nextAmount0Fits price liquidity amount false then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (nextAmount0Word price liquidity amount false :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hpc : UInt256.land price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price :=
    solcAddrMask_clean hp
  have hnc := amount0Numerator1_clean hl
  by_cases hz : amount = ⟨0⟩
  · simp only [nextAmount0Fits, hz, true_or, if_true, nextAmount0Word]
    have rd1 := poolManagerBlocks.poolManager_block_23697_taken (by change R.length+6 ≤ 1024; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_23810 (by change R.length+4 ≤ 1024; omega) hret rd1
    exact ⟨_, _, by omega, rd2⟩
  · simp only [nextAmount0Fits, hz, false_or, nextAmount0Word, if_false]
    have rd1 := poolManagerBlocks.poolManager_block_23697_fallthrough
      (by change R.length+6 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) h
    by_cases hg : nextAmount0SubGuard price liquidity amount
    · have htest : UInt256.isZero (UInt256.land
          (UInt256.eq (UInt256.div (nextAmount0Product price amount) amount) price)
          (UInt256.gt (amount0Numerator1 liquidity) (nextAmount0Product price amount))) = ⟨0⟩ := by
        rw [hg.1, uInt256_eq_self, ugt_one hg.2]
        rfl
      have rd2 := poolManagerBlocks.poolManager_block_23706_fallthrough
        (x0 := liquidity) (x1 := amount) (x2 := price) (R := ret :: R)
        (by change R.length+8 ≤ 1024; omega)
        (by rw [hpc, hnc]; exact htest) rd1
      simp only [poolManagerBlocks.poolManager_block_23706_fallthrough_stack,
        hpc, hnc] at rd2
      rw [← nextAmount0Product] at rd2
      have hr := nextAmount0SubRoundTrace (n := amount0Numerator1 liquidity) (price := price)
        (product := nextAmount0Product price amount) (ret := ret) (R := R) v hstack hret rd2
      by_cases hf : nextAmount0RoundFits (amount0Numerator1 liquidity) price
          (UInt256.sub (amount0Numerator1 liquidity) (nextAmount0Product price amount)) true
      · have hcore : nextAmount0CoreFits price liquidity amount false := ⟨hg, hf⟩
        rw [if_pos hcore]
        simp only [nextAmount0CoreWord, Bool.false_eq_true, if_false]
        obtain ⟨k4, C4, hC4, rd4⟩ := hr.1 hf
        exact ⟨k4, C4, by omega, rd4⟩
      · have hcore : ¬nextAmount0CoreFits price liquidity amount false := fun hh => hf hh.2
        rw [if_neg hcore]
        exact hr.2 hf
    · have htest : UInt256.isZero (UInt256.land
          (UInt256.eq (UInt256.div (nextAmount0Product price amount) amount) price)
          (UInt256.gt (amount0Numerator1 liquidity) (nextAmount0Product price amount))) ≠ ⟨0⟩ := by
        by_cases heq : UInt256.div (nextAmount0Product price amount) amount = price
        · have hle : (amount0Numerator1 liquidity).toNat ≤ (nextAmount0Product price amount).toNat :=
            Nat.le_of_not_gt (fun hh => hg ⟨heq, hh⟩)
          rw [heq, uInt256_eq_self, ugt_zero hle]
          decide
        · have he : UInt256.eq (UInt256.div (nextAmount0Product price amount) amount) price = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun hh => heq (uInt256_eq_one_eq hh))
          rw [he, u256_land_zero_left]
          decide
      have rd2 := poolManagerBlocks.poolManager_block_23706_taken
        (x0 := liquidity) (x1 := amount) (x2 := price) (R := ret :: R)
        (by change R.length+8 ≤ 1024; omega)
        (by rw [hpc, hnc]; exact htest)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      simp only [nextAmount0CoreFits, Bool.false_eq_true, if_false, hg, false_and]
      exact poolManagerBlocks.poolManager_block_23797 (by change R.length+6 ≤ 1024; omega) rd2

end Benchmarks.UniswapV4PoolManager
