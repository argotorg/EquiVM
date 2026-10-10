import Benchmarks.UniswapV3.Pool.UnsafeDivRoundSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool

theorem unsafeDivRoundWord (x y : UInt256) :
    UInt256.isZero (UInt256.isZero (UInt256.mod x y)) + UInt256.div x y =
      unsafeDivRoundResult x y := by
  by_cases hy : y.toNat = 0
  · have hw : y = UInt256.ofNat 0 := uint256_toNat_eq_zero hy
    have hr : UInt256.mod x y = UInt256.ofNat 0 := by rw [hw]; rfl
    rw [hr]
    apply u256_inj
    rw [uadd_toNat, udiv_toNat, unsafeDivRoundResult_toNat]
    simp only [unsafeDivRoundNat, hy, if_true, Nat.div_zero, Nat.add_zero]
    rfl
  · have hr := umod_toNat_of_ne_zero x y hy
    have hf : (UInt256.isZero (UInt256.isZero (UInt256.mod x y))).toNat =
        if x.toNat % y.toNat = 0 then 0 else 1 := by
      by_cases hz : x.toNat % y.toNat = 0
      · have hw : UInt256.mod x y = (⟨0⟩ : UInt256) := uint256_toNat_eq_zero (hr.trans hz)
        rw [hw, if_pos hz]
        rfl
      · have hw : UInt256.mod x y ≠ (⟨0⟩ : UInt256) := by
          intro he
          rw [he] at hr
          exact hz hr.symm
        rw [isZero_eq_zero_of_ne hw, if_neg hz]
        rfl
    have hb : unsafeDivRoundNat x y < UInt256.size :=
      lt_of_le_of_lt (unsafeDivRoundNat_le x y) x.val.isLt
    apply u256_inj
    rw [uadd_toNat, hf, udiv_toNat, unsafeDivRoundResult_toNat]
    simp only [unsafeDivRoundNat, if_neg hy] at hb ⊢
    rw [Nat.add_comm, Nat.mod_eq_of_lt hb]

theorem unsafeDivRoundX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret x y : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19703⟩ (y :: x :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (unsafeDivRoundResult x y :: R) mem aw rdata σ k' C' := by
  have rr := uniswapV3Pool_block_19703 (immWords := wordsOf (immStore v)) hov hret rd
  simp only [uniswapV3Pool_block_19703_stack, unsafeDivRoundWord] at rr
  exact ⟨_, _, rr⟩

end Benchmarks.UniswapV3.Pool
