import Benchmarks.UniswapV3.Pool.TickLogChooseTrace
import Benchmarks.UniswapV3.Pool.TickSqrtTrace
import Benchmarks.UniswapV3.Pool.TickLogStartTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickLogCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw log x4 x5 x6 x7 price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14740⟩
      (tickLogBoundsStack log (x4 :: x5 :: x6 :: x7 :: price :: R)) mem aw rdata σ k C)
    (he : tickLogLow log ≠ tickLogHigh log) (hov : R.length + 19 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ tickLogSafe log) ∨
      (tickLogSafe log ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14788⟩
        (tickLogChoiceRaw log (tickLogPrice price) ::
          tickLogBoundsStack log (x4 :: x5 :: x6 :: x7 :: price :: R))
        mem aw rdata σ k' C') := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  have hprice : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) price = tickLogPrice price := by
    rw [u256_land_comm]
    rfl
  unfold tickLogBoundsStack at rd
  have hjCall : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11629) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]
    native_decide
  have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 14758) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]
    native_decide
  have rcall := uniswapV3Pool_block_14740 (immWords := wordsOf (immStore v))
    (by evm_ov) hjCall rd
  simp only [uniswapV3Pool_block_14740_stack, hmask, hprice] at rcall
  rcases tickSqrtX (v := v) rcall hjReturn
      (by simp only [List.length_cons]; omega) with ⟨rrev, hv⟩ | ⟨hv, k', C', rout⟩
  · exact Or.inl ⟨rrev, fun hs ↦ hs.elim he hv⟩
  · change RD _ _ _ _ _ (tickSqrtRaw (tickLogHigh log) :: _) _ _ _ _ _ _ at rout
    obtain ⟨k'', C'', rchosen⟩ := tickLogChooseX rout he (by simp only [List.length_cons]; omega)
    exact Or.inr ⟨Or.inr hv, k'', C'', rchosen⟩

theorem tickLogReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw log price x4 x5 x6 x7 original ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14788⟩
      (tickLogChoiceRaw log price ::
        tickLogBoundsStack log (x4 :: x5 :: x6 :: x7 :: original :: ret :: R))
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (tickLogChoiceRaw log price :: R)
      mem aw rdata σ k' C' := by
  unfold tickLogBoundsStack at rd
  exact ⟨_, _, uniswapV3Pool_block_14788 (immWords := wordsOf (immStore v)) hov hret rd⟩

end Benchmarks.UniswapV3.Pool
