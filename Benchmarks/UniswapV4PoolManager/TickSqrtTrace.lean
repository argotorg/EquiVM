import Benchmarks.UniswapV4PoolManager.TickSqrtStartTrace
import Benchmarks.UniswapV4PoolManager.TickSqrtMiddleTrace
import Benchmarks.UniswapV4PoolManager.TickSqrtFinishTrace
import Benchmarks.UniswapV4PoolManager.WordAbsolute

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickSqrtRatio_parts (absTick : UInt256) :
    tickSqrtFinalStage absTick (tickSqrtStages absTick (tickSqrtFirstStage absTick) tickSqrtMiddleFactors) =
      tickSqrtRatio absTick := rfl

theorem tickSqrtTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret tick : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16728⟩ (tick :: ret :: R) mem aw rdata σ k C) :
    ((EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)).natAbs > 887272 ∧ RDrev (deployedRuntime v) g s0) ∨
    ((EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)).natAbs ≤ 887272 ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ret
        (tickSqrtPrice (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) :: R) mem aw rdata σ k' C') := by
  let cleanTick := UInt256.signextend (UInt256.ofNat 2) tick
  let absTick := UInt256.ofNat (EVM.signed cleanTick).natAbs
  have ha : absTick.toNat = (EVM.signed cleanTick).natAbs :=
    UInt256.toNat_ofNat_of_lt (signedNatAbs_lt_size cleanTick)
  by_cases hn : (EVM.signed cleanTick).natAbs ≤ 887272
  · have hc : UInt256.gt
        (UInt256.xor (UInt256.sar (UInt256.ofNat 255) cleanTick + cleanTick)
          (UInt256.sar (UInt256.ofNat 255) cleanTick)) (UInt256.ofNat 887272) = UInt256.ofNat 0 := by
      rw [wordAbsolute]
      apply ugt_zero
      change absTick.toNat ≤ 887272
      rw [ha]
      exact hn
    have rd1 := poolManagerBlocks.poolManager_block_16728_fallthrough (by omega) hc h
    simp only [poolManagerBlocks.poolManager_block_16728_fallthrough_stack, wordAbsolute] at rd1
    obtain ⟨k2, C2, rd2⟩ := tickSqrtStartTrace v hstack rd1
    obtain ⟨k3, C3, rd3⟩ := tickSqrtMiddleTrace v (by simp only [List.length_cons]; omega) rd2
    obtain ⟨k4, C4, rd4⟩ := tickSqrtFinishTrace v (by omega) hret rd3
    simp only [tickSqrtRatio_parts] at rd4
    exact .inr ⟨hn, k4, C4, rd4⟩
  · have hc : UInt256.gt
        (UInt256.xor (UInt256.sar (UInt256.ofNat 255) cleanTick + cleanTick)
          (UInt256.sar (UInt256.ofNat 255) cleanTick)) (UInt256.ofNat 887272) ≠ UInt256.ofNat 0 := by
      rw [wordAbsolute]
      have hg : UInt256.gt absTick (UInt256.ofNat 887272) = ⟨1⟩ := ugt_one (by
        change 887272 < absTick.toNat
        rw [ha]
        omega)
      rw [hg]
      decide
    have rd1 := poolManagerBlocks.poolManager_block_16728_taken (by omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := poolManagerBlocks.poolManager_block_17566 (by omega) rd1
    exact .inl ⟨Nat.lt_of_not_ge hn, hr⟩

end Benchmarks.UniswapV4PoolManager
