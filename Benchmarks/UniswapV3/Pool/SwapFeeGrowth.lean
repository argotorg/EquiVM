import Benchmarks.UniswapV3.Pool.SwapFeeGrowthStoreTrace
import Benchmarks.UniswapV3.Pool.SwapIterationStepLoad
import Benchmarks.UniswapV3.Pool.SwapAccountingFirstLoad
import Benchmarks.UniswapV3.Pool.FullMathInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapFeeGrowthX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3574⟩ (q :: p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hfit : s.Fits) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    (ExecStmt config frame evm swapLoopBody[15]! .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config frame evm swapLoopBody[15]!
        (.ok (swapFeeGrowthFrame frame s d) evm) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3637⟩ (q :: p :: R) mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' free ∧ SwapStateMemory mem' p (swapFeeGrowthState s d) ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧
        aw.toNat ≤ aw'.toNat) := by
  have hl := SwapStateMemory.load_liquidity hs (by change _ < 2 ^ 256; omega)
  have hc : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) s.liquidity = s.liquidity := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) hfit.2.2.2.2.2
  have hp192 := uadd_word_ofNat_toNat p 192
    (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbp : (p + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 := by rw [hp192]; omega
  have hm1 := hm.expand32 (p + UInt256.ofNat 192) hbp
  have hmono1 := expandedWords_mono (off := p + UInt256.ofNat 192) (size := ⟨32⟩)
    hm.active hbp
  have he := evalSwapFeeGrowthGuard (evm := evm) s hstate
  by_cases hpos : 0 < s.liquidity.toNat
  · have hnz : s.liquidity ≠ ⟨0⟩ := by
      intro hz
      rw [hz] at hpos
      exact (Nat.lt_irrefl 0) hpos
    have r1 := uniswapV3Pool_block_3574_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by rw [hl, solcMask128, hc]; exact isZero_eq_zero_of_ne hnz) rd
    have hq192 := uadd_word_ofNat_toNat q 192
      (show q.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
    have hbq : (UInt256.ofNat 192 + q).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, hq192]; omega
    have hbp' : (UInt256.ofNat 192 + p).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm]; exact hbp
    have hl' : memLoad (UInt256.ofNat 192 + p) mem = s.liquidity := by
      rw [u256_add_comm]; exact hl
    have hfee : memLoad (UInt256.ofNat 192 + q) mem = d.feeAmount := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_fee hd (by change _ < 2 ^ 256; omega)
    have r2 := uniswapV3Pool_block_3594 (immWords := wordsOf (immStore v))
      (by omega) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
    simp only [uniswapV3Pool_block_3594_stack, hl', hfee, solcMask128, hc] at r2
    simp only [solcShift128] at r2
    have hm2 := hm1.expand32 (UInt256.ofNat 192 + q) hbq
    have hm3 := hm2.expand32 (UInt256.ofNat 192 + p) hbp'
    have hmono2 := expandedWords_mono (off := UInt256.ofNat 192 + q) (size := ⟨32⟩)
      hm1.active hbq
    have hmono3 := expandedWords_mono (off := UInt256.ofNat 192 + p) (size := ⟨32⟩)
      hm2.active hbp'
    simp only [hpos, decide_true] at he
    rcases fullMathInternalX (v := v) d.feeAmount (UInt256.ofNat (2 ^ 128)) s.liquidity
        frame evm swapFeeGrowthArgs "__c11" hf (evalSwapFeeGrowthArgs s d hstate hstep) r2
        (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
        (by change R.length + 2 + 16 ≤ 1024; omega) with
      ⟨hex, hr⟩ | ⟨hex, k3, C3, hC3, r3⟩
    · exact Or.inl ⟨ExecStmt.iteTrue he (ExecBlock.consRevert hex), hr⟩
    · obtain ⟨a4, k4, C4, hC4, r4, hm4, hs4, hd4, hp4, hmono4⟩ :=
        swapFeeGrowthStoreX (v := v) s d (swapFeeGrowthValue s d) r3 hm3 hs hd hp hdisj
          (by omega) (by omega)
      refine Or.inr ⟨?_, _, a4, k4, C4, ?_, r4, hm4, ?_, hd4, hp4,
        hmono1.trans (hmono2.trans (hmono3.trans hmono4))⟩
      · simp only [swapFeeGrowthFrame, hpos, if_true]
        exact ExecStmt.iteTrue he (ExecBlock.consNormal hex
          (ExecBlock.consNormal (swapFeeGrowthAssignSource s d hstate) .nil))
      · dsimp only [memExpansionCost, M, expandedWords] at hC3 hC4 ⊢
        omega
      · simpa only [swapFeeGrowthState, hpos, if_true, swapFeeGrowthUpdatedState] using hs4
  · have hz : s.liquidity = ⟨0⟩ := u256_inj (by change s.liquidity.toNat = 0; omega)
    have r1 := uniswapV3Pool_block_3574_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hl, solcMask128, hc, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    refine Or.inr ⟨?_, mem, _, k + 14,
      C + (47 + memExpansionCost aw (p + UInt256.ofNat 192) ⟨32⟩),
      ?_, r1, hm1, ?_, hd, MemoryPrefix.refl _ _, hmono1⟩
    · simp only [swapFeeGrowthFrame, hpos, if_false]
      simp only [hpos, decide_false] at he
      exact ExecStmt.iteFalse he .nil
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [swapFeeGrowthState, hpos, if_false] using hs

end Benchmarks.UniswapV3.Pool
