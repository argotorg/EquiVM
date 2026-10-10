import Benchmarks.UniswapV3.Pool.SwapIterationStepLoad
import Benchmarks.UniswapV3.Pool.SwapStepCostInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def swapIterationStepFrame (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall frame "__c4" (some (swapStepResults (swapIterationStepArgs v a s d)))

theorem swapIterationStepCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if a.zeroForOne then ⟨3260⟩ else ⟨3231⟩)
      (swapIterationCompareWords a s.price ⟨3347⟩ q p exactWord cache snap
        dataStart dataLength ret R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (hframe : frame = {contract := contract, locals := frame.locals, immutables := immStore v})
    (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (ha : a.Fits) (hsfit : s.Fits) (hdfit : d.priceNext.toNat < 2 ^ 160)
    (hpb : p.toNat + 224 ≤ 2 ^ 200) (hqb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 64 ≤ 1024) :
    (ExecStmt config frame evm swapLoopBody[8]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config frame evm swapLoopBody[8]!
        (.ok (swapIterationStepFrame frame v a s d) evm) ∧
      swapStepValid (swapIterationStepArgs v a s d) ∧
      UInt256.land
          (swapStepRawPrice (swapIterationStepArgs v a s d) s.price (swapIterationTarget a d))
          (UInt256.ofNat (2 ^ 160 - 1)) = swapStepPrice (swapIterationStepArgs v a s d) ∧
      ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3347⟩
          (swapStepRawResults (swapIterationStepArgs v a s d) s.price (swapIterationTarget a d) ++
            q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat) := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapIterationTargetX a d rd hm hd ha hdfit hqb (by omega)
  obtain ⟨a2, k2, C2, hC2, r2, hm2, hmono2⟩ :=
    swapIterationStepLoadX a s d r1 hm1 hs hpb (by omega)
  have hargs := swapIterationStepArgs_fits v a s d ha hsfit hdfit
  have hcur : UInt256.land s.price (UInt256.ofNat (2 ^ 160 - 1)) = s.price :=
    u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hsfit.2.2.1
  have htar : UInt256.land (swapIterationTarget a d) (UInt256.ofNat (2 ^ 160 - 1)) =
      swapIterationTarget a d :=
    u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
      (swapIterationTarget_fits a d ha hdfit)
  have hliq : UInt256.land s.liquidity (UInt256.ofNat (2 ^ 128 - 1)) = s.liquidity :=
    u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) hsfit.2.2.2.2.2
  have hfee : UInt256.land (wordsOf (immStore v) "fee") (UInt256.ofNat (2 ^ 24 - 1)) =
      poolFeeWord v := by
    rw [wordsOf_immStore_fee, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat]
    rfl
  have he := evalSwapIterationStepArgs (evm := evm) v a s d hstate hstep hzero hlimit hframe
  rcases swapStepInternalMonoX (v := v) (swapIterationStepArgs v a s d) frame evm
      swapIterationStepExprs "__c4" hframe he r2 hargs hcur htar hliq hfee
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 14 + 50 ≤ 1024; omega) with
    ⟨hsrc, hbad⟩ | ⟨hsrc, hvalid, hclean, k3, C3, hC3, r3⟩
  · exact Or.inl ⟨by rw [swapIterationStepStmt]; exact hsrc, hbad⟩
  · refine Or.inr ⟨?_, hvalid, hclean, a2, k3, C3, by omega, r3, hm2,
      hmono1.trans hmono2⟩
    rw [swapIterationStepStmt]
    exact hsrc

end Benchmarks.UniswapV3.Pool
