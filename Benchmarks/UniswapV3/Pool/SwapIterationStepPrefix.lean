import Benchmarks.UniswapV3.Pool.SwapIterationFrameLaws
import Benchmarks.UniswapV3.Pool.SwapIterationStepCall
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationComputedData (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : SwapIterationData :=
  swapIterationPriceData (swapIterationClampedData v a s evm)

noncomputable def swapIterationComputedFrame (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) : Frame :=
  swapIterationStepFrame
    (swapIterationPriceFrame (swapIterationClampedFrame frame v a s evm)
      (swapIterationClampedData v a s evm)) v a s (swapIterationComputedData v a s evm)

theorem swapIterationStepPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hm : HeapMemory mem aw q) (hs : SwapStateMemory mem p s) (ha : a.Fits) (hfit : s.Fits)
    (hpl : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 64 ≤ 1024) :
    let d := swapIterationComputedData v a s evm
    let b := swapIterationStepArgs v a s d
    (ExecBlock config frame evm (swapLoopBody.take 9) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 9)
        (.ok (swapIterationComputedFrame frame v a s evm) evm) ∧
      swapStepValid b ∧
      UInt256.land (swapStepRawPrice b s.price (swapIterationTarget a d))
        (UInt256.ofNat (2 ^ 160 - 1)) = swapStepPrice b ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3347⟩
          (swapStepRawResults b s.price (swapIterationTarget a d) ++
            q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' (q + ⟨224⟩) ∧ SwapStateMemory mem' p s ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' q.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  dsimp only
  have hbody : swapLoopBody.take 9 = swapLoopBody.take 6 ++
      ((swapLoopBody.drop 6).take 2 ++ [swapLoopBody[8]!]) := rfl
  rcases swapIterationTickPrefixX a s frame evm rd hst hf hi hstate hzero hm hs hfit
      hpl hdisj hb (by omega) with
    ⟨hfail, hr⟩ | ⟨hex1, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hc1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hfail (by intro _ _ h; cases h)
  · have hparts := swapIterationClampedFrame_parts frame v a s evm
    obtain ⟨hex2, m2, a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩ :=
      swapIterationPriceX a s (swapIterationClampedData v a s evm)
        (swapIterationClampedFrame frame v a s evm) evm r1 (hparts.1.trans hf)
        (swapIterationClampedFrame_step frame v a s evm) hm1 hs1 hd1
        (swapIterationClampedData_bounds v a s evm) (by have hl := hm.lower; omega)
        hdisj hb (by omega)
    have hget (name : Ident) (hstep : name ≠ "step") (hc2 : name ≠ "__c2")
        (hc3 : name ≠ "__c3") :
        (swapIterationPriceFrame (swapIterationClampedFrame frame v a s evm)
          (swapIterationClampedData v a s evm)).locals.get? name = frame.locals.get? name := by
      rw [swapIterationPriceFrame_get _ _ _ hstep hc3,
        swapIterationClampedFrame_get _ _ _ _ _ _ hstep hc2]
    rcases swapIterationStepCallX (v := v) a s (swapIterationComputedData v a s evm)
        (swapIterationPriceFrame (swapIterationClampedFrame frame v a s evm)
          (swapIterationClampedData v a s evm)) evm r2 hm2 hs2 hd2
        (frame_eq_of_parts (hparts.1.trans hf) (hparts.2.trans hi))
        ((hget "state" (by decide) (by decide) (by decide)).trans hstate)
        (swapIterationPriceFrame_step _ _)
        ((hget "zeroForOne" (by decide) (by decide) (by decide)).trans hzero)
        ((hget "sqrtPriceLimitX96" (by decide) (by decide) (by decide)).trans hlimit)
        ha hfit (tickSqrtValue_lt160 _) (by omega) hb hov with
      ⟨hex3, hr⟩ | ⟨hex3, hvalid, hclean, a3, k3, C3, hC3, r3, hm3, hmono3⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [hbody]
      exact execBlock_append_ok hex1 (execBlock_append_ok hex2 (ExecBlock.consRevert hex3))
    · refine Or.inr ⟨?_, hvalid, hclean, m2, a3, k3, C3, by omega, r3, hm3,
        hs2, hd2, hp1.trans hp2, by omega⟩
      rw [hbody]
      exact execBlock_append_ok hex1
        (execBlock_append_ok hex2 (ExecBlock.consNormal hex3 ExecBlock.nil))

end Benchmarks.UniswapV3.Pool
