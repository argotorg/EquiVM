import Benchmarks.UniswapV3.Pool.SwapIterationStoredModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationResultPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hm : HeapMemory mem aw q) (hs : SwapStateMemory mem p s) (ha : a.Fits) (hfit : s.Fits)
    (hpl : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 64 ≤ 1024) :
    (ExecBlock config frame evm (swapLoopBody.take 13) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 13)
        (.ok (swapIterationStoredFrame frame v a s evm) evm) ∧
      (swapIterationStoredState v a s evm).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 (if swapExactInput a then ⟨3383⟩ else ⟨3445⟩)
          (q :: swapLoopWords a p (swapExactInput a).toUInt256 cache snap
            dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' (q + ⟨224⟩) ∧
        SwapStateMemory mem' p (swapIterationStoredState v a s evm) ∧
        SwapIterationMemory mem' q (swapIterationStoredData v a s evm) ∧
        MemoryPrefix mem mem' p.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  have hbody : swapLoopBody.take 13 = swapLoopBody.take 9 ++ (swapLoopBody.drop 9).take 4 := rfl
  rcases swapIterationStepPrefixX a s frame evm rd hst hf hi hstate hzero hlimit
      hm hs ha hfit hpl hdisj hb hov with
    ⟨hex, hr⟩ | ⟨hex1, hv, hclean, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hc1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hex (by intro _ _ h; cases h)
  · let b := swapIterationComputedArgs v a s evm
    have hex2 := swapIterationResultSource (evm := evm) s (swapIterationComputedData v a s evm)
      (swapStepPrice b) (swapStepAmount b true) (swapStepOutput b) (swapStepFee b)
      ((swapIterationComputedFrame_get frame v a s evm "state"
        (by decide) (by decide) (by decide) (by decide)).trans hstate)
      (swapIterationComputedFrame_step frame v a s evm)
      (swapIterationComputedFrame_results frame v a s evm)
    obtain ⟨k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono⟩ :=
      swapIterationResultStoreX (v := v) s (swapIterationComputedData v a s evm)
        (swapStepPrice b) (swapStepAmount b true) (swapStepOutput b) (swapStepFee b)
        (swapExactInput a) r1 hm1 hs1 hd1 (by rw [u256_land_comm]; exact hclean)
        hpl hdisj hb (by change R.length + 11 + 9 ≤ 1024; omega)
    refine Or.inr ⟨?_, swapIterationStoredState_fits v a s evm ha hfit hv,
      _, _, k2, C2, by omega, r2, hm2, hs2, hd2,
      (hp1.mono (by omega : p.toNat ≤ q.toNat)).trans hp2, by omega⟩
    rw [hbody]
    exact execBlock_append_ok hex1 hex2

end Benchmarks.UniswapV3.Pool
