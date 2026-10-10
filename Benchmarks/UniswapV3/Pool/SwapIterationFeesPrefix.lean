import Benchmarks.UniswapV3.Pool.SwapIterationAccountedFrame
import Benchmarks.UniswapV3.Pool.SwapFees

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def swapIterationFeesState (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) : SwapStateData :=
  swapFeesState c (swapIterationAccountedState v a s evm) (swapIterationStoredData v a s evm)

noncomputable def swapIterationFeesData (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) : SwapIterationData :=
  swapProtocolData c (swapIterationStoredData v a s evm)

noncomputable def swapIterationFeesFrame (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) : Frame :=
  swapFeesFrame (swapIterationAccountedFrame frame v a s evm) c
    (swapIterationAccountedState v a s evm) (swapIterationStoredData v a s evm)

theorem swapIterationFeesPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hcache : frame.locals.get? "cache" = some c.value)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hexact : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (hm : HeapMemory mem aw q) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (ha : a.Fits) (hfit : s.Fits) (hcfit : c.Fits)
    (hcl : 96 ≤ cache.toNat) (hcachep : cache.toNat + 192 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 64 ≤ 1024) :
    (ExecBlock config frame evm (swapLoopBody.take 16) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 16)
        (.ok (swapIterationFeesFrame frame v a c s evm) evm) ∧
      (swapIterationFeesState v a c s evm).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3637⟩
          (q :: swapLoopWords a p (swapExactInput a).toUInt256 cache snap
            dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' (q + ⟨224⟩) ∧
        SwapStateMemory mem' p (swapIterationFeesState v a c s evm) ∧
        SwapIterationMemory mem' q (swapIterationFeesData v a c s evm) ∧
        MemoryPrefix mem mem' p.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  have hbody : swapLoopBody.take 16 =
      swapLoopBody.take 14 ++ (swapLoopBody.drop 14).take 2 := rfl
  rcases swapIterationAccountingPrefixX (v := v) a s frame evm rd hst hf hi hstate hzero hlimit
      hexact hm hs ha hfit (by omega) hdisj hb hov with
    ⟨hex1, hr⟩ | ⟨hex1, hfit1, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hcover⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hex1 (by intro _ _ h; cases h)
  · have hc1 : SwapCacheMemory m1 cache c := MemoryPrefix.wordArray hp1 hc hcl hcachep
    have hcache1 := (swapIterationAccountedFrame_get frame v a s evm "cache" (by decide)).trans
      hcache
    rcases swapFeesX (v := v) c (swapIterationAccountedState v a s evm)
        (swapIterationStoredData v a s evm) (swapIterationAccountedFrame frame v a s evm) evm r1
        ((swapIterationAccountedFrame_parts frame v a s evm).1.trans hf)
        hcache1 (swapIterationAccountedFrame_state frame v a s evm)
        (swapIterationAccountedFrame_step frame v a s evm) hm1 hc1 hs1 hd1 hfit1
        (by have := hcfit.1; omega) (by omega) hcachep hdisj hb
        (by change R.length + 10 + 20 ≤ 1024; omega) with
      ⟨hex2, hr⟩ | ⟨hex2, hfit2, m2, a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono⟩
    · refine Or.inl ⟨?_, Or.inl hr⟩
      rw [hbody]
      exact execBlock_append_ok hex1 hex2
    · refine Or.inr ⟨?_, hfit2, m2, a2, k2, C2, by omega, r2, hm2, hs2, hd2,
        hp1.trans hp2, by omega⟩
      rw [hbody]
      exact execBlock_append_ok hex1 hex2

end Benchmarks.UniswapV3.Pool
