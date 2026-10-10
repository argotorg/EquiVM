import Benchmarks.UniswapV3.Pool.SwapLoop
import Benchmarks.UniswapV3.Pool.SwapPostLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1500000 in
theorem swapLoopFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free p cache snap start len : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    {old0 old1 : Value}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2991⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap start len ⟨621⟩ R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v) (hperm : ee.perm = true)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hr : frame.locals.get? "recipient" = some (.address a.recipient))
    (he : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (ha : frame.locals.get? "amountSpecified" = some (.int a.amountSpecified))
    (h0 : frame.locals.get? "amount0" = some old0)
    (h1 : frame.locals.get? "amount1" = some old1)
    (hd : frame.locals.get? "data" =
      some (.bytes (ee.calldata.extract start.toNat (start.toNat + len.toNat))))
    (hcache : frame.locals.get? "cache" = some c.value)
    (hstate : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hslot0 : frame.locals.get? "slot0" = none)
    (hliq : frame.locals.get? "liquidity" = none)
    (hg : ∀ second, frame.locals.get? (feeGrowthName second) = none)
    (hprot : frame.locals.get? "protocolFees" = none)
    (hm : HeapMemory mem aw free) (hcm : SwapCacheMemory mem cache c)
    (hsm : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (haf : a.Fits) (hcf : c.Fits) (hsf : s.Fits)
    (hsl : 96 ≤ snap.toNat) (hcl : 96 ≤ cache.toNat)
    (hsc : snap.toNat + 224 ≤ cache.toNat) (hcp : cache.toNat + 192 ≤ p.toNat)
    (hpf : p.toNat + 224 ≤ free.toNat)
    (hmem : 128 ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hcd : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecBlock config frame evm (swapTransition.body.drop 13) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapTransition.body.drop 13) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ (finalFrame : Frame) (finalState : EVM.State) (amount0 amount1 : Int),
      ExecBlock config frame evm (swapTransition.body.drop 13)
        (.returned finalFrame finalState (some [.int amount0, .int amount1])) ∧
      RDret (deployedRuntime v) g s0 finalState.accountMap
        ((EVM.wordOfInt amount0).toByteArray ++ (EVM.wordOfInt amount1).toByteArray) ∧
      (-(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255) ∧
      (-(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) := by
  rcases swapLoopX (v := v) a c s initial frame evm rd hs hf hi hz hcache hstate hslot hlimit he
      hg hm hcm hsm hsnap haf hcf hsf hperm hcl hsl hsc hcp hpf hbudget hallowance hcover hov
      with hoog | (⟨hex, rr⟩ | hout)
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hex, rr⟩)
  rcases hout with ⟨out⟩
  by_cases hcost : g.toNat < out.cost
  · exact Or.inl (RD.oog_of_cost_gt out.rd hcost)
  have hstep := out.cost_bound
  have hbudget' := hbudget.advance
    (show C + (Cₘ out.aw - Cₘ aw) ≤ out.cost by omega)
  have hwords := hbudget'.words_lt (gas := g) (by omega) hallowance
  have hcover' := out.cover
  have hfree := out.free_mono
  have hsize : 128 ≤ out.mem.size := hmem.trans out.memory_prefix.size
  have hcache128 : 128 ≤ cache.toNat := by omega
  have hzero' : memLoad (UInt256.ofNat 96) out.mem = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad out.memory_prefix (UInt256.ofNat 96)
      (by decide) hcache128 hmem, hzero]
  rcases swapPostLoopX (v := v) a out.cacheData out.stateData initial out.frame' out.evm'
      out.rd out.source_state (out.contract_eq.trans hf) (out.immutables_eq.trans hi) hperm
      ((out.locals_get _ (by decide)).trans hz)
      ((out.locals_get _ (by decide)).trans hr)
      ((out.locals_get _ (by decide)).trans he)
      ((out.locals_get _ (by decide)).trans ha)
      ((out.locals_get _ (by decide)).trans h0)
      ((out.locals_get _ (by decide)).trans h1)
      ((out.locals_get _ (by decide)).trans hd)
      out.cache_get out.state_get ((out.locals_get _ (by decide)).trans hslot)
      ((out.locals_get _ (by decide)).trans hslot0)
      ((out.locals_get _ (by decide)).trans hliq)
      (fun b ↦ (out.locals_get _ (by cases b <;> decide)).trans (hg b))
      ((out.locals_get _ (by decide)).trans hprot)
      out.heap out.cache_mem out.state_mem out.snapshot out.cache_fits out.state_fits
      hsl hcl hsc hcp (by omega) hsize hzero' hcd hl (by omega) (by omega)
      with ⟨hex, rr⟩ | (⟨hex, rr⟩ | ⟨finalFrame, finalState, hex, rr⟩)
  · exact Or.inr (Or.inl ⟨ExecBlock.consNormal out.source hex, rr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ExecBlock.consNormal out.source hex, rr⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨finalFrame, finalState,
      swapAmount0 a out.stateData, swapAmount1 a out.stateData,
      ExecBlock.consNormal out.source hex, rr, swapAmounts_bounds a out.stateData out.state_fits⟩))

end Benchmarks.UniswapV3.Pool
