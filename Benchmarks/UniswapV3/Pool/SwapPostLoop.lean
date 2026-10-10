import Benchmarks.UniswapV3.Pool.SwapWrite
import Benchmarks.UniswapV3.Pool.SwapPoolLiquidity
import Benchmarks.UniswapV3.Pool.SwapPoolFeesTrace
import Benchmarks.UniswapV3.Pool.SwapAmountsTrace
import Benchmarks.UniswapV3.Pool.SwapFinishSource
import Benchmarks.UniswapV3.Pool.SwapFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1500000 in
theorem swapPostLoopX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free p cache snap start len : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    {old0 old1 : Value}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3999⟩
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
    (hslot0 : frame.locals.get? "slot0" = none)
    (hliq : frame.locals.get? "liquidity" = none)
    (hg : ∀ second, frame.locals.get? (feeGrowthName second) = none)
    (hprot : frame.locals.get? "protocolFees" = none)
    (hm : HeapMemory mem aw free) (hcm : SwapCacheMemory mem cache c)
    (hsm : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hcf : c.Fits) (hsf : s.Fits)
    (hsl : 96 ≤ snap.toNat) (hcl : 96 ≤ cache.toNat)
    (hsc : snap.toNat + 224 ≤ cache.toNat) (hcp : cache.toNat + 192 ≤ p.toNat)
    (hpf : p.toNat + 224 ≤ free.toNat)
    (hmem : 128 ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hcd : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hb : free.toNat + 2 ^ 140 + 2048 ≤ 2 ^ 200) (hov : R.length + 42 ≤ 1024) :
    (ExecBlock config frame evm (swapTransition.body.drop 14) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapTransition.body.drop 14) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ finalFrame finalState,
      ExecBlock config frame evm (swapTransition.body.drop 14)
        (.returned finalFrame finalState (some [.int (swapAmount0 a s), .int (swapAmount1 a s)])) ∧
      RDret (deployedRuntime v) g s0 finalState.accountMap
        ((EVM.wordOfInt (swapAmount0 a s)).toByteArray ++
          (EVM.wordOfInt (swapAmount1 a s)).toByteArray) := by
  rcases swapWriteX (v := v) c s initial frame evm rd hs hf hi hcache hstate hslot hslot0
      hm hcm hsm hsnap hcf hsf hperm hsl hcl hsc hcp hpf (by omega)
      (by change R.length + 9 + 33 ≤ 1024; omega) with
    ⟨hbad, rr⟩ | (⟨hbad, rr⟩ | hwrite)
  · exact Or.inl ⟨ExecBlock.consRevert hbad, Or.inr rr⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consStatic hbad, rr⟩)
  rcases hwrite with ⟨w⟩
  have hwf : w.frame'.contract = contract := w.contract_eq.trans hf
  have hwi : w.frame'.immutables = immStore v := w.immutables_eq.trans hi
  have hwc := (w.locals_get "cache" (by decide)).trans hcache
  have hws := (w.locals_get "state" (by decide)).trans hstate
  have hwz := (w.locals_get "zeroForOne" (by decide)).trans hz
  have hmem1 : 128 ≤ w.mem.size := le_trans hmem w.memory_prefix.size
  have hzero1 : memLoad (UInt256.ofNat 96) w.mem = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad w.memory_prefix (UInt256.ofNat 96) (by decide) hm.lower hmem, hzero]
  have hwbound := w.free_bound
  have hpb : p.toNat + 224 ≤ 2 ^ 200 := by omega
  obtain ⟨evm2, σ2, aw2, k2, C2, hex2, hs2, r2, hm2⟩ :=
    swapPoolLiquidityX (v := v) c s w.frame' w.evm' w.rd w.source_state hwf hwc hws
      ((w.locals_get "liquidity" (by decide)).trans hliq) w.heap w.cache_mem w.state_mem hcf hsf
      hperm (by omega) hpb (by change R.length + 10 + 9 ≤ 1024; omega)
  obtain ⟨hex3, hs3, aw3, k3, C3, r3, hm3⟩ := swapPoolFeesX (v := v) a s w.frame' evm2 r2 hs2
    hwf hwz hws (fun second ↦ (w.locals_get _ (by cases second <;> decide)).trans (hg second))
    ((w.locals_get "protocolFees" (by decide)).trans hprot) hm2 w.state_mem hsf hperm hpb (by omega)
  have hex4 := swapAmountsSource (evm := swapPoolFeesState evm2 (!a.zeroForOne) s)
    a s hwz ((w.locals_get "exactInput" (by decide)).trans he)
    ((w.locals_get "amountSpecified" (by decide)).trans ha) hws
    ((w.locals_get "amount0" (by decide)).trans h0) ((w.locals_get "amount1" (by decide)).trans h1)
  obtain ⟨aw4, k4, C4, r4, hm4⟩ := swapAmountsX (v := v) a s r3 hm3 w.state_mem hpb (by omega)
  let f4 := swapAmountsFrame w.frame' a s
  have hget4 (name : Ident) (hn0 : name ≠ "amount0") (hn1 : name ≠ "amount1") :
      f4.locals.get? name = w.frame'.locals.get? name := swapAmountsFrame_get _ _ _ _ hn0 hn1
  have hf4 : f4.contract = contract := hwf
  have hi4 : f4.immutables = immStore v := hwi
  have hfit := swapAmounts_bounds a s hsf
  rcases swapPaymentX (v := v) a (swapAmount0 a s) (swapAmount1 a s) f4
      (swapPoolFeesState evm2 (!a.zeroForOne) s) r4 hs3 hf4 hi4 hperm
      ((hget4 _ (by decide) (by decide)).trans hwz)
      ((hget4 _ (by decide) (by decide)).trans ((w.locals_get _ (by decide)).trans hr))
      (swapAmountsFrame_amount0 _ _ _) (swapAmountsFrame_amount1 _ _ _)
      ((hget4 _ (by decide) (by decide)).trans ((w.locals_get _ (by decide)).trans hd))
      hfit.1 hfit.2 hm4 hmem1 hzero1 hcd hl (by omega) (by omega) with
    ⟨hbad, rr⟩ | hpayment
  · exact Or.inl ⟨ExecBlock.consNormal w.source (ExecBlock.consNormal hex2
      (ExecBlock.consNormal hex3 (ExecBlock.consNormal hex4 (ExecBlock.consRevert hbad)))),
        Or.inl rr⟩
  rcases hpayment with ⟨pay⟩
  have hpbound := pay.free_bound
  have hget5 (name : Ident) (hn : name ∉ swapPaymentWrites a.zeroForOne) :
      pay.frame'.locals.get? name = f4.locals.get? name := pay.locals_get name hn
  have hfinish := swapFinishSource pay.frame' pay.evm' a.recipient
    (swapAmount0 a s) (swapAmount1 a s) s (pay.contract_eq.trans hf4)
    ((hget5 _ (by cases a.zeroForOne <;> decide)).trans
      ((hget4 _ (by decide) (by decide)).trans ((w.locals_get _ (by decide)).trans hr)))
    ((hget5 _ (by cases a.zeroForOne <;> decide)).trans (swapAmountsFrame_amount0 _ _ _))
    ((hget5 _ (by cases a.zeroForOne <;> decide)).trans (swapAmountsFrame_amount1 _ _ _))
    ((hget5 _ (by cases a.zeroForOne <;> decide)).trans
      ((hget4 _ (by decide) (by decide)).trans hws))
    ((hget5 _ (by cases a.zeroForOne <;> decide)).trans
      ((hget4 _ (by decide) (by decide)).trans ((w.locals_get _ (by decide)).trans hslot0)))
  have rr := swapFinishX (v := v) pay.rd pay.source_state hperm pay.heap (by omega) hpb
    (by omega)
  exact Or.inr (Or.inr ⟨pay.frame', storeSlot0Unlocked pay.evm' true,
    ExecBlock.consNormal w.source (ExecBlock.consNormal hex2 (ExecBlock.consNormal hex3
      (ExecBlock.consNormal hex4 (ExecBlock.consNormal pay.source hfinish)))), rr⟩)

end Benchmarks.UniswapV3.Pool
