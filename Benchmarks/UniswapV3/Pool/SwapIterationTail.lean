import Benchmarks.UniswapV3.Pool.SwapCrossBranch
import Benchmarks.UniswapV3.Pool.SwapPriceChanged
import Benchmarks.UniswapV3.Pool.SwapCrossGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationTailX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3637⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hdget : frame.locals.get? "step" = some d.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hg : ∀ b, frame.locals.get? (feeGrowthName b) = none)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hcf : c.Fits) (hsf : s.Fits)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23)
    (hstart : d.priceStart.toNat < 2 ^ 160) (hnext : d.priceNext.toNat < 2 ^ 160)
    (hperm : ee.perm = true) (hcache : 96 ≤ cache.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcp : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hqfree : q.toNat + 224 ≤ free.toNat) (hb : free.toNat ≤ 2 ^ 200)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecStmt config frame evm swapLoopBody[16]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapTailExit v ee g s0 rdata ⟨3993⟩ q p cache
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      d [swapLoopBody[16]!] frame evm mem aw free C) := by
  have he := evalSwapCrossGuard (evm := evm) s d hsget hdget
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapCrossGuardX (v := v) s d rd hm hs hd hsf.2.2.1 hnext (by omega) (by omega)
      (by change R.length + 12 + 7 ≤ 1024; omega)
  have hbudget1 := hbudget.advance (show C + (Cₘ aw1 - Cₘ aw) ≤ C1 by omega)
  have hcover1 : free.toNat ≤ aw1.toNat * 32 + 32 := by omega
  by_cases heq : s.price = d.priceNext
  · simp only [heq, if_true] at r1
    simp only [heq, decide_true] at he
    rcases swapCrossBranchX (v := v) a c s d initial frame evm r1 hsource hf hi hz hcget
        hsget hdget hslot hg hm1 hc hs hd hsnap hcf hsf ht hperm hcache hsnapc hcp hpq
        hqfree hb hbudget1 hallowance hcover1 hov with hoog | (⟨hex, hr⟩ | ⟨out⟩)
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue he hex, hr⟩)
    · rcases out with ⟨out⟩
      have hC2 := out.cost_bound
      exact Or.inr (Or.inr ⟨{out with
        source := ExecBlock.consNormal (ExecStmt.iteTrue he out.source) .nil
        cost_bound := by omega }⟩)
  · simp only [heq, if_false] at r1
    simp only [heq, decide_false] at he
    rcases swapPriceChangedX (v := v) s d frame evm r1 hf hsget hdget hm1 hs hd hsf hstart
        (by omega) hpq (by omega) (by change R.length + 12 + 24 ≤ 1024; omega) with
      ⟨hex, hr⟩ | ⟨hex, m2, aw2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.iteFalse he hex, hr⟩)
    · refine Or.inr (Or.inr ⟨{
        cacheData := c, stateData := swapPriceChangedState s d
        frame' := swapPriceChangedFrame frame s d, evm' := evm, accounts := σ
        mem := m2, aw := aw2, free := free, k := k2, cost := C2
        source := ExecBlock.consNormal (ExecStmt.iteFalse he hex) .nil
        source_state := hsource
        contract_eq := (swapPriceChangedFrame_parts frame s d).1
        immutables_eq := (swapPriceChangedFrame_parts frame s d).2
        cache_get := (swapPriceChangedFrame_get frame s d "cache" (by decide) (by decide)).trans
          hcget
        state_get := swapPriceChangedFrame_state frame s d hsget
        locals_get := ?_, cache_fits := hcf
        state_fits := swapPriceChangedState_fits s d hsf
        rd := r2, heap := hm2, cache_mem := MemoryPrefix.wordArray hp2 hc hcache hcp
        state_mem := hs2, step_mem := hd2, memory_prefix := hp2.mono (by omega)
        free_mono := le_refl _, cover := by omega, cost_bound := by omega }⟩)
      intro name hn
      simp only [swapTailWrites, List.mem_cons, List.not_mem_nil, not_or,
        not_false_eq_true, and_true] at hn
      exact swapPriceChangedFrame_get frame s d name hn.1 hn.2.2.2.2.2

end Benchmarks.UniswapV3.Pool
