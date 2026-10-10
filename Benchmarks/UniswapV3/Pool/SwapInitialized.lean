import Benchmarks.UniswapV3.Pool.SwapLiquidity
import Benchmarks.UniswapV3.Pool.SwapCrossCall
import Benchmarks.UniswapV3.Pool.SwapObservationReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapTailWrites : List Ident :=
  ["state", "cache", "__c12", "liquidityNet", "__c14", "__c15"]

structure SwapTailExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (rdata : ByteArray) (pc q p cache : UInt256) (stack : List UInt256)
    (d : SwapIterationData) (body : List Stmt) (frame : Frame) (evm : EVM.State)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) where
  cacheData : SwapCacheData
  stateData : SwapStateData
  frame' : Frame
  evm' : EVM.State
  accounts : AccountMap
  mem : ByteArray
  aw : UInt256
  free : UInt256
  k : Nat
  cost : Nat
  source : ExecBlock config frame evm body (.ok frame' evm')
  source_state : SourceState s0 ee accounts evm'
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  cache_get : frame'.locals.get? "cache" = some cacheData.value
  state_get : frame'.locals.get? "state" = some stateData.value
  locals_get : ∀ name, name ∉ swapTailWrites → frame'.locals.get? name = frame.locals.get? name
  cache_fits : cacheData.Fits
  state_fits : stateData.Fits
  rd : RD (deployedRuntime v) ee g s0 pc stack mem aw rdata accounts k cost
  heap : HeapMemory mem aw free
  cache_mem : SwapCacheMemory mem cache cacheData
  state_mem : SwapStateMemory mem p stateData
  step_mem : SwapIterationMemory mem q d
  memory_prefix : MemoryPrefix initMem mem cache.toNat
  free_mono : initFree.toNat ≤ free.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + 1 + (Cₘ aw - Cₘ initAw) ≤ cost

theorem swapInitializedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3682⟩
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
    (hperm : ee.perm = true) (hcache : 96 ≤ cache.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcp : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hqfree : q.toNat + 224 ≤ free.toNat) (hb : free.toNat ≤ 2 ^ 200)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecBlock config frame evm swapInitializedBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapTailExit v ee g s0 rdata ⟨3893⟩ q p cache
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      d swapInitializedBody frame evm mem aw free C) := by
  rcases swapObservationReadyX (v := v) c s d initial frame evm rd hf hsource hcget hslot
      hm hc hs hd hsnap hcf hcache hsnapc hcp hpq hqfree hb hbudget hallowance hcover
      (by change R.length + 9 + 58 ≤ 1024; omega) with hoog | (⟨hex, hr⟩ | ⟨out⟩)
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hex, hr⟩)
  · rcases out with ⟨out⟩
    have hf1 := frame_eq_of_parts (out.contract_eq.trans hf) (out.immutables_eq.trans hi)
    have hz1 := (out.locals_get "zeroForOne" (by decide) (by decide)).trans hz
    have hs1 := (out.locals_get "state" (by decide) (by decide)).trans hsget
    have hd1 := (out.locals_get "step" (by decide) (by decide)).trans hdget
    have hg1 : ∀ b, out.frame'.locals.get? (feeGrowthName b) = none := by
      intro b
      exact (out.locals_get (feeGrowthName b) (by cases b <;> decide)
        (by cases b <;> decide)).trans (hg b)
    obtain ⟨hex2, hsrc2, aw2, k2, C2, hC2, r2, hm2, hc2, hs2, hd2, hp2, hmono2⟩ :=
      swapCrossCallX (v := v) a out.cacheData s d out.frame' evm out.rd hsource hf1 hz1
        out.cache_get hs1 hd1 hg1 out.heap out.cache_mem out.state_mem out.step_mem ht hperm
        hcache hcp hpq (by omega) (by omega)
    let ca := swapCrossArgs a.zeroForOne out.cacheData s d σ ee
    let f2 := swapCrossCallFrame out.frame' evm ca
    have hf2 : f2.contract = contract := out.contract_eq.trans hf
    have hz2 := (resumeAfterInternalCall_get out.frame' "liquidityNet" "zeroForOne"
      (some [.int (tickCrossResult evm ca)]) (by decide)).trans hz1
    have hsget2 := (resumeAfterInternalCall_get out.frame' "liquidityNet" "state"
      (some [.int (tickCrossResult evm ca)]) (by decide)).trans hs1
    have hn2 : f2.locals.get? "liquidityNet" = some (.int (tickCrossResult evm ca)) :=
      Std.HashMap.getElem?_insert_self
    have hnetfit : -(2 ^ 127 : Int) ≤ tickCrossResult evm ca ∧
        tickCrossResult evm ca < 2 ^ 127 := tickNetValue_bounds _ _ _
    rcases swapLiquidityX (v := v) a s d (tickCrossResult evm ca) f2 (tickCrossState evm ca)
        r2 hf2 hz2 hsget2 hn2 hm2 hs2 hd2 hsf hnetfit (by omega) hpq (by omega) (by omega) with
      ⟨hex3, hr⟩ | ⟨hex3, m3, aw3, k3, C3, hC3, r3, hm3, hs3, hd3, hp3, hmono3⟩
    · exact Or.inr (Or.inl ⟨ExecBlock.consNormal out.source
        (ExecBlock.consNormal hex2 hex3), hr⟩)
    · have hf3 := swapLiquidityFrame_parts f2 s a.zeroForOne (tickCrossResult evm ca)
      have hget3 := swapLiquidityFrame_get f2 s a.zeroForOne (tickCrossResult evm ca)
      have hC1 := out.cost_bound
      have hcvr := out.cover
      refine Or.inr (Or.inr ⟨{
        cacheData := out.cacheData
        stateData := swapLiquidityState s a.zeroForOne (tickCrossResult evm ca)
        frame' := swapLiquidityFrame f2 s a.zeroForOne (tickCrossResult evm ca)
        evm' := tickCrossState evm ca, accounts := tickCrossMap ca σ ee
        mem := m3, aw := aw3, free := out.free, k := k3, cost := C3
        source := ExecBlock.consNormal out.source (ExecBlock.consNormal hex2 hex3)
        source_state := hsrc2
        contract_eq := hf3.1.trans out.contract_eq
        immutables_eq := hf3.2.trans out.immutables_eq
        cache_get := (hget3 "cache" (by decide) (by decide) (by decide)).trans
          ((resumeAfterInternalCall_get out.frame' "liquidityNet" "cache"
            (some [.int (tickCrossResult evm ca)]) (by decide)).trans out.cache_get)
        state_get := swapLiquidityFrame_state f2 s a.zeroForOne (tickCrossResult evm ca)
        locals_get := ?_
        cache_fits := out.fits
        state_fits := swapLiquidityState_fits s a.zeroForOne (tickCrossResult evm ca) hsf
        rd := r3, heap := hm3
        cache_mem := MemoryPrefix.wordArray hp3 hc2 hcache hcp
        state_mem := hs3, step_mem := hd3
        memory_prefix := out.memory_prefix.trans (hp2.trans (hp3.mono (by omega)))
        free_mono := out.free_mono, cover := by omega, cost_bound := by omega }⟩)
      intro name hn
      simp only [swapTailWrites, List.mem_cons, List.not_mem_nil, not_or,
        not_false_eq_true, and_true] at hn
      exact (hget3 name hn.1 hn.2.2.2.2.1 hn.2.2.2.1).trans
        ((resumeAfterInternalCall_get out.frame' "liquidityNet" name
          (some [.int (tickCrossResult evm ca)]) hn.2.2.2.1).trans
          (out.locals_get name hn.2.1 hn.2.2.1))

end Benchmarks.UniswapV3.Pool
