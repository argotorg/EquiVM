import Benchmarks.UniswapV3.Pool.SwapObservation
import Benchmarks.UniswapV3.Pool.SwapObservationFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SwapObservationReadyExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (q p exactWord cache snap : UInt256)
    (R : List UInt256) (s : SwapStateData) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) where
  cacheData : SwapCacheData
  frame' : Frame
  mem : ByteArray
  aw : UInt256
  free : UInt256
  k : Nat
  cost : Nat
  source : ExecStmt config frame evm swapInitializedBody[0]! (.ok frame' evm)
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  cache_get : frame'.locals.get? "cache" = some cacheData.value
  locals_get : ∀ name, name ≠ "cache" → name ≠ "__c12" →
    frame'.locals.get? name = frame.locals.get? name
  fits : cacheData.Fits
  rd : RD (deployedRuntime v) ee g s0 ⟨3775⟩ ([q, p, exactWord, cache, snap] ++ R)
    mem aw rdata σ k cost
  heap : HeapMemory mem aw free
  cache_mem : SwapCacheMemory mem cache cacheData
  state_mem : SwapStateMemory mem p s
  step_mem : SwapIterationMemory mem q d
  memory_prefix : MemoryPrefix initMem mem cache.toNat
  free_mono : initFree.toNat ≤ free.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + 1 + (Cₘ aw - Cₘ initAw) ≤ cost

theorem swapObservationReadyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw q p exactWord cache snap free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3682⟩ ([q, p, exactWord, cache, snap] ++ R)
      mem aw rdata σ k C)
    (hf : frame.contract = contract) (hst : SourceState s0 ee σ evm)
    (hcache : frame.locals.get? "cache" = some c.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv) (hfit : c.Fits)
    (hcl : 96 ≤ cache.toNat) (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcachep : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hqfree : q.toNat + 224 ≤ free.toNat) (hb : free.toNat ≤ 2 ^ 200)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 58 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecStmt config frame evm swapInitializedBody[0]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapObservationReadyExit v ee g s0 σ rdata q p exactWord cache snap R s d
      frame evm mem aw free C) := by
  have hcget := evalExpr_structField (name := "computedLatestObservation")
    (evalExpr_var_get (cfg := config) (evm := evm) hcache) rfl
  have he : evalExpr? config frame evm
      (.unary .not (.field (.var "cache") "computedLatestObservation")) =
      .ok (.bool (!c.computedLatestObservation)) := by
    simp only [evalExpr?, hcget, evalUnaryOp?, EvalResult.ofOption, bind, EvalResult.bind]
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapObservationGuardX (v := v) c rd hm hc (by omega)
      (by change R.length + 1 + 6 ≤ 1024; omega)
  have hbudget1 := hbudget.advance (show C + (Cₘ a1 - Cₘ aw) ≤ C1 by omega)
  have hcover1 : free.toNat ≤ a1.toNat * 32 + 32 := by omega
  cases hcomp : c.computedLatestObservation
  · simp only [hcomp, Bool.false_eq_true, if_false] at r1
    simp only [hcomp, Bool.not_false] at he
    rcases swapObservationX (v := v) c s d initial frame evm r1 hf hst hcache hslot hm1 hc hs hd
        hsnap hfit hcl hsnapc hcachep hpq hqfree hb hbudget1 hallowance hcover1 hov with
      hoog | (⟨hex, hr⟩ | ⟨tick, seconds, hex, hfit2, m2, a2, f2, k2, C2, hC2, r2,
        hm2, hc2, hs2, hd2, hp2, hf2, hcover2⟩)
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue he hex, hr⟩)
    · exact Or.inr (Or.inr ⟨{
        cacheData := swapObservationCache c tick seconds
        frame' := swapObservationFrame frame c tick seconds
        mem := m2, aw := a2, free := f2, k := k2, cost := C2
        source := ExecStmt.iteTrue he hex
        contract_eq := (swapObservationFrame_parts frame c tick seconds).1
        immutables_eq := (swapObservationFrame_parts frame c tick seconds).2
        cache_get := swapObservationFrame_cache frame c tick seconds
        locals_get := swapObservationFrame_get frame c tick seconds
        fits := hfit2, rd := r2, heap := hm2, cache_mem := hc2, state_mem := hs2
        step_mem := hd2, memory_prefix := hp2, free_mono := hf2, cover := hcover2
        cost_bound := by omega }⟩)
  · simp only [hcomp, if_true] at r1
    simp only [hcomp, Bool.not_true] at he
    exact Or.inr (Or.inr ⟨{
      cacheData := c, frame' := frame, mem := mem, aw := a1, free := free, k := k1, cost := C1
      source := ExecStmt.iteFalse he .nil
      contract_eq := rfl, immutables_eq := rfl, cache_get := hcache
      locals_get := fun _ _ _ ↦ rfl
      fits := hfit, rd := r1, heap := hm1, cache_mem := hc, state_mem := hs, step_mem := hd
      memory_prefix := MemoryPrefix.refl _ _, free_mono := le_refl _, cover := hcover1
      cost_bound := hC1 }⟩)

end Benchmarks.UniswapV3.Pool
