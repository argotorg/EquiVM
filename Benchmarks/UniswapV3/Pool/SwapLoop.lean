import Benchmarks.UniswapV3.Pool.SwapIteration
import Benchmarks.UniswapV3.Pool.SwapLoopGuardMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SwapLoopExit (v : UniswapV3PoolImmutables) (a : SwapArgs) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (rdata : ByteArray) (p cache snap : UInt256) (stack : List UInt256)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
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
  source : ExecStmt config frame evm swapTransition.body[13]! (.ok frame' evm')
  stopped : swapContinues a stateData = false
  source_state : SourceState s0 ee accounts evm'
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  cache_get : frame'.locals.get? "cache" = some cacheData.value
  state_get : frame'.locals.get? "state" = some stateData.value
  locals_get : ∀ name, name ∉ swapIterationWrites →
    frame'.locals.get? name = frame.locals.get? name
  cache_fits : cacheData.Fits
  state_fits : stateData.Fits
  rd : RD (deployedRuntime v) ee g s0 ⟨3999⟩ stack mem aw rdata accounts k cost
  heap : HeapMemory mem aw free
  cache_mem : SwapCacheMemory mem cache cacheData
  state_mem : SwapStateMemory mem p stateData
  snapshot : Slot0Memory mem snap initial.accountMap initial.executionEnv
  memory_prefix : MemoryPrefix initMem mem cache.toNat
  free_mono : initFree.toNat ≤ free.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + 1 + (Cₘ aw - Cₘ initAw) ≤ cost

set_option maxHeartbeats 1000000 in
theorem swapLoopX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat}
    {aw p q cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2991⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hexact : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (hg : ∀ b, frame.locals.get? (feeGrowthName b) = none)
    (hm : HeapMemory mem aw q) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (ha : a.Fits) (hcf : c.Fits) (hsf : s.Fits)
    (hperm : ee.perm = true) (hcache : 96 ≤ cache.toNat) (hsl : 96 ≤ snap.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcp : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : q.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecStmt config frame evm swapTransition.body[13]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapLoopExit v a ee g s0 rdata p cache snap
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      initial frame evm mem aw q C) := by
  generalize hfuel : g.toNat + 1 - C = fuel
  induction fuel using Nat.strong_induction_on
      generalizing σ k C aw q mem c s frame evm with
  | h fuel ih =>
    by_cases hgas : g.toNat < C
    · exact Or.inl (RD.oog_of_cost_gt rd hgas)
    rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hcap
    · exact Or.inl hoog
    have he := evalSwapLoopCondition (evm := evm) a s hsget hlimit
    obtain ⟨aw1, k1, C1, hC1, r1, haw1, hmono1⟩ :=
      swapLoopGuardMonoX (v := v) a s rd ha hsf hs hm.active (by omega) (by omega)
    have hm1 : HeapMemory mem aw1 q := {hm with active := haw1}
    have hbudget1 := hbudget.advance (show C + (Cₘ aw1 - Cₘ aw) ≤ C1 by omega)
    have hcover1 : q.toNat ≤ aw1.toNat * 32 + 32 := by omega
    cases hcont : swapContinues a s
    · simp only [hcont, Bool.false_eq_true, if_false] at r1
      rw [hcont] at he
      exact Or.inr (Or.inr ⟨{
        cacheData := c, stateData := s, frame' := frame, evm' := evm, accounts := σ
        mem := mem, aw := aw1, free := q, k := k1, cost := C1
        source := ExecStmt.whileFalse he, stopped := hcont
        source_state := hsource, contract_eq := rfl, immutables_eq := rfl
        cache_get := hcget, state_get := hsget, locals_get := fun _ _ ↦ rfl
        cache_fits := hcf, state_fits := hsf, rd := r1, heap := hm1
        cache_mem := hc, state_mem := hs, snapshot := hsnap
        memory_prefix := MemoryPrefix.refl _ _, free_mono := le_refl _, cover := hcover1
        cost_bound := hC1 }⟩)
    · simp only [hcont, if_true] at r1
      rw [hcont] at he
      rcases swapIterationX (v := v) a c s initial frame evm r1 hsource hf hi hz hcget hsget
          hslot hlimit hexact hg hm1 hc hs hsnap ha hcf hsf hperm hcache hsl hsnapc hcp hpq
          hbudget1 hallowance hcover1 hov with hoog | (⟨hex, hr⟩ | ⟨out⟩)
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨ExecStmt.whileRevert he hex, hr⟩)
      · rcases out with ⟨out⟩
        have hcost2 := out.cost_bound
        have hcost : C + 1 + (Cₘ out.aw - Cₘ aw) ≤ out.cost := by omega
        have hlt : g.toNat + 1 - out.cost < fuel := by omega
        have hbudget2 := hbudget1.advance
          (show C1 + (Cₘ out.aw - Cₘ aw1) ≤ out.cost by omega)
        have hpq2 : p.toNat + 224 ≤ out.free.toNat := by
          have hm := out.free_mono
          omega
        have hg2 : ∀ b, out.frame'.locals.get? (feeGrowthName b) = none := by
          intro b
          exact (out.locals_get (feeGrowthName b) (by cases b <;> decide)).trans (hg b)
        rcases ih (g.toNat + 1 - out.cost) hlt
            (σ := out.accounts) (k := out.k) (C := out.cost) (aw := out.aw) (q := out.free)
            (mem := out.mem) (c := out.cacheData) (s := out.stateData)
            (frame := out.frame') (evm := out.evm')
            (rd := out.rd) (hsource := out.source_state)
            (hf := out.contract_eq.trans hf) (hi := out.immutables_eq.trans hi)
            (hz := (out.locals_get "zeroForOne" (by decide)).trans hz)
            (hcget := out.cache_get) (hsget := out.state_get)
            (hslot := (out.locals_get "slot0Start" (by decide)).trans hslot)
            (hlimit := (out.locals_get "sqrtPriceLimitX96" (by decide)).trans hlimit)
            (hexact := (out.locals_get "exactInput" (by decide)).trans hexact)
            (hg := hg2) (hm := out.heap) (hc := out.cache_mem) (hs := out.state_mem)
            (hsnap := out.snapshot) (hcf := out.cache_fits) (hsf := out.state_fits)
            (hpq := hpq2) (hbudget := hbudget2) (hcover := out.cover) (hfuel := rfl) with
          hoog | (⟨hex, hr⟩ | ⟨rest⟩)
        · exact Or.inl hoog
        · exact Or.inr (Or.inl ⟨ExecStmt.whileTrue he out.source hex, hr⟩)
        · rcases rest with ⟨rest⟩
          have hcost3 := rest.cost_bound
          have hfree2 := out.free_mono
          have hfree3 := rest.free_mono
          exact Or.inr (Or.inr ⟨{rest with
            source := ExecStmt.whileTrue he out.source rest.source
            contract_eq := rest.contract_eq.trans out.contract_eq
            immutables_eq := rest.immutables_eq.trans out.immutables_eq
            locals_get := fun name hn ↦ (rest.locals_get name hn).trans (out.locals_get name hn)
            memory_prefix := out.memory_prefix.trans rest.memory_prefix
            free_mono := by omega, cost_bound := by omega }⟩)

end Benchmarks.UniswapV3.Pool
