import Benchmarks.UniswapV3.Pool.SwapCrossFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossBranchX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3672⟩
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
    (ExecBlock config frame evm swapCrossBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapTailExit v ee g s0 rdata ⟨3993⟩ q p cache
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      d swapCrossBody frame evm mem aw free C) := by
  have he := evalExpr_structField (name := "initialized")
    (evalExpr_var_get (cfg := config) (evm := evm) hdget) rfl
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapInitializedGuardX (v := v) d rd hm hd (by omega)
      (by change R.length + 13 + 3 ≤ 1024; omega)
  have hbudget1 := hbudget.advance (show C + (Cₘ aw1 - Cₘ aw) ≤ C1 by omega)
  have hcover1 : free.toNat ≤ aw1.toNat * 32 + 32 := by omega
  have hhead :
      (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
      (ExecStmt config frame evm swapCrossBody[0]! .reverted ∧
        (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
      Nonempty (SwapTailExit v ee g s0 rdata ⟨3893⟩ q p cache
        (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        d [swapCrossBody[0]!] frame evm mem aw free C) := by
    cases hinit : d.initialized
    · simp only [hinit, Bool.false_eq_true, if_false] at r1
      change evalExpr? config frame evm (.field (.var "step") "initialized") =
        .ok (.bool d.initialized) at he
      rw [hinit] at he
      exact Or.inr (Or.inr ⟨{
        cacheData := c, stateData := s, frame' := frame, evm' := evm, accounts := σ
        mem := mem, aw := aw1, free := free, k := k1, cost := C1
        source := ExecBlock.consNormal (ExecStmt.iteFalse he .nil) .nil
        source_state := hsource, contract_eq := rfl, immutables_eq := rfl
        cache_get := hcget, state_get := hsget, locals_get := fun _ _ ↦ rfl
        cache_fits := hcf, state_fits := hsf
        rd := r1, heap := hm1, cache_mem := hc, state_mem := hs, step_mem := hd
        memory_prefix := MemoryPrefix.refl _ _, free_mono := le_refl _, cover := hcover1
        cost_bound := hC1 }⟩)
    · simp only [hinit, if_true] at r1
      change evalExpr? config frame evm (.field (.var "step") "initialized") =
        .ok (.bool d.initialized) at he
      rw [hinit] at he
      rcases swapInitializedX (v := v) a c s d initial frame evm r1 hsource hf hi hz hcget
          hsget hdget hslot hg hm1 hc hs hd hsnap hcf hsf ht hperm hcache hsnapc hcp hpq
          hqfree hb hbudget1 hallowance hcover1 hov with hoog | (⟨hex, hr⟩ | ⟨out⟩)
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue he hex, hr⟩)
      · rcases out with ⟨out⟩
        have hC2 := out.cost_bound
        exact Or.inr (Or.inr ⟨{out with
          source := ExecBlock.consNormal (ExecStmt.iteTrue he out.source) .nil
          cost_bound := by omega }⟩)
  rcases hhead with hoog | (⟨hex, hr⟩ | ⟨out⟩)
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hex, hr⟩)
  · rcases out with ⟨out⟩
    exact Or.inr (Or.inr (swapCrossFinishX a d frame evm out hz hdget ht hcache hcp hpq
      (by omega) (by omega)))

end Benchmarks.UniswapV3.Pool
