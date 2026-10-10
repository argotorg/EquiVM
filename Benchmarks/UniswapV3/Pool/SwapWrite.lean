import Benchmarks.UniswapV3.Pool.SwapWriteStoreSource
import Benchmarks.UniswapV3.Pool.SwapWriteStoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapWriteWrites : List Ident :=
  ["__c16", "observationIndex", "observationCardinality", "__t17", "__t18", "__t19", "__t20"]

structure SwapWriteExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (rdata : ByteArray) (p cache snap : UInt256) (stack : List UInt256)
    (c : SwapCacheData) (s : SwapStateData) (initial : EVM.State)
    (frame : Frame) (evm : EVM.State) (initMem : ByteArray) (initFree : UInt256) where
  frame' : Frame
  evm' : EVM.State
  accounts : AccountMap
  mem : ByteArray
  aw : UInt256
  free : UInt256
  k : Nat
  cost : Nat
  source : ExecStmt config frame evm swapTransition.body[14]! (.ok frame' evm')
  source_state : SourceState s0 ee accounts evm'
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  locals_get : ∀ name, name ∉ swapWriteWrites → frame'.locals.get? name = frame.locals.get? name
  rd : RD (deployedRuntime v) ee g s0 ⟨4268⟩ stack mem aw rdata accounts k cost
  heap : HeapMemory mem aw free
  cache_mem : SwapCacheMemory mem cache c
  state_mem : SwapStateMemory mem p s
  snapshot : Slot0Memory mem snap initial.accountMap initial.executionEnv
  memory_prefix : MemoryPrefix initMem mem initFree.toNat
  free_mono : initFree.toNat ≤ free.toNat
  free_bound : free.toNat ≤ initFree.toNat + 384

theorem swapWriteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache snap exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3999⟩
      ([p, exactWord, cache, snap] ++ R) mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hbase : frame.locals.get? "slot0" = none)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hcf : c.Fits) (hsf : s.Fits) (hperm : ee.perm = true)
    (hsl : 96 ≤ snap.toNat) (hcache : 96 ≤ cache.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat) (hcp : cache.toNat + 192 ≤ p.toNat)
    (hpfree : p.toNat + 224 ≤ free.toNat) (hb : free.toNat + 384 ≤ 2 ^ 200)
    (hov : R.length + 33 ≤ 1024) :
    (ExecStmt config frame evm swapTransition.body[14]! .reverted ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    (ExecStmt config frame evm swapTransition.body[14]! .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    Nonempty (SwapWriteExit v ee g s0 rdata p cache snap
      ([p, exactWord, cache, snap] ++ R) c s initial frame evm mem free) := by
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapWriteGuardX (v := v) s initial rd hm hs hsnap hsf (by omega) (by omega) (by omega)
  have he := evalSwapWriteGuard (evm := evm) s initial hsget hslot
  by_cases ht : s.tick = slot0TickValue initial.accountMap initial.executionEnv
  · simp only [ht, if_true] at r1
    simp only [ht, ne_eq, not_true_eq_false, decide_false] at he
    have hassign : ExecStmt config frame evm
        (.assign .storage ⟨"slot0", [.field "sqrtPriceX96"]⟩
          (.field (.var "state") "sqrtPriceX96"))
        (.ok frame (swapSlotFieldState evm false s.price)) :=
      ExecStmt.assign
        (evalExpr_structField (name := "sqrtPriceX96") (evalExpr_var_get hsget) rfl)
        (by simpa only [wordOfInt_ofNat_toNat] using
          assignSwapSlotField_frame evm false (Int.ofNat s.price.toNat) hf hbase)
    obtain ⟨aw2, k2, C2, r2, hm2⟩ := swapPriceStoreX (v := v) s r1 hm1 hs hperm
      (by omega) (by change R.length + 3 + 7 ≤ 1024; omega)
    exact Or.inr (Or.inr ⟨{
      frame' := frame, evm' := swapSlotFieldState evm false s.price
      accounts := _, mem := mem, aw := aw2, free := free, k := k2, cost := C2
      source := ExecStmt.iteFalse he (ExecBlock.consNormal hassign .nil)
      source_state := SourceState.swapSlotField hsource false s.price
      contract_eq := rfl, immutables_eq := rfl, locals_get := fun _ _ ↦ rfl
      rd := r2, heap := hm2, cache_mem := hc, state_mem := hs, snapshot := hsnap
      memory_prefix := MemoryPrefix.refl _ _, free_mono := le_refl _, free_bound := by omega }⟩)
  · simp only [ht, if_false] at r1
    simp only [ht, ne_eq, not_false_eq_true, decide_true] at he
    rcases swapWriteCallX (v := v) c s initial frame evm r1 (frame_eq_of_parts hf hi)
        hcget hslot hsource hm1 hc hs hsnap hcf hsl hcache hsnapc hcp hpfree hb hov with
      ⟨hex, hr⟩ | (⟨hex, hr⟩ |
        ⟨hex, hv, σ2, aw2, k2, C2, hsrc2, r2, hm2, hc2, hs2, hsnap2, hpre2, hlo2, hhi2⟩)
    · exact Or.inl ⟨ExecStmt.iteTrue he (ExecBlock.consRevert hex), hr⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue he (ExecBlock.consStatic hex), hr⟩)
    · let a := swapWriteArgs c initial
      let index := oracleWriteResultIndex a evm
      let cardinality := oracleWriteResultCardinality a evm
      let f := swapWriteCallFrame frame a evm
      have hget (name : Ident) (hn : name ≠ "__c16") :
          f.locals.get? name = frame.locals.get? name :=
        resumeAfterInternalCall_get _ _ _ _ hn
      have hstores := swapWriteStoresSource (evm := oracleWriteState a evm) s index cardinality
        (show f.contract = contract from hf) ((hget "state" (by decide)).trans hsget)
        ((hget "slot0" (by decide)).trans hbase)
        (show f.locals.get? "__c16" = some (.tuple
          [.int (Int.ofNat index.toNat), .int (Int.ofNat cardinality.toNat)]) from
          Std.HashMap.getElem?_insert_self)
      obtain ⟨aw3, k3, C3, r3, hm3⟩ := swapWriteStoreX (v := v) s r2 hm2 hs2 hsf hperm
        (by omega) (by omega)
      have hparts := swapWriteStoreFrame_parts f s index cardinality
      refine Or.inr (Or.inr ⟨{
        frame' := swapWriteStoreFrame f s index cardinality
        evm' := swapSlotFieldsState (oracleWriteState a evm) s.price (EVM.wordOfInt s.tick)
          index cardinality
        accounts := _, mem := _, aw := aw3, free := _, k := k3, cost := C3
        source := ExecStmt.iteTrue he (ExecBlock.consNormal hex hstores)
        source_state := SourceState.swapSlotFields hsrc2 s.price (EVM.wordOfInt s.tick)
          index cardinality
        contract_eq := hparts.1, immutables_eq := hparts.2, locals_get := ?_
        rd := r3, heap := hm3, cache_mem := hc2, state_mem := hs2, snapshot := hsnap2
        memory_prefix := hpre2, free_mono := hlo2, free_bound := hhi2 }⟩)
      intro name hn
      change name ∉ "__c16" :: _ at hn
      have hn' : name ≠ "__c16" ∧ name ∉
          ["observationIndex", "observationCardinality", "__t17", "__t18", "__t19", "__t20"] := by
        simpa only [List.mem_cons, not_or] using hn
      exact (swapWriteStoreFrame_get f s index cardinality name hn'.2).trans (hget name hn'.1)

end Benchmarks.UniswapV3.Pool
