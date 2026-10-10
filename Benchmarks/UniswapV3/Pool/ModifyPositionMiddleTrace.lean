import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleOracleTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleStoresTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleFinalTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState modifyPositionMiddleOracleState
  modifyPositionMiddleStoresState oracleWriteResultIndex oracleWriteResultCardinality

theorem modifyPositionMiddleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (modifyPositionUpdatedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨16536⟩
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hplo : 96 ≤ p.toNat) (hqlo : 96 ≤ q.toNat)
    (hphi : p.toNat + 224 ≤ free.toNat) (hqhi : q.toNat + 128 ≤ free.toNat)
    (hb : free.toNat + 384 ≤ 2 ^ 200) (hperm : ee.perm = true) (hov : R.length + 42 ≤ 1024) :
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionMiddleBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionMiddleBody .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionMiddleBody
      (.ok (modifyPositionMiddleFinalFrame v a evm) (modifyPositionMiddleFinalState v a evm)) ∧
      signedAmountDeltaValid false (modifyPositionMiddleAmountArgs a evm false) ∧
      signedAmountDeltaValid true (modifyPositionMiddleAmountArgs a evm true) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionMiddleFinalState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨16801⟩
        (p :: EVM.wordOfInt (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)) ::
          EVM.wordOfInt (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)) ::
          key :: q :: R) (modifyPositionMiddleMemory mem free v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (modifyPositionMiddleMemory mem free v a evm) aw' (modifyPositionMiddleFree free v a evm)) := by
  rcases modifyPositionMiddleOracleX (v := v) a evm hs rd hm hq hp hplo hqlo hphi hqhi hb (by omega) with
    ⟨hsrc, rr⟩ | ⟨hsrc, rr⟩ | ⟨hsrc, _, σ1, aw1, k1, C1, hs1, r1, hm1, hq1, hp1⟩
  · refine Or.inl ⟨?_, Or.inr rr⟩
    rw [← List.take_append_drop 3 modifyPositionMiddleBody]
    exact execBlock_append_term hsrc (by intro _ _ h; cases h)
  · refine Or.inr (Or.inl ⟨?_, rr⟩)
    rw [← List.take_append_drop 3 modifyPositionMiddleBody]
    exact execBlock_append_term hsrc (by intro _ _ h; cases h)
  · obtain ⟨σ2, aw2, k2, C2, hs2, r2, hm2⟩ := modifyPositionMiddleStoresX (v := v) a evm hs1 r1
      hm1 hq1 hp1 (by omega) (by omega) hperm (by omega)
    have hs5 : ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
        (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 5)
        (.ok (modifyPositionMiddleOracleFrame v a evm) (modifyPositionMiddleStoresState v a evm)) :=
      execBlock_append_ok hsrc (modifyPositionMiddleStoresSource v a evm)
    rcases modifyPositionMiddleAmountX (v := v) a evm (modifyPositionMiddleStoresState v a evm) false
      r2 ha ht hm2 hq1 hp1 (by omega) (by omega) hov with
        ⟨hsrc0, rr⟩ | ⟨hsrc0, hv0, aw3, k3, C3, r3, hm3⟩
    · refine Or.inl ⟨?_, Or.inl rr⟩
      rw [← List.take_append_drop 5 modifyPositionMiddleBody]
      apply execBlock_append_ok hs5
      change ExecBlock config _ _ (modifyPositionMiddleAmountBody false ++ modifyPositionMiddleBody.drop 8) _
      exact execBlock_append_term hsrc0 (by intro _ _ h; cases h)
    · have hs8 : ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
          (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 8)
          (.ok (modifyPositionMiddleAssigned0Frame v a evm) (modifyPositionMiddleStoresState v a evm)) :=
        execBlock_append_ok hs5 hsrc0
      obtain ⟨aw4, k4, C4, r4, hm4⟩ := modifyPositionMiddleLowerEntryX (v := v) a r3 hm3 hq1
        (by omega) (by omega)
      rcases modifyPositionMiddleAmountX (v := v) a evm (modifyPositionMiddleStoresState v a evm) true
        r4 ha ht hm4 hq1 hp1 (by omega) (by omega) hov with
          ⟨hsrc1, rr⟩ | ⟨hsrc1, hv1, aw5, k5, C5, r5, hm5⟩
      · refine Or.inl ⟨?_, Or.inl rr⟩
        rw [← List.take_append_drop 8 modifyPositionMiddleBody]
        apply execBlock_append_ok hs8
        change ExecBlock config _ _ (modifyPositionMiddleAmountBody true ++ modifyPositionMiddleBody.drop 11) _
        exact execBlock_append_term hsrc1 (by intro _ _ h; cases h)
      · have hs11 : ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
            (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 11)
            (.ok (modifyPositionMiddleAssigned1Frame v a evm) (modifyPositionMiddleStoresState v a evm)) :=
          execBlock_append_ok hs8 hsrc1
        rcases modifyPositionMiddleFinalX (v := v) a evm hs2 r5 ha hm5 hq1 (by omega) hperm (by omega) with
          ⟨hfinal, rr⟩ | ⟨hfinal, σ6, aw6, k6, C6, hs6, r6, hm6⟩
        · refine Or.inl ⟨?_, Or.inl rr⟩
          rw [← List.take_append_drop 11 modifyPositionMiddleBody]
          exact execBlock_append_ok hs11 hfinal
        · refine Or.inr (Or.inr ⟨?_, hv0, hv1, σ6, aw6, k6, C6, hs6, r6, hm6⟩)
          rw [← List.take_append_drop 11 modifyPositionMiddleBody]
          exact execBlock_append_ok hs11 hfinal

end Benchmarks.UniswapV3.Pool
