import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideFinish
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleChoice
import Benchmarks.UniswapV3.Pool.ModifyPositionMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState modifyPositionMiddleOracleState
  modifyPositionMiddleStoresState modifyPositionMiddleFinalState

theorem modifyPositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16233⟩ (q :: ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hq : ModifyPositionParamsMemory mem q a)
    (hqlo : 96 ≤ q.toNat) (hqp : q.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 1210 ≤ 2 ^ 200) (hperm : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 50 ≤ 1024) :
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ModifyPositionSuccess v a evm s0 ee g ret R mem p rdata := by
  rcases modifyPositionPrefixX (v := v) a evm hs rd ha hm hq hqlo hqp (by omega) hov with
    hbad | hstatic | ⟨ht, hprefix, σ1, aw1, k1, C1, hs1, r1, hm1, hq1, hp1⟩
  · exact Or.inl hbad
  · exact Or.inr (Or.inl hstatic)
  · have hpflo := modifyPositionPrefixFree_lower p a evm (by omega)
    have hpfhi := modifyPositionPrefixFree_bound p a evm (by omega)
    have hmemory := modifyPositionPrefixMemory_prefix mem p v a evm (by omega)
    obtain ⟨aw2, k2, C2, r2, hm2⟩ := modifyPositionNonzeroX (v := v) a r1 ha hm1 hq1
      (by omega) (by evm_ov)
    by_cases hz : a.delta = 0
    · rw [if_pos hz] at r2
      refine Or.inr (Or.inr ?_)
      exact modifyPositionFinishX (v := v) a evm (modifyPositionUpdatedState v a evm)
        (modifyPositionUpdatedFrame (immStore v) a evm) 0 0 hprefix
        (modifyPositionZeroTailSource (immStore v) a evm _ hz) hs1 r2
        (by norm_num) (by norm_num) hm2 (by omega) hmemory hret (by omega)
    · rw [if_neg hz] at r2
      obtain ⟨aw3, k3, C3, r3, hm3⟩ := modifyPositionRangeX (v := v) a evm false r2 ha hm2 hq1 hp1
        (by omega) (by omega) (by evm_ov)
      simp only [Bool.false_eq_true, if_false] at r3
      by_cases hlo : slot0TickValue evm.accountMap evm.executionEnv < a.lower
      · rw [if_pos hlo] at r3
        rcases modifyPositionOutsideFinishX (v := v) a evm false hprefix hs1 r3 ha ht hz hlo hm3 hq1
          (by omega) (by omega) hmemory hret (by omega) with ⟨hsr, rr⟩ | hok
        · exact Or.inl ⟨hsr, Or.inl rr⟩
        · exact Or.inr (Or.inr hok)
      · rw [if_neg hlo] at r3
        obtain ⟨aw4, k4, C4, r4, hm4⟩ := modifyPositionRangeX (v := v) a evm true r3 ha hm3 hq1 hp1
          (by omega) (by omega) (by evm_ov)
        simp only [if_true] at r4
        by_cases hhi : slot0TickValue evm.accountMap evm.executionEnv < a.upper
        · rw [if_pos hhi] at r4
          have hfree : (modifyPositionPrefixFree p a evm).toNat + 384 ≤ 2 ^ 200 := by omega
          rcases modifyPositionMiddleX (v := v) a evm hs1 r4 ha ht hm4 hq1 hp1
            (by have h := hm.lower; omega) hqlo hpflo (by omega) hfree hperm (by evm_ov) with
              ⟨hsrc, rr⟩ | ⟨hsrc, rr⟩ | ⟨hsrc, hv0, hv1, σ5, aw5, k5, C5, hs5, r5, hm5⟩
          · refine Or.inl ⟨?_, rr⟩
            apply ExecFuncBody.execBlockRevert
            rw [← List.take_append_drop 8 modifyPositionFunction.body]
            apply execBlock_append_ok hprefix
            exact ExecBlock.consRevert (modifyPositionMiddleChoiceSource v a evm .reverted hz
              (by omega) hhi hsrc)
          · refine Or.inr (Or.inl ⟨?_, rr⟩)
            apply ExecFuncBody.execBlockStatic
            rw [← List.take_append_drop 8 modifyPositionFunction.body]
            apply execBlock_append_ok hprefix
            exact ExecBlock.consStatic (modifyPositionMiddleChoiceSource v a evm .staticViolation hz
              (by omega) hhi hsrc)
          · have hchoice := modifyPositionMiddleChoiceSource v a evm _ hz (by omega) hhi hsrc
            have htail := ExecBlock.consNormal hchoice (ExecBlock.consReturn
              (modifyPositionMiddleReturnSource v a evm (modifyPositionMiddleFinalState v a evm))
              (stmts := []))
            have hf := modifyPositionMiddleFree_bounds (modifyPositionPrefixFree p a evm) v a evm hfree
            have hmem := hmemory.trans ((modifyPositionMiddleMemory_prefix
              (modifyPositionPrefixMemory mem p v a evm) (modifyPositionPrefixFree p a evm) v a evm hfree).mono
                (by omega : p.toNat ≤ (modifyPositionPrefixFree p a evm).toNat))
            refine Or.inr (Or.inr ?_)
            exact modifyPositionFinishX (v := v) a evm (modifyPositionMiddleFinalState v a evm)
              (modifyPositionMiddleFinalFrame v a evm)
              (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false))
              (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)) hprefix htail hs5 r5
              (signedAmountDeltaResult_bounds false _ (modifyPositionMiddleAmountArgs_fits a evm false ha) hv0)
              (signedAmountDeltaResult_bounds true _ (modifyPositionMiddleAmountArgs_fits a evm true ha) hv1)
              hm5 (by omega) hmem hret (by omega)
        · rw [if_neg hhi] at r4
          rcases modifyPositionOutsideFinishX (v := v) a evm true hprefix hs1 r4 ha ht hz
            (by change a.upper ≤ slot0TickValue evm.accountMap evm.executionEnv; omega) hm4 hq1
            (by omega) (by omega) hmemory hret (by omega) with ⟨hsr, rr⟩ | hok
          · exact Or.inl ⟨hsr, Or.inl rr⟩
          · exact Or.inr (Or.inr hok)

end Benchmarks.UniswapV3.Pool
