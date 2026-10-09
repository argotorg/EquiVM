import Benchmarks.CompoundIII.Comet.AccrueThenSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem accrue_block (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    internalBlockResult config (accrueEntry v) evm accrueCallable.body (accrueOutcome v evm) := by
  let time := timestampWord evm.executionEnv
  let last := lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
  let elapsed := accrueElapsed evm
  let f0 := accrueEntry v
  let f1 : Frame := { f0 with locals := f0.locals.insert "now_" (.int time.toNat) }
  let f2 := accrueTimeFrame v elapsed time
  by_cases ht : time.toNat < 2^40
  · apply internalBlockResult.prepend (now_call_ok f0 evm "now_" rfl ht)
    have he : evalExpr? config f1 evm (.var "now_") = .ok (.int time.toNat) := by
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    have hl : evalExpr? config f1 evm (.storage ⟨"lastAccrualTime", []⟩) =
        .ok (.int last.toNat) :=
      evalLastAccrual evm f1.locals (immStore v) (by simp [f1, f0, accrueEntry])
    by_cases hle : last.toNat ≤ time.toNat
    · have hv : AccrueTimeValid evm := ⟨ht, hle⟩
      have hd := checkedNarrowSubSourceOk ⟨40, by decide⟩ he hl ht hle
      have hdt : elapsed.toNat < 2^40 := currentElapsed_lt ht hle
      have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hd
      rw [normalizeInt_uint256_word] at hcast
      apply internalBlockResult.prepend (ExecStmt.letDecl hcast)
      have het : evalExpr? config f2 evm (.var "timeElapsed") = .ok (.int elapsed.toNat) := by
        simp only [evalExpr?, f2, accrueTimeFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      have hcond : evalExpr? config f2 evm (.binary .gt (.var "timeElapsed") (.intLit 0)) =
          .ok (.bool (decide (0 < elapsed.toNat))) := by
        simp only [evalExpr?, het, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
        simp
      dsimp only [elapsed] at hcond
      by_cases hz : accrueElapsed evm = ⟨0⟩
      · simp only [accrueOutcome, if_pos hv, if_pos hz]
        have hnot : ¬ 0 < (accrueElapsed evm).toNat := by rw [hz]; decide
        have hf : evalExpr? config f2 evm (.binary .gt (.var "timeElapsed") (.intLit 0)) =
            .ok (.bool false) := hcond.trans (by rw [decide_eq_false hnot])
        exact ⟨f2, ExecBlock.consNormal (ExecStmt.iteFalse hf ExecBlock.nil) ExecBlock.nil⟩
      · have hpos : 0 < (accrueElapsed evm).toNat := by
          by_contra h
          exact hz (uint256_toNat_eq_zero (by omega))
        rw [decide_eq_true hpos] at hcond
        simp only [accrueOutcome, if_pos hv, if_neg hz]
        exact internalBlockResult.iteTrue hcond (accrueThen_source v evm elapsed time hdt)
    · have hv : ¬ AccrueTimeValid evm := fun h ↦ hle h.2
      simp only [accrueOutcome, if_neg hv]
      have hd := checkedNarrowSubSourceUnderflow ⟨40, by decide⟩ he hl (Nat.lt_of_not_ge hle)
      apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
      change evalExpr? config f1 evm _ = _
      simp only [evalExpr?, hd, bind, EvalResult.bind]
  · have hv : ¬ AccrueTimeValid evm := fun h ↦ ht h.1
    simp only [accrueOutcome, if_neg hv]
    exact ExecBlock.consRevert (now_call_revert f0 evm "now_" rfl ht)

theorem accrue_source (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    internalSourceResult config (accrueEntry v) evm accrueCallable.body (accrueOutcome v evm) :=
  (accrue_block v evm).toSource

theorem accrue_call (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v) :
    ExecStmt config frame evm (.internalCall "accrueInternal" [] ret)
      (internalStmtResult frame ret (accrueOutcome v evm)) := by
  apply internalVoidCall (callee := accrueCallable) (locals := ∅) (argVals := [])
    rfl (by rw [hc]; exact accrueCallable_lookup) rfl
  simpa only [hc, hi] using accrue_source v evm

end Benchmarks.CompoundIII.Comet
