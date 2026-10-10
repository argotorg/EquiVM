import Benchmarks.CompoundIII.Comet.AssetMembershipWriteSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem assetMembershipCond_eval (evm : EVM.State) (imms : Store)
    (account : AccountAddress) (out : ByteArray) (initial final : UInt256) (add : Bool) :
    evalExpr? config (assetMembershipEntry imms account out initial final) evm
      (assetMembershipCond add) = .ok (.bool
        (if add then decide (initial = ⟨0⟩ ∧ final ≠ ⟨0⟩)
          else decide (initial ≠ ⟨0⟩ ∧ final = ⟨0⟩))) := by
  have hz (w : UInt256) : (Int.ofNat w.toNat = 0) ↔ w = ⟨0⟩ := by
    constructor
    · intro h
      change (w.toNat : Int) = 0 at h
      exact u256_inj (by change w.toNat = 0; omega)
    · rintro rfl; rfl
  have hi : evalExpr? config (assetMembershipEntry imms account out initial final) evm
      (.var "initialUserBalance") = .ok (.int initial.toNat) := by
    simp only [evalExpr?, assetMembershipEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hf : evalExpr? config (assetMembershipEntry imms account out initial final) evm
      (.var "finalUserBalance") = .ok (.int final.toNat) := by
    simp only [evalExpr?, assetMembershipEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hbool (w : UInt256) : ((Value.int w.toNat) == .int 0) = decide (w = ⟨0⟩) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
    exact hz w
  cases add <;>
    simp only [assetMembershipCond, Bool.false_eq_true, if_false, if_true, evalExpr?,
      hi, hf, pure, bind, EvalResult.bind, evalBinaryOp?]
  all_goals
    simp only [hbool]
    by_cases hx : initial = ⟨0⟩ <;> simp [hx]

theorem assetMembership_source (evm : EVM.State) (imms : Store)
    (account : AccountAddress) (out : ByteArray) (initial final : UInt256)
    (ho : (calldataWord out 0).toNat < 2^8) :
    internalSourceResult config (assetMembershipEntry imms account out initial final) evm
      assetMembershipCallable.body
      (assetMembershipResult evm account (calldataWord out 0) initial final) := by
  let frame := assetMembershipEntry imms account out initial final
  have hwrite (add : Bool) := assetMembershipWrite_source frame evm account
    (calldataWord out 0) add rfl (by simp [frame, assetMembershipEntry])
    (by simp only [evalExpr?, frame, assetMembershipEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl) ho
    (by simp only [assetMembershipOffset, evalExpr?, frame, assetMembershipEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
        bind, EvalResult.bind, assetValue, lookupField?]; rfl)
  have hyes := assetMembershipCond_eval evm imms account out initial final true
  have hno := assetMembershipCond_eval evm imms account out initial final false
  simp only [if_true] at hyes
  simp only [Bool.false_eq_true, if_false] at hno
  apply internalBlockResult.toSource
  by_cases hi : initial = ⟨0⟩
  · by_cases hf : final = ⟨0⟩
    · rw [decide_eq_false (show ¬ (initial = ⟨0⟩ ∧ final ≠ ⟨0⟩) from fun h ↦ h.2 hf)] at hyes
      rw [decide_eq_false (show ¬ (initial ≠ ⟨0⟩ ∧ final = ⟨0⟩) from fun h ↦ h.1 hi)] at hno
      simp only [assetMembershipResult, assetMembershipChange, if_pos hi, if_pos hf]
      apply internalBlockResult.iteFalse hyes
      apply internalBlockResult.iteFalse hno
      exact ⟨frame, ExecBlock.nil⟩
    · rw [decide_eq_true (And.intro hi hf)] at hyes
      simp only [assetMembershipResult, assetMembershipChange, if_pos hi, if_neg hf]
      exact internalBlockResult.iteTrue hyes (hwrite true)
  · rw [decide_eq_false (show ¬ (initial = ⟨0⟩ ∧ final ≠ ⟨0⟩) from fun h ↦ hi h.1)] at hyes
    apply internalBlockResult.iteFalse hyes
    by_cases hf : final = ⟨0⟩
    · rw [decide_eq_true (And.intro hi hf)] at hno
      simp only [assetMembershipResult, assetMembershipChange, if_neg hi, if_pos hf]
      exact internalBlockResult.iteTrue hno (hwrite false)
    · rw [decide_eq_false (show ¬ (initial ≠ ⟨0⟩ ∧ final = ⟨0⟩) from fun h ↦ hf h.2)] at hno
      simp only [assetMembershipResult, assetMembershipChange, if_neg hi, if_neg hf]
      apply internalBlockResult.iteFalse hno
      exact ⟨frame, ExecBlock.nil⟩

theorem assetMembership_call (frame : Frame) (evm : EVM.State) (account : AccountAddress)
    (out : ByteArray) (initial final : UInt256) (accountExpr assetExpr initialExpr finalExpr : Expr)
    (ret : Ident) (hc : frame.contract = contract) (ho : (calldataWord out 0).toNat < 2^8)
    (ha : evalExpr? config frame evm accountExpr = .ok (.address account))
    (hs : evalExpr? config frame evm assetExpr = .ok (assetValue out))
    (hi : evalExpr? config frame evm initialExpr = .ok (.int initial.toNat))
    (hf : evalExpr? config frame evm finalExpr = .ok (.int final.toNat)) :
    ExecStmt config frame evm
      (.internalCall "updateAssetsIn" [accountExpr, assetExpr, initialExpr, finalExpr] ret)
      (internalStmtResult frame ret
        (assetMembershipResult evm account (calldataWord out 0) initial final)) := by
  apply internalVoidCall (callee := assetMembershipCallable)
    (locals := (assetMembershipEntry frame.immutables account out initial final).locals)
    (argVals := [.address account, assetValue out, .int initial.toNat, .int final.toNat])
  · simp only [evalExprs?, ha, hs, hi, hf, pure, bind, EvalResult.bind]
  · rw [hc]; exact assetMembershipCallable_lookup
  · rfl
  · simpa only [hc] using assetMembership_source evm frame.immutables account out initial final ho

end Benchmarks.CompoundIII.Comet
