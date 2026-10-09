import Benchmarks.CompoundIII.Comet.ReentrancyStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem reentrancyWrite_source (frame : Frame) (evm : EVM.State) (enter : Bool)
    (hc : frame.contract = contract) (hl : frame.locals.get? "__reentrancyGuard" = none) :
    internalBlockResult config frame evm [reentrancyWriteStmt enter]
      (reentrancyWriteOutcome evm enter) := by
  have he : evalExpr? config frame evm (.intLit (if enter then 1 else 0)) =
      .ok (.int (reentrancyValue enter).toNat) := by
    cases enter <;> simp only [evalExpr?, pure, reentrancyValue, Bool.false_eq_true,
      if_false, if_true] <;> rfl
  have hw := assignReentrancy frame evm enter hc hl
  cases hp : evm.executionEnv.perm
  · simp only [reentrancyWriteOutcome, hp, Bool.false_eq_true, if_false, internalBlockResult]
    exact ExecBlock.consStatic (ExecStmt.assignStatic he hw hp)
  · simp only [reentrancyWriteOutcome, hp, if_true, internalBlockResult]
    exact ⟨frame, ExecBlock.consNormal (ExecStmt.assign he hw) .nil⟩

theorem reentrancy_source (imms : Store) (evm : EVM.State) (enter : Bool) :
    internalSourceResult config { contract := contract, locals := ∅, immutables := imms }
      evm (reentrancyCallable enter).body (reentrancyOutcome evm enter) := by
  apply internalBlockResult.toSource
  cases enter
  · exact reentrancyWrite_source _ evm false rfl (by simp)
  · let frame : Frame := { contract := contract, locals := ∅, immutables := imms }
    let ready := { frame with locals := frame.locals.insert "status" (.int (reentrancyWord evm).toNat) }
    have hr := evalReentrancy frame evm rfl (by simp [frame])
    have he : evalExpr? config ready evm (.var "status") =
        .ok (.int (reentrancyWord evm).toNat) := by
      simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hg : evalExpr? config ready evm (.binary .ne (.var "status") (.intLit 1)) =
        .ok (.bool (decide ((reentrancyWord evm).toNat ≠ 1))) := by
      simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
      have hcmp : (Value.int (reentrancyWord evm).toNat == Value.int 1) =
          decide ((reentrancyWord evm).toNat = 1) := by
        apply Bool.eq_iff_iff.mpr
        simp
      rw [hcmp]
      simp
    by_cases hlocked : (reentrancyWord evm).toNat = 1
    · simp only [reentrancyOutcome, hlocked, decide_true, Bool.and_self, if_true]
      exact ExecBlock.consNormal (ExecStmt.letDecl hr)
        (ExecBlock.consRevert (ExecStmt.requireFalse (hg.trans (by simp [hlocked]))))
    · simp only [reentrancyOutcome, hlocked, decide_false, Bool.and_false, Bool.false_eq_true,
        if_false]
      exact ((reentrancyWrite_source ready evm true rfl (by
          simp [ready, frame])).prepend (ExecStmt.requireTrue
            (hg.trans (by rw [decide_eq_true hlocked])))).prepend (ExecStmt.letDecl hr)

theorem reentrancy_call (frame : Frame) (evm : EVM.State) (enter : Bool) (ret : Ident)
    (hc : frame.contract = contract) :
    ExecStmt config frame evm (.internalCall (reentrancyName enter) [] ret)
      (internalStmtResult frame ret (reentrancyOutcome evm enter)) := by
  apply internalVoidCall (callee := reentrancyCallable enter) (locals := ∅) (argVals := [])
    rfl (by rw [hc]; exact reentrancyCallable_lookup enter) rfl
  simpa only [hc] using reentrancy_source frame.immutables evm enter

end Benchmarks.CompoundIII.Comet
