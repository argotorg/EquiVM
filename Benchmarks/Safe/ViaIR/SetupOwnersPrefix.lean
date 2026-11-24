import Benchmarks.Safe.ViaIR.SetupOwnersContext

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

theorem safeSetupOwnersThreshold (p : SetupOwnersInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (.var "_threshold") = .ok (uint256Value p.threshold) :=
  evalLocalValue (by simp [SetupOwnersInput.frame, SetupOwnersInput.args,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safeSetupOwnersLength (p : SetupOwnersInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (localLength "_owners") =
      .ok (.int (Int.ofNat p.owners.length)) := by
  have h := evalLocalArrayLength (cfg := config) (frame := p.frame) (evm := evm)
    (name := "_owners") (xs := p.owners.map addressArrayValue)
    (by simp [SetupOwnersInput.frame, SetupOwnersInput.args])
  simpa only [List.length_map] using h

theorem safeSetupOwnersUninitialized (p : SetupOwnersInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (eqE (.storage thresholdRef) (.intLit 0)) =
      .ok (.bool (decide ((storedThreshold evm).toNat = 0))) := by
  have h : evalExpr? config p.frame evm (.storage thresholdRef) =
      .ok (.int (Int.ofNat (storedThreshold evm).toNat)) :=
    safeEvalStoredThreshold evm p.args (by
      simp [SetupOwnersInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  rw [eqE, evalExpr_binary_nonshort (by decide) (by decide), h]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.natCast_eq_zero]

theorem safeSetupOwnersBound (p : SetupOwnersInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (leE (.var "_threshold") (localLength "_owners")) =
      .ok (.bool (decide (p.threshold.toNat ≤ p.owners.length))) := by
  rw [leE, evalExpr_binary_nonshort (by decide) (by decide),
    safeSetupOwnersThreshold, safeSetupOwnersLength]
  simp [uint256Value, evalBinaryOp?, EvalResult.bind, bind, pure, Int.ofNat_eq_natCast]

theorem safeSetupOwnersNonzero (p : SetupOwnersInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (neE (.var "_threshold") (.intLit 0)) =
      .ok (.bool (decide (p.threshold.toNat ≠ 0))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), safeSetupOwnersThreshold]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure, uint256Value]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.natCast_eq_zero]

theorem safeSetupOwnersPrefix (p : SetupOwnersInput) (evm : EVM.State) {result : ExecResult}
    (hz : (storedThreshold evm).toNat = 0) (hle : p.threshold.toNat ≤ p.owners.length)
    (hne : p.threshold.toNat ≠ 0)
    (htail : ExecBlock fork config { contract := contract, locals := p.loopLocals } evm
      (setupOwnersFunction.body.drop 6) result) :
    ExecBlock fork config p.frame evm setupOwnersFunction.body result := by
  refine .consNormal (.requireTrue (by
      simpa only [hz, decide_true] using safeSetupOwnersUninitialized p evm))
    (.consNormal (.requireTrue (by
      simpa only [hle, decide_true] using safeSetupOwnersBound p evm))
      (.consNormal (.requireTrue (by
        exact (safeSetupOwnersNonzero p evm).trans (by congr 2; exact decide_eq_true hne)))
        (.consNormal (.letDecl (safeEvalOwnerSentinel evm _))
          (.consNormal (.letDecl ?_) (.consNormal (.letDecl (by simp [evalExpr?, pure])) htail)))))
  have h := evalLocalArrayLength (cfg := config) (evm := evm)
    (frame := {
      contract := contract
      locals := p.args.insert "currentOwner" (addressArrayValue ⟨1⟩) })
    (name := "_owners") (xs := p.owners.map addressArrayValue) (by
      simp [SetupOwnersInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  simpa only [List.length_map] using h

theorem safeSetupOwnersAlreadyInitialized (p : SetupOwnersInput) (evm : EVM.State)
    (hz : (storedThreshold evm).toNat ≠ 0) :
    ExecFuncBody fork config p.frame evm setupOwnersFunction.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by
    simpa only [hz, decide_false] using safeSetupOwnersUninitialized p evm)))

theorem safeSetupOwnersThresholdTooLarge (p : SetupOwnersInput) (evm : EVM.State)
    (hz : (storedThreshold evm).toNat = 0) (hle : ¬p.threshold.toNat ≤ p.owners.length) :
    ExecFuncBody fork config p.frame evm setupOwnersFunction.body .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (by
      simpa only [hz, decide_true] using safeSetupOwnersUninitialized p evm))
    (.consRevert (.requireFalse (by
      simpa only [hle, decide_false] using safeSetupOwnersBound p evm))))

theorem safeSetupOwnersThresholdZero (p : SetupOwnersInput) (evm : EVM.State)
    (hz : (storedThreshold evm).toNat = 0) (hle : p.threshold.toNat ≤ p.owners.length)
    (hne : p.threshold.toNat = 0) :
    ExecFuncBody fork config p.frame evm setupOwnersFunction.body .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (by
      simpa only [hz, decide_true] using safeSetupOwnersUninitialized p evm))
    (.consNormal (.requireTrue (by
      simpa only [hle, decide_true] using safeSetupOwnersBound p evm))
      (.consRevert (.requireFalse (by
        simpa only [hne, ne_eq, not_true_eq_false, decide_false] using
          safeSetupOwnersNonzero p evm)))))

theorem safeInternalSetupOwners {caller : Frame} {evm : EVM.State}
    {owners threshold : Expr} {retVar : Ident} {p : SetupOwnersInput} {result : ExecResult}
    (hc : caller.contract = contract) (him : caller.immutables = ∅)
    (ho : evalExpr? config caller evm owners = .ok (.array (p.owners.map addressArrayValue)))
    (ht : evalExpr? config caller evm threshold = .ok (uint256Value p.threshold))
    (hb : ExecFuncBody fork config p.frame evm setupOwnersFunction.body result) :
    ExecStmt fork config caller evm (.internalCall "setupOwners" [owners, threshold] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := setupOwnersFunction) (locals := p.args)
    (argVals := [.array (p.owners.map addressArrayValue), uint256Value p.threshold])
  · simp only [evalExprs?, ho, ht, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc, him] using hb

end Benchmarks.Safe.ViaIR
