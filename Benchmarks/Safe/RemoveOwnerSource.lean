import Benchmarks.Safe.OwnerGuardTraces
import Benchmarks.Safe.ThresholdChange
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def removeOwnerArgs (prev key threshold : UInt256) : Store :=
  (((∅ : Store).insert "prevOwner" (.address (AccountAddress.ofNat prev.toNat))).insert
    "owner" (.address (AccountAddress.ofNat key.toNat))).insert
    "_threshold" (.int (Int.ofNat threshold.toNat))

def removeOwnerFrame (prev key threshold : UInt256) : Frame :=
  { contract := contract, locals := removeOwnerArgs prev key threshold }

def removeOwnerFrame₁ (prev key threshold : UInt256) : Frame :=
  resumeAfterInternalCall (removeOwnerFrame prev key threshold) "_ok" none

def removeOwnerCountState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (UInt256.sub (ownerCount evm) ⟨1⟩)

def removeOwnerLinks (evm : EVM.State) (prev key : UInt256) : EVM.State :=
  writeOwnerLink (writeOwnerLink evm prev (ownerLink evm key)) key ⟨0⟩

def removeOwnerTail : List Stmt :=
  [ .require (geE (.storage ownerCountRef) (.var "_threshold")),
    .internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "owner"] "_ok",
    .assign .storage (ownersRef (.var "prevOwner")) (.storage (ownersRef (.var "owner"))),
    .assign .storage (ownersRef (.var "owner")) zeroAddr,
    .emit "RemovedOwner" [.var "owner"], thresholdChangeStmt ]

theorem safeRemoveOwnerEvalThreshold (evm : EVM.State) (prev key threshold : UInt256) :
    evalExpr? config (removeOwnerFrame prev key threshold) evm (.var "_threshold") =
      .ok (.int (Int.ofNat threshold.toNat)) := by
  simp [removeOwnerFrame, removeOwnerArgs, evalExpr?, EvalResult.ofOption]

theorem safeRemoveOwnerLocal (prev key threshold : UInt256) (name : Ident)
    (hn : name ≠ "prevOwner" ∧ name ≠ "owner" ∧ name ≠ "_threshold") :
    (removeOwnerFrame prev key threshold).locals[name]? = none := by
  simp [removeOwnerFrame, removeOwnerArgs, Std.HashMap.getElem_insert,
    hn.1, hn.2.1, hn.2.2, Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2]

theorem safeRemoveOwnerDecrement (evm : EVM.State) (prev key threshold : UInt256)
    (hnz : ownerCount evm ≠ ⟨0⟩) :
    evalExpr? config (removeOwnerFrame prev key threshold) evm (dec256 (.storage ownerCountRef)) =
      .ok (.int (Int.ofNat (UInt256.sub (ownerCount evm) ⟨1⟩).toNat)) := by
  apply evalExpr_checkedSub256_ok
    (safeEvalOwnerCount evm _ (safeRemoveOwnerLocal prev key threshold "ownerCount" (by decide)))
    (b := ⟨1⟩) (by simp [evalExpr?]; rfl) rfl
  have hpos : (ownerCount evm).toNat ≠ 0 := fun hz ↦ hnz (uint256_toNat_eq_zero hz)
  change 1 ≤ (ownerCount evm).toNat
  omega

theorem safeRemoveOwnerPrefix (evm : EVM.State) (prev key threshold : UInt256) {result : ExecResult}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hnz : ownerCount evm ≠ ⟨0⟩)
    (htail : ExecBlock config (removeOwnerFrame prev key threshold) (removeOwnerCountState evm)
      removeOwnerTail result) :
    ExecBlock config (removeOwnerFrame prev key threshold) evm removeownerTransition.body
      result :=
  .consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.assign (safeRemoveOwnerDecrement evm prev key threshold hnz)
        (safeAssignOwnerCount evm _ _
          (safeRemoveOwnerLocal prev key threshold "ownerCount" (by decide)))) htail))

theorem safeRemoveOwnerUnderflow (evm : EVM.State) (prev key threshold : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hz : ownerCount evm = ⟨0⟩) :
    ExecTransitionBody config contract evm (removeOwnerArgs prev key threshold)
      removeownerTransition.body .reverted := by
  have he := evalExpr_checkedSub256_revert
    (safeEvalOwnerCount evm _ (safeRemoveOwnerLocal prev key threshold "ownerCount" (by decide)))
    (b := ⟨1⟩) (y := .intLit 1) (by simp [evalExpr?]; rfl) (by rw [hz]; decide)
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert (.assignExprRevert he))))

theorem safeRemoveOwnerStatic (evm : EVM.State) (prev key threshold : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hnz : ownerCount evm ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (removeOwnerArgs prev key threshold)
      removeownerTransition.body .staticViolation :=
  .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consStatic (.assignStatic (safeRemoveOwnerDecrement evm prev key threshold hnz)
        (safeAssignOwnerCount evm _ _
          (safeRemoveOwnerLocal prev key threshold "ownerCount" (by decide))) hperm))))

theorem safeRemoveOwnerCountGuard (evm : EVM.State) (prev key threshold : UInt256) :
    evalExpr? config (removeOwnerFrame prev key threshold) evm
      (geE (.storage ownerCountRef) (.var "_threshold")) =
      .ok (.bool (decide (threshold.toNat ≤ (ownerCount evm).toNat))) := by
  have he := safeEvalOwnerCount evm _
    (safeRemoveOwnerLocal prev key threshold "ownerCount" (by decide))
  change evalExpr? config (removeOwnerFrame prev key threshold) evm (.storage ownerCountRef) = _
    at he
  rw [geE, evalExpr_binary_nonshort (by decide) (by decide), he, safeRemoveOwnerEvalThreshold]
  simp [evalBinaryOp?, EvalResult.bind, bind, pure]

theorem safeRemoveOwnerCountTooSmall (evm : EVM.State) (prev key threshold : UInt256)
    (hle : ¬threshold.toNat ≤ (ownerCount evm).toNat) :
    ExecBlock config (removeOwnerFrame prev key threshold) evm removeOwnerTail .reverted :=
  .consRevert (.requireFalse (by
    simpa [hle] using safeRemoveOwnerCountGuard evm prev key threshold))

theorem safeRemoveOwnerCanRemove (evm : EVM.State) (prev key threshold : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner evm.accountMap evm.executionEnv key) (hl : ownerLink evm prev = key) :
    ExecStmt config (removeOwnerFrame prev key threshold) evm
      (.internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "owner"] "_ok")
      (.ok (removeOwnerFrame₁ prev key threshold) evm) := by
  apply internalCallFunctionReturn (callee := requireCanRemoveOwnerFunction)
    (argVals := [.address (AccountAddress.ofNat prev.toNat),
      .address (AccountAddress.ofNat key.toNat)]) (locals := canRemoveOwnerArgs prev key)
    (calleeSolm := canRemoveOwnerFrame prev key)
  · simp [removeOwnerFrame, removeOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact safeCanRemoveOwnerSource evm prev key hp hc hv hl

theorem safeRemoveOwnerGuardRevert (evm : EVM.State) (prev key threshold : UInt256)
    (hle : threshold.toNat ≤ (ownerCount evm).toNat)
    (hbody : ExecFuncBody config (canRemoveOwnerFrame prev key) evm
      requireCanRemoveOwnerFunction.body .reverted) :
    ExecBlock config (removeOwnerFrame prev key threshold) evm removeOwnerTail .reverted := by
  have hcall : ExecStmt config (removeOwnerFrame prev key threshold) evm
      (.internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "owner"] "_ok") .reverted := by
    apply internalCallFunctionRevert (callee := requireCanRemoveOwnerFunction)
      (argVals := [.address (AccountAddress.ofNat prev.toNat),
        .address (AccountAddress.ofNat key.toNat)]) (locals := canRemoveOwnerArgs prev key)
    · simp [removeOwnerFrame, removeOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
        EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
    · rfl
    · rfl
    · exact hbody
  exact .consNormal (.requireTrue (by
    simpa [hle] using safeRemoveOwnerCountGuard evm prev key threshold)) (.consRevert hcall)

theorem safeRemoveOwnerEval₁ (evm : EVM.State) (prev key threshold : UInt256) :
    evalExpr? config (removeOwnerFrame₁ prev key threshold) evm (.var "owner") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [removeOwnerFrame₁, removeOwnerFrame, removeOwnerArgs, resumeAfterInternalCall,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeRemoveOwnerEvalPrev₁ (evm : EVM.State) (prev key threshold : UInt256) :
    evalExpr? config (removeOwnerFrame₁ prev key threshold) evm (.var "prevOwner") =
      .ok (.address (AccountAddress.ofNat prev.toNat)) := by
  simp [removeOwnerFrame₁, removeOwnerFrame, removeOwnerArgs, resumeAfterInternalCall,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeRemoveOwnerEvalThreshold₁ (evm : EVM.State) (prev key threshold : UInt256) :
    evalExpr? config (removeOwnerFrame₁ prev key threshold) evm (.var "_threshold") =
      .ok (.int (Int.ofNat threshold.toNat)) := by
  simp [removeOwnerFrame₁, removeOwnerFrame, removeOwnerArgs, resumeAfterInternalCall,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeRemoveOwnerLocal₁ (prev key threshold : UInt256) (name : Ident)
    (hn : name ≠ "prevOwner" ∧ name ≠ "owner" ∧ name ≠ "_threshold" ∧ name ≠ "_ok") :
    (removeOwnerFrame₁ prev key threshold).locals[name]? = none := by
  simp [removeOwnerFrame₁, removeOwnerFrame, removeOwnerArgs, resumeAfterInternalCall,
    Std.HashMap.getElem_insert, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2,
    Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2.1, Ne.symm hn.2.2.2]

theorem safeRemoveOwnerLinksPrefix (evm : EVM.State) (prev key threshold : UInt256)
    {result : ExecResult}
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hle : threshold.toNat ≤ (ownerCount evm).toNat)
    (hv : validOwner evm.accountMap evm.executionEnv key) (hl : ownerLink evm prev = key)
    (ht : ExecStmt config (removeOwnerFrame₁ prev key threshold) (removeOwnerLinks evm prev key)
      thresholdChangeStmt result) :
    ExecBlock config (removeOwnerFrame prev key threshold) evm removeOwnerTail result := by
  have hb := safeRemoveOwnerLocal₁ prev key threshold "owners" (by decide)
  have hload := safeEvalOwnerLink evm _ _ key hb hc (safeRemoveOwnerEval₁ evm prev key threshold)
  have hfirst := safeAssignOwnerLink evm _ _ prev (ownerLink evm key) hb hp
    (solcAddrMask_result_canonical _) (safeRemoveOwnerEvalPrev₁ evm prev key threshold)
  have hsecond := safeAssignOwnerLink (writeOwnerLink evm prev (ownerLink evm key)) _ _ key ⟨0⟩
    hb hc (by decide) (safeRemoveOwnerEval₁ _ prev key threshold)
  exact .consNormal (.requireTrue (by
    simpa [hle] using safeRemoveOwnerCountGuard evm prev key threshold))
    (.consNormal (safeRemoveOwnerCanRemove evm prev key threshold hp hc hv hl)
      (.consNormal (.assign hload hfirst)
        (.consNormal (.assign (evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)) hsecond)
          (.consNormal (.emit (evalExprs?_singleton (safeRemoveOwnerEval₁ _ prev key threshold)))
            (execBlock_singleton ht)))))

theorem safeRemoveOwnerUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals removeownerTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

end Benchmarks.Safe
