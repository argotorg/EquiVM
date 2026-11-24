import Benchmarks.Safe.V1_0227664.OwnerGuardTraces
import Benchmarks.Safe.V1_0227664.OwnerCount
import Benchmarks.Safe.V1_0227664.ThresholdChange

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V1_0227664

def addOwnerArgs (key threshold : UInt256) : Store :=
  ((∅ : Store).insert "owner" (.address (AccountAddress.ofNat key.toNat))).insert
    "_threshold" (.int (Int.ofNat threshold.toNat))

def addOwnerFrame (key threshold : UInt256) : Frame :=
  { contract := contract, locals := addOwnerArgs key threshold }

def addOwnerFrame₁ (key threshold : UInt256) : Frame :=
  resumeAfterInternalCall (addOwnerFrame key threshold) "_ok" none

def addOwnerLinks (evm : EVM.State) (key : UInt256) : EVM.State :=
  writeOwnerLink (writeOwnerLink evm key (ownerLink evm ⟨1⟩)) ⟨1⟩ key

def addOwnerCountState (evm : EVM.State) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (UInt256.add (ownerCount evm) ⟨1⟩)

def addOwnerTail : List Stmt :=
  [ .assign .storage ownerCountRef (inc256 (.storage ownerCountRef)),
    .emit "AddedOwner" [.var "owner"],
    .ite (neE (.storage thresholdRef) (.var "_threshold"))
      [.internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged"] [] ]

def addOwnerThresholdStmt : Stmt :=
  .ite (neE (.storage thresholdRef) (.var "_threshold"))
    [.internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged"] []

theorem safeAddOwnerEval (evm : EVM.State) (key threshold : UInt256) :
    evalExpr? config (addOwnerFrame₁ key threshold) evm (.var "owner") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [addOwnerFrame₁, addOwnerFrame, addOwnerArgs, resumeAfterInternalCall,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeAddOwnerEvalThreshold (evm : EVM.State) (key threshold : UInt256) :
    evalExpr? config (addOwnerFrame₁ key threshold) evm (.var "_threshold") =
      .ok (.int (Int.ofNat threshold.toNat)) := by
  simp [addOwnerFrame₁, addOwnerFrame, addOwnerArgs, resumeAfterInternalCall,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeAddOwnerLocal (key threshold : UInt256) (name : Ident)
    (hn : name ≠ "owner" ∧ name ≠ "_threshold" ∧ name ≠ "_ok") :
    (addOwnerFrame₁ key threshold).locals[name]? = none := by
  simp [addOwnerFrame₁, addOwnerFrame, addOwnerArgs, resumeAfterInternalCall,
    Std.HashMap.getElem_insert, hn.1, hn.2.1, hn.2.2,
    Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2]

theorem safeAddOwnerCanAdd (evm : EVM.State) (key threshold : UInt256)
    (hc : key.toNat < EVM.addressModulus) (hv : validOwner evm.accountMap evm.executionEnv key)
    (he : ownerLink evm key = ⟨0⟩) :
    ExecStmt fork config (addOwnerFrame key threshold) evm
      (.internalCall "requireCanAddOwner" [.var "owner"] "_ok")
      (.ok (addOwnerFrame₁ key threshold) evm) := by
  apply internalCallFunctionReturn (callee := requireCanAddOwnerFunction)
    (argVals := [.address (AccountAddress.ofNat key.toNat)])
    (locals := canAddOwnerArgs key) (calleeStele := canAddOwnerFrame key)
  · simp [addOwnerFrame, addOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact safeCanAddOwnerSource evm key hc hv he

theorem safeAddOwnerPrefix (evm : EVM.State) (key threshold : UInt256) {result : ExecResult}
    (hc : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hv : validOwner evm.accountMap evm.executionEnv key) (he : ownerLink evm key = ⟨0⟩)
    (htail : ExecBlock fork config (addOwnerFrame₁ key threshold) (addOwnerLinks evm key)
      addOwnerTail result)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config (addOwnerFrame key threshold) evm addownerwiththresholdTransition.body
      result := by
  have hb := safeAddOwnerLocal key threshold "owners" (by decide)
  have hload := safeEvalOwnerLink evm _ sentinelAddr ⟨1⟩ hb (by decide)
    (safeEvalOwnerSentinel evm _)
  have hfirst := safeAssignOwnerLink evm _ _ key (ownerLink evm ⟨1⟩) hb hc
    (solcAddrMask_result_canonical _) (safeAddOwnerEval evm key threshold)
  have hsecond := safeAssignOwnerLink (writeOwnerLink evm key (ownerLink evm ⟨1⟩))
    _ sentinelAddr ⟨1⟩ key hb (by decide) hc (safeEvalOwnerSentinel _ _)
  exact .consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (safeAddOwnerCanAdd evm key threshold hc hv he)
        (.consNormal (.assign (hperm := Or.inr hperm) hload hfirst)
          (.consNormal (.assign (hperm := Or.inr (by simpa only [writeOwnerLink, storageStore_executionEnv] using hperm)) (safeAddOwnerEval _ key threshold) hsecond) htail))))

theorem safeAddOwnerIncrement (evm : EVM.State) (key threshold : UInt256)
    (hno : (ownerCount evm).toNat + 1 < UInt256.size)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config (addOwnerFrame₁ key threshold) evm
      (.assign .storage ownerCountRef (inc256 (.storage ownerCountRef)))
      (.ok (addOwnerFrame₁ key threshold) (addOwnerCountState evm)) := by
  have hb := safeAddOwnerLocal key threshold "ownerCount" (by decide)
  exact .assign (hperm := Or.inr hperm) (checkedAddSourceOk (safeEvalOwnerCount evm _ hb)
      (b := ⟨1⟩) (by simp [evalExpr?]; rfl) hno) (safeAssignOwnerCount evm _ _ hb)

theorem safeAddOwnerIncrementOverflow (evm : EVM.State) (key threshold : UInt256)
    (hno : ¬(ownerCount evm).toNat + 1 < UInt256.size) :
    ExecBlock fork config (addOwnerFrame₁ key threshold) evm addOwnerTail .reverted :=
  .consRevert (.assignExprRevert (checkedAddSourceOverflow
    (safeEvalOwnerCount evm _ (safeAddOwnerLocal key threshold "ownerCount" (by decide)))
    (b := ⟨1⟩) (by simp [evalExpr?]; rfl) (by change UInt256.size ≤ _ + 1; omega)))

theorem safeAddOwnerThresholdGuard (evm : EVM.State) (key threshold : UInt256) :
    evalExpr? config (addOwnerFrame₁ key threshold) evm
      (neE (.storage thresholdRef) (.var "_threshold")) =
      .ok (.bool (decide (storedThreshold evm ≠ threshold))) :=
  safeThresholdChangeGuard evm _ threshold
    (safeAddOwnerLocal key threshold "threshold" (by decide))
    (safeAddOwnerEvalThreshold evm key threshold)

theorem safeAddOwnerThresholdUnchanged (evm : EVM.State) (key threshold : UInt256)
    (ht : storedThreshold evm = threshold) :
    ExecStmt fork config (addOwnerFrame₁ key threshold) evm addOwnerThresholdStmt
      (.ok (addOwnerFrame₁ key threshold) evm) :=
  safeThresholdChangeUnchanged evm _ threshold
    (safeAddOwnerLocal key threshold "threshold" (by decide))
    (safeAddOwnerEvalThreshold evm key threshold) ht

theorem safeAddOwnerThresholdChanged (evm : EVM.State) (key threshold : UInt256)
    (ht : storedThreshold evm ≠ threshold)
    (hle : threshold.toNat ≤ (ownerCount evm).toNat) (hnz : threshold ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config (addOwnerFrame₁ key threshold) evm addOwnerThresholdStmt
      (.ok (resumeAfterInternalCall (addOwnerFrame₁ key threshold) "_thresholdChanged" none)
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ threshold)) :=
  safeThresholdChangeChanged (hperm := by assumption) evm _ threshold
    (safeAddOwnerLocal key threshold "threshold" (by decide))
    (safeAddOwnerEvalThreshold evm key threshold) ht hle hnz

theorem safeAddOwnerThresholdRevert (evm : EVM.State) (key threshold : UInt256)
    (ht : storedThreshold evm ≠ threshold)
    (hb : ExecFuncBody fork config (thresholdFrame threshold) evm changeThresholdBodyFunction.body
      .reverted) :
    ExecStmt fork config (addOwnerFrame₁ key threshold) evm addOwnerThresholdStmt .reverted :=
  safeThresholdChangeRevert evm _ threshold
    (safeAddOwnerLocal key threshold "threshold" (by decide))
    (safeAddOwnerEvalThreshold evm key threshold) ht hb

theorem safeAddOwnerTailOK (evm : EVM.State) (key threshold : UInt256) {frame' evm'}
    (hno : (ownerCount evm).toNat + 1 < UInt256.size)
    (ht : ExecStmt fork config (addOwnerFrame₁ key threshold) (addOwnerCountState evm)
      addOwnerThresholdStmt (.ok frame' evm'))
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config (addOwnerFrame₁ key threshold) evm addOwnerTail (.ok frame' evm') :=
  .consNormal (safeAddOwnerIncrement (fork := fork) (hperm := by assumption) evm key threshold hno)
    (.consNormal (.emit (hperm := by simpa only [addOwnerCountState, storageStore_executionEnv] using hperm) (evalExprs?_singleton (safeAddOwnerEval _ key threshold)))
      (.consNormal ht .nil))

theorem safeAddOwnerTailRevert (evm : EVM.State) (key threshold : UInt256)
    (hno : (ownerCount evm).toNat + 1 < UInt256.size)
    (ht : ExecStmt fork config (addOwnerFrame₁ key threshold) (addOwnerCountState evm)
      addOwnerThresholdStmt .reverted)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config (addOwnerFrame₁ key threshold) evm addOwnerTail .reverted :=
  .consNormal (safeAddOwnerIncrement (fork := fork) (hperm := by assumption) evm key threshold hno)
    (.consNormal (.emit (hperm := by simpa only [addOwnerCountState, storageStore_executionEnv] using hperm) (evalExprs?_singleton (safeAddOwnerEval _ key threshold)))
      (.consRevert ht))

theorem safeAddOwnerSourceStatic (evm : EVM.State) (key threshold : UInt256)
    (hc : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hv : validOwner evm.accountMap evm.executionEnv key) (he : ownerLink evm key = ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (addOwnerArgs key threshold)
      addownerwiththresholdTransition.body .staticViolation := by
  have hb := safeAddOwnerLocal key threshold "owners" (by decide)
  have hload := safeEvalOwnerLink evm _ sentinelAddr ⟨1⟩ hb (by decide)
    (safeEvalOwnerSentinel evm _)
  have hfirst := safeAssignOwnerLink evm _ _ key (ownerLink evm ⟨1⟩) hb hc
    (solcAddrMask_result_canonical _) (safeAddOwnerEval evm key threshold)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (safeAddOwnerCanAdd evm key threshold hc hv he)
        (.consStatic (.assignStatic hload hfirst hperm)))))

theorem safeAddOwnerSourceGuardRevert (evm : EVM.State) (key threshold : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hbody : ExecFuncBody fork config (canAddOwnerFrame key) evm requireCanAddOwnerFunction.body
      .reverted) :
    ExecTransitionBody fork config contract evm (addOwnerArgs key threshold)
      addownerwiththresholdTransition.body .reverted := by
  have hcall : ExecStmt fork config (addOwnerFrame key threshold) evm
      (.internalCall "requireCanAddOwner" [.var "owner"] "_ok") .reverted := by
    apply internalCallFunctionRevert (callee := requireCanAddOwnerFunction)
      (argVals := [.address (AccountAddress.ofNat key.toNat)]) (locals := canAddOwnerArgs key)
    · simp [addOwnerFrame, addOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
        EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
    · rfl
    · rfl
    · exact hbody
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _)) (.consRevert
      hcall)))

theorem safeAddOwnerSourceUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm locals addownerwiththresholdTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

end Benchmarks.Safe.V1_0227664
