import Benchmarks.Safe.OwnerGuardTraces

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def swapOwnerArgs (prev old new : UInt256) : Store :=
  (((∅ : Store).insert "prevOwner" (.address (AccountAddress.ofNat prev.toNat))).insert
    "oldOwner" (.address (AccountAddress.ofNat old.toNat))).insert
    "newOwner" (.address (AccountAddress.ofNat new.toNat))

def swapOwnerFrame (prev old new : UInt256) : Frame :=
  { contract := contract, locals := swapOwnerArgs prev old new }

def swapOwnerFrame₁ (prev old new : UInt256) : Frame :=
  resumeAfterInternalCall (swapOwnerFrame prev old new) "_canAdd" none

def swapOwnerFrame₂ (prev old new : UInt256) : Frame :=
  resumeAfterInternalCall (swapOwnerFrame₁ prev old new) "_canRemove" none

def swapOwnerState (evm : EVM.State) (prev old new : UInt256) : EVM.State :=
  writeOwnerLink (writeOwnerLink (writeOwnerLink evm new (ownerLink evm old)) prev new) old ⟨0⟩

theorem safeSwapOwnerCanAdd (evm : EVM.State) (prev old new : UInt256)
    (hc : new.toNat < EVM.addressModulus) (hv : validOwner evm.accountMap evm.executionEnv new)
    (he : ownerLink evm new = ⟨0⟩) :
    ExecStmt config (swapOwnerFrame prev old new) evm
      (.internalCall "requireCanAddOwner" [.var "newOwner"] "_canAdd")
      (.ok (swapOwnerFrame₁ prev old new) evm) := by
  apply internalCallFunctionReturn (callee := requireCanAddOwnerFunction)
    (argVals := [.address (AccountAddress.ofNat new.toNat)])
    (locals := canAddOwnerArgs new) (calleeSolm := canAddOwnerFrame new)
  · simp [swapOwnerFrame, swapOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · exact safeCanAddOwnerSource evm new hc hv he

theorem safeSwapOwnerCanRemove (evm : EVM.State) (prev old new : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (ho : old.toNat < EVM.addressModulus)
    (hv : validOwner evm.accountMap evm.executionEnv old) (hl : ownerLink evm prev = old) :
    ExecStmt config (swapOwnerFrame₁ prev old new) evm
      (.internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "oldOwner"] "_canRemove")
      (.ok (swapOwnerFrame₂ prev old new) evm) := by
  apply internalCallFunctionReturn (callee := requireCanRemoveOwnerFunction)
    (argVals := [.address (AccountAddress.ofNat prev.toNat),
      .address (AccountAddress.ofNat old.toNat)])
    (locals := canRemoveOwnerArgs prev old) (calleeSolm := canRemoveOwnerFrame prev old)
  · simp [swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs, resumeAfterInternalCall,
      evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact safeCanRemoveOwnerSource evm prev old hp ho hv hl

theorem safeSwapOwnerEvalOld (evm : EVM.State) (prev old new : UInt256) :
    evalExpr? config (swapOwnerFrame₂ prev old new) evm (.var "oldOwner") =
      .ok (.address (AccountAddress.ofNat old.toNat)) := by
  simp [swapOwnerFrame₂, swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs,
    resumeAfterInternalCall, evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeSwapOwnerEvalNew (evm : EVM.State) (prev old new : UInt256) :
    evalExpr? config (swapOwnerFrame₂ prev old new) evm (.var "newOwner") =
      .ok (.address (AccountAddress.ofNat new.toNat)) := by
  simp [swapOwnerFrame₂, swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs,
    resumeAfterInternalCall, evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeSwapOwnerEvalPrev (evm : EVM.State) (prev old new : UInt256) :
    evalExpr? config (swapOwnerFrame₂ prev old new) evm (.var "prevOwner") =
      .ok (.address (AccountAddress.ofNat prev.toNat)) := by
  simp [swapOwnerFrame₂, swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs,
    resumeAfterInternalCall, evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeSwapOwnerLocals (prev old new : UInt256) :
    (swapOwnerFrame₂ prev old new).locals["owners"]? = none := by
  simp [swapOwnerFrame₂, swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs,
    resumeAfterInternalCall, Std.HashMap.getElem_insert]

theorem safeSwapOwnerSource (evm : EVM.State) (prev old new : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (ho : old.toNat < EVM.addressModulus)
    (hn : new.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hvn : validOwner evm.accountMap evm.executionEnv new) (he : ownerLink evm new = ⟨0⟩)
    (hvo : validOwner evm.accountMap evm.executionEnv old) (hl : ownerLink evm prev = old) :
    ExecTransitionBody config contract evm (swapOwnerArgs prev old new) swapownerTransition.body
      (.returned (swapOwnerFrame₂ prev old new) (swapOwnerState evm prev old new) none) := by
  have hbase := safeSwapOwnerLocals prev old new
  have hload := safeEvalOwnerLink evm _ _ old hbase ho (safeSwapOwnerEvalOld evm prev old new)
  have hfirst := safeAssignOwnerLink evm _ _ new (ownerLink evm old) hbase hn
    (solcAddrMask_result_canonical _) (safeSwapOwnerEvalNew evm prev old new)
  have hsecond := safeAssignOwnerLink (writeOwnerLink evm new (ownerLink evm old)) _ _ prev new
    hbase hp hn (safeSwapOwnerEvalPrev _ prev old new)
  have hthird := safeAssignOwnerLink (writeOwnerLink
    (writeOwnerLink evm new (ownerLink evm old)) prev new) _ _ old ⟨0⟩ hbase ho (by decide)
      (safeSwapOwnerEvalOld _ prev old new)
  have hz (evm' : EVM.State) : evalExpr? config (swapOwnerFrame₂ prev old new) evm' zeroAddr =
      .ok (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
      bind, pure]
  exact .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (safeSwapOwnerCanAdd evm prev old new hn hvn he)
        (.consNormal (safeSwapOwnerCanRemove evm prev old new hp ho hvo hl)
          (.consNormal (.assign hload hfirst)
            (.consNormal (.assign (safeSwapOwnerEvalNew _ prev old new) hsecond)
              (.consNormal (.assign (hz _) hthird)
                (.consNormal (.emit (evalExprs?_singleton (safeSwapOwnerEvalOld _ prev old new)))
                  (.consNormal (.emit (evalExprs?_singleton (safeSwapOwnerEvalNew _ prev old new)))
                    .nil)))))))))

theorem safeSwapOwnerSourceStatic (evm : EVM.State) (prev old new : UInt256)
    (hp : prev.toNat < EVM.addressModulus) (ho : old.toNat < EVM.addressModulus)
    (hn : new.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hvn : validOwner evm.accountMap evm.executionEnv new) (he : ownerLink evm new = ⟨0⟩)
    (hvo : validOwner evm.accountMap evm.executionEnv old) (hl : ownerLink evm prev = old)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (swapOwnerArgs prev old new) swapownerTransition.body
      .staticViolation := by
  have hbase := safeSwapOwnerLocals prev old new
  have hload := safeEvalOwnerLink evm _ _ old hbase ho (safeSwapOwnerEvalOld evm prev old new)
  have hfirst := safeAssignOwnerLink evm _ _ new (ownerLink evm old) hbase hn
    (solcAddrMask_result_canonical _) (safeSwapOwnerEvalNew evm prev old new)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (safeSwapOwnerCanAdd evm prev old new hn hvn he)
        (.consNormal (safeSwapOwnerCanRemove evm prev old new hp ho hvo hl)
          (.consStatic (.assignStatic hload hfirst hperm))))))

theorem safeSwapOwnerSourceAddRevert (evm : EVM.State) (prev old new : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hbody : ExecFuncBody config (canAddOwnerFrame new) evm
      requireCanAddOwnerFunction.body .reverted) :
    ExecTransitionBody config contract evm (swapOwnerArgs prev old new) swapownerTransition.body
      .reverted := by
  have hcall : ExecStmt config (swapOwnerFrame prev old new) evm
      (.internalCall "requireCanAddOwner" [.var "newOwner"] "_canAdd") .reverted := by
    apply internalCallFunctionRevert (callee := requireCanAddOwnerFunction)
      (argVals := [.address (AccountAddress.ofNat new.toNat)])
      (locals := canAddOwnerArgs new)
    · simp [swapOwnerFrame, swapOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
        EvalResult.bind, bind, pure]
    · rfl
    · rfl
    · exact hbody
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert hcall)))

theorem safeSwapOwnerSourceRemoveRevert (evm : EVM.State) (prev old new : UInt256)
    (hn : new.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hvn : validOwner evm.accountMap evm.executionEnv new) (he : ownerLink evm new = ⟨0⟩)
    (hbody : ExecFuncBody config (canRemoveOwnerFrame prev old) evm
      requireCanRemoveOwnerFunction.body .reverted) :
    ExecTransitionBody config contract evm (swapOwnerArgs prev old new) swapownerTransition.body
      .reverted := by
  have hcall : ExecStmt config (swapOwnerFrame₁ prev old new) evm
      (.internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "oldOwner"] "_canRemove")
      .reverted := by
    apply internalCallFunctionRevert (callee := requireCanRemoveOwnerFunction)
      (argVals := [.address (AccountAddress.ofNat prev.toNat),
        .address (AccountAddress.ofNat old.toNat)])
      (locals := canRemoveOwnerArgs prev old)
    · simp [swapOwnerFrame₁, swapOwnerFrame, swapOwnerArgs, resumeAfterInternalCall,
        evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
        Std.HashMap.getElem_insert]
    · rfl
    · rfl
    · exact hbody
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (safeSwapOwnerCanAdd evm prev old new hn hvn he) (.consRevert hcall))))

theorem safeSwapOwnerSourceUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals swapownerTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

end Benchmarks.Safe
