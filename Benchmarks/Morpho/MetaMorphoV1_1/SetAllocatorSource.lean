import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Source outcomes for updating allocator permissions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setAllocatorLocals (addr : AccountAddress) (flag : UInt256) : Store :=
  ((∅ : Store).insert "newAllocator" (.address addr)).insert "newIsAllocator"
    (wordToElem .bool flag)

def setAllocatorFrame (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) : Frame := adminFrame evm (setAllocatorLocals addr flag) imms

def setAllocatorGuard : Expr :=
  .binary .ne (.storage ⟨"isAllocator", [.mindex (.var "newAllocator")]⟩)
    (.var "newIsAllocator")

def setAllocatorAssign : Stmt :=
  .assign .storage ⟨"isAllocator", [.mindex (.var "newAllocator")]⟩ (.var "newIsAllocator")

def setAllocatorEmit : Stmt :=
  .emit "SetIsAllocator" [.var "newAllocator", .var "newIsAllocator"]

def setAllocatorTail : List Stmt :=
  [.require setAllocatorGuard, setAllocatorAssign, setAllocatorEmit]

theorem setAllocatorFrame_addr (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) :
    (setAllocatorFrame evm imms addr flag).locals.get? "newAllocator" = some (.address addr) := by
  simp only [setAllocatorFrame, adminFrame, setAllocatorLocals,
    store_get_ne _ _ (by decide : ("__c0" == "newAllocator") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "newAllocator") = false),
    store_get_ne _ _ (by decide : ("newIsAllocator" == "newAllocator") = false), store_get_self]

theorem setAllocatorFrame_flag (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) :
    (setAllocatorFrame evm imms addr flag).locals.get? "newIsAllocator" =
      some (wordToElem .bool flag) := by
  simp only [setAllocatorFrame, adminFrame, setAllocatorLocals,
    store_get_ne _ _ (by decide : ("__c0" == "newIsAllocator") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "newIsAllocator") = false), store_get_self]

theorem setAllocatorGuardSource (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩) :
    evalExpr? config (setAllocatorFrame evm imms addr flag) evm setAllocatorGuard =
      .ok (.bool (decide (allocatorBoolWord evm addr ≠ flag))) := by
  have hread := evalStorage_allocator evm (setAllocatorFrame evm imms addr flag).locals imms
    "newAllocator" addr (by simp [setAllocatorFrame, adminFrame, setAllocatorLocals])
    (setAllocatorFrame_addr evm imms addr flag)
  have hnew : evalExpr? config (setAllocatorFrame evm imms addr flag) evm
      (.var "newIsAllocator") = .ok (wordToElem .bool flag) := by
    simp only [evalExpr?, setAllocatorFrame_flag, EvalResult.ofOption]
  have h := boolWordNeSource hread hnew
  rw [(boolWordClean_iff flag).mpr hflag] at h
  exact h

theorem setAllocatorAssignment (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) :
    ExecStmt config (setAllocatorFrame evm imms addr flag) evm setAllocatorAssign
      (.ok (setAllocatorFrame evm imms addr flag) (setAllocatorState evm addr flag)) := by
  apply ExecStmt.assign (value := wordToElem .bool flag)
  · simp only [evalExpr?, setAllocatorFrame_flag, EvalResult.ofOption]
  · exact assignStorage_allocator evm _ imms "newAllocator" addr flag
      (by simp [setAllocatorFrame, adminFrame, setAllocatorLocals])
      (setAllocatorFrame_addr evm imms addr flag)

theorem setAllocatorPrefix (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hne : allocatorBoolWord evm addr ≠ flag) :
    ABlock config evm ⟨contract, setAllocatorLocals addr flag, imms⟩
      setIsAllocatorTransition.body (setAllocatorFrame evm imms addr flag)
      [setAllocatorAssign, setAllocatorEmit] := by
  have hpre := adminPrefix evm (setAllocatorLocals addr flag) imms setAllocatorTail hwv hhi howner
  apply hpre.requireStep
  change evalExpr? config (setAllocatorFrame evm imms addr flag) evm setAllocatorGuard = _
  simp [setAllocatorGuardSource evm imms addr flag hflag, hne]

theorem setAllocatorBodyReturns (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hne : allocatorBoolWord evm addr ≠ flag) :
    ExecTransitionBody config contract evm (setAllocatorLocals addr flag)
      setIsAllocatorTransition.body
      (.returned (setAllocatorFrame evm imms addr flag) (setAllocatorState evm addr flag) none)
      imms := by
  apply ExecFuncBody.execBlockOK
  apply (setAllocatorPrefix evm imms addr flag hflag hwv hhi howner hne).run
  refine ExecBlock.consNormal (setAllocatorAssignment evm imms addr flag) ?_
  apply (ABlock.start.emitStep (vals := [.address addr, wordToElem .bool flag]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, setAllocatorFrame_addr, setAllocatorFrame_flag,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem setAllocatorBodyStatic (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hne : allocatorBoolWord evm addr ≠ flag) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (setAllocatorLocals addr flag)
      setIsAllocatorTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (setAllocatorPrefix evm imms addr flag hflag hwv hhi howner hne).run
  exact ExecBlock.consStatic
    (execStmt_assign_static (setAllocatorAssignment evm imms addr flag) hperm)

theorem setAllocatorBodyReverts (evm : EVM.State) (imms : Store) (addr : AccountAddress)
    (flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (heq : allocatorBoolWord evm addr = flag) :
    ExecTransitionBody config contract evm (setAllocatorLocals addr flag)
      setIsAllocatorTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (setAllocatorLocals addr flag) imms setAllocatorTail hwv hhi howner
  apply hpre.requireRevert
  change evalExpr? config (setAllocatorFrame evm imms addr flag) evm setAllocatorGuard = _
  simp [setAllocatorGuardSource evm imms addr flag hflag, heq]

end Benchmarks.Morpho.MetaMorphoV1_1
