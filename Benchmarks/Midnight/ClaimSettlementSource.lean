import Benchmarks.Midnight.SafeTransferSource
import Benchmarks.Midnight.RoleSource
import Benchmarks.Midnight.InternalCall

/-! Source execution of the settlement-fee claim through its safe-transfer call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def claimSettlementArguments (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) : Store :=
  (((∅ : Store).insert "token" (.address token)).insert "amount" (uint256Value amount)).insert
    "receiver" (.address receiver)

def claimSettlementFrame (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) : Frame :=
  calldataFrame contract (claimSettlementArguments token amount receiver) ∅ evm

def claimSettlementSlot (token : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨6⟩ (UInt256.ofNat token.val)

def claimSettlementBalance (evm : State) (token : AccountAddress) : UInt256 :=
  Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (claimSettlementSlot token)

def claimSettlementState (evm : State) (token : AccountAddress) (amount : UInt256) : State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (claimSettlementSlot token)
    (UInt256.sub (claimSettlementBalance evm token) amount)

def claimSettlementRef : StorageRef :=
  { base := "claimableSettlementFee", steps := [.mindex (.var "token")] }

def claimSettlementSubtract : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage claimSettlementRef) (.var "amount"))

def claimSettlementCall : Stmt :=
  .internalCall "SafeTransferLib_safeTransfer" [.var "token", .var "receiver", .var "amount"] "__c0"

theorem claimSettlementGet (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    (claimSettlementFrame evm token amount receiver).locals.get? "token" = some (.address token) ∧
    (claimSettlementFrame evm token amount receiver).locals.get? "amount" = some (uint256Value amount) ∧
    (claimSettlementFrame evm token amount receiver).locals.get? "receiver" =
      some (.address receiver) := by
  simp only [claimSettlementFrame, calldataFrame, claimSettlementArguments]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · rw [store_get_ne _ _ (by decide), store_get_self]

theorem claimSettlementGuardEval (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    evalExpr? config (claimSettlementFrame evm token amount receiver) evm (roleGuard "feeClaimer") =
      .ok (.bool (decide (roleAllowed evm ⟨11⟩))) := by
  exact evalRoleGuard evm "feeClaimer" ⟨11⟩ rfl
    (by simp [claimSettlementFrame, calldataFrame, claimSettlementArguments]) rfl rfl

theorem claimSettlementResolve (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    evalStorageRef config (claimSettlementFrame evm token amount receiver) evm claimSettlementRef =
      .ok { base := "claimableSettlementFee", steps := [.mindex (.address token)] } := by
  simp only [claimSettlementRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    (claimSettlementGet evm token amount receiver).1, EvalResult.ofOption, EvalResult.bind,
    valueToKey?, pure, bind]

theorem claimSettlementLayout (token : AccountAddress) :
    midnightStorageLayout { base := "claimableSettlementFee", steps := [.mindex (.address token)] } =
      some (.leaf {
        slot := claimSettlementSlot token, offset := 0, size := 32,
        hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) := by
  change some (StorageAddr.leaf {
    slot := solcMappingSlot ⟨6⟩ (keyValueToWord (.address token)), offset := 0, size := 32,
    hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
  rw [keyValueToWord_address]
  rfl

theorem claimSettlementRead (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    evalExpr? config (claimSettlementFrame evm token amount receiver) evm
      (.storage claimSettlementRef) = .ok (uint256Value (claimSettlementBalance evm token)) := by
  apply evalExpr_storage_scalar_value (er := {
      base := "claimableSettlementFee", steps := [.mindex (.address token)] })
    (loc := {
      slot := claimSettlementSlot token, offset := 0, size := 32,
      hbound := by decide, type := .int (.uint ⟨256, by decide⟩) })
    (t := .int (.uint ⟨256, by decide⟩))
  · simp [claimSettlementFrame, calldataFrame, claimSettlementArguments, claimSettlementRef]
  · exact claimSettlementResolve evm token amount receiver
  · rfl
  · rfl
  · exact claimSettlementLayout token
  · exact storageLocLoad_uint256 evm _

theorem claimSettlementAmountEval (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    evalExpr? config (claimSettlementFrame evm token amount receiver) evm (.var "amount") =
      .ok (uint256Value amount) := by
  simp only [evalExpr?, (claimSettlementGet evm token amount receiver).2.1, EvalResult.ofOption]

theorem claimSettlementAssign (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) :
    assignStorageRef? config (claimSettlementFrame evm token amount receiver) evm .storage
      claimSettlementRef (uint256Value (UInt256.sub (claimSettlementBalance evm token) amount)) =
      .ok (claimSettlementFrame evm token amount receiver, claimSettlementState evm token amount) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := "claimableSettlementFee", steps := [.mindex (.address token)] })
    (loc := {
      slot := claimSettlementSlot token, offset := 0, size := 32,
      hbound := by decide, type := .int (.uint ⟨256, by decide⟩) })
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) (layout := midnightStorageLayout)
  · simp [claimSettlementFrame, calldataFrame, claimSettlementArguments, claimSettlementRef]
  · exact claimSettlementResolve evm token amount receiver
  · rfl
  · rfl
  · exact claimSettlementLayout token
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ _

theorem claimSettlementBody_shape : claimSettlementFeeTransition.body = entryPrefix ++
    [.require (roleGuard "feeClaimer"), .assign .storage claimSettlementRef claimSettlementSubtract,
     .emit "ClaimSettlementFee" [.env .caller, .var "token", .var "amount", .var "receiver"],
     claimSettlementCall] := rfl

theorem claimSettlementUnauthorized (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : ¬roleAllowed evm ⟨11⟩) :
    ExecTransitionBody config contract evm (claimSettlementArguments token amount receiver)
      claimSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [claimSettlementBody_shape]
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert (ExecStmt.requireFalse _)
  exact (claimSettlementGuardEval evm token amount receiver).trans
    (by rw [decide_eq_false ha])

theorem claimSettlementUnderflow (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : roleAllowed evm ⟨11⟩)
    (hunder : (claimSettlementBalance evm token).toNat < amount.toNat) :
    ExecTransitionBody config contract evm (claimSettlementArguments token amount receiver)
      claimSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [claimSettlementBody_shape]
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (claimSettlementGuardEval evm token amount receiver).trans
      (by rw [decide_eq_true ha])
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert _)
  exact Reasoning.VyperDispatch.evalExpr_uint256_sub_underflow
    (claimSettlementRead evm token amount receiver)
    (claimSettlementAmountEval evm token amount receiver) hunder

theorem claimSettlementStatic (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : roleAllowed evm ⟨11⟩)
    (hbound : amount.toNat ≤ (claimSettlementBalance evm token).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (claimSettlementArguments token amount receiver)
      claimSettlementFeeTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [claimSettlementBody_shape]
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (claimSettlementGuardEval evm token amount receiver).trans
      (by rw [decide_eq_true ha])
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (evalExpr_uint256_sub (claimSettlementRead ..)
    (claimSettlementAmountEval ..) hbound) (claimSettlementAssign evm token amount receiver) hperm

theorem claimSettlementRun (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver : AccountAddress) {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : roleAllowed evm ⟨11⟩)
    (hbound : amount.toNat ≤ (claimSettlementBalance evm token).toNat)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (claimSettlementFrame evm token amount receiver)
      (claimSettlementState evm token amount) [claimSettlementCall] result) :
    ExecBlock config {
      contract := contract, locals := claimSettlementArguments token amount receiver,
      immutables := ∅ } evm claimSettlementFeeTransition.body result := by
  rw [claimSettlementBody_shape]
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (claimSettlementGuardEval evm token amount receiver).trans
      (by rw [decide_eq_true ha])
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalExpr_uint256_sub (claimSettlementRead ..) (claimSettlementAmountEval ..) hbound)
    (claimSettlementAssign evm token amount receiver)) ?_
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address token, uint256Value amount, .address receiver]) ?_ ?_) htail
  · simpa only [claimSettlementState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, envValue, claimSettlementState, storageStore_executionEnv,
      (claimSettlementGet evm token amount receiver).1,
      (claimSettlementGet evm token amount receiver).2.1,
      (claimSettlementGet evm token amount receiver).2.2,
      EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem claimSettlementCallArgs (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver sender : AccountAddress) :
    evalExprs? config (claimSettlementFrame evm token amount receiver)
      (claimSettlementState evm token amount) [.var "token", .var "receiver", .var "amount"] =
      .ok (safeTransferArguments false token sender receiver amount) := by
  simp only [evalExprs?, evalExpr?,
    (claimSettlementGet evm token amount receiver).1,
    (claimSettlementGet evm token amount receiver).2.1,
    (claimSettlementGet evm token amount receiver).2.2,
    EvalResult.ofOption, EvalResult.bind, pure, bind]
  rfl

theorem claimSettlementCallReverts (evm : State) (token : AccountAddress) (amount : UInt256)
    (receiver sender : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : roleAllowed evm ⟨11⟩)
    (hbound : amount.toNat ≤ (claimSettlementBalance evm token).toNat)
    (hperm : evm.executionEnv.perm = true)
    (hbody : ExecFuncBody config (safeTransferFrame false ∅ token sender receiver amount)
      (claimSettlementState evm token amount) (safeTransferFunctionFor false).body .reverted) :
    ExecTransitionBody config contract evm (claimSettlementArguments token amount receiver)
      claimSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply claimSettlementRun evm token amount receiver hwv hhi ha hbound hperm
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (claimSettlementCallArgs evm token amount receiver sender)
    (safeTransferLookup false) (safeTransferBind false token sender receiver amount) hbody

theorem claimSettlementReturns (evm evm' : State) (token : AccountAddress) (amount : UInt256)
    (receiver sender : AccountAddress) (out : ByteArray) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (ha : roleAllowed evm ⟨11⟩)
    (hbound : amount.toNat ≤ (claimSettlementBalance evm token).toNat)
    (hperm : evm.executionEnv.perm = true)
    (hbody : ExecFuncBody config (safeTransferFrame false ∅ token sender receiver amount)
      (claimSettlementState evm token amount) (safeTransferFunctionFor false).body
      (.returned (safeTransferCallFrame false ∅ token sender receiver amount true out) evm' none)) :
    ExecTransitionBody config contract evm (claimSettlementArguments token amount receiver)
      claimSettlementFeeTransition.body
      (.returned (resumeAfterInternalCall (claimSettlementFrame evm token amount receiver) "__c0" none)
        evm' none) := by
  apply ExecFuncBody.execBlockOK
  apply claimSettlementRun evm token amount receiver hwv hhi ha hbound hperm
  exact ExecBlock.consNormal
    (internalCallFunctionReturn (claimSettlementCallArgs evm token amount receiver sender)
      (safeTransferLookup false) (safeTransferBind false token sender receiver amount) hbody)
    ExecBlock.nil

end Benchmarks.Midnight
