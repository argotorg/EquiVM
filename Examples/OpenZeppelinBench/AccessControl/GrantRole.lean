import Examples.OpenZeppelinBench.AccessControl.Storage
import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `grantRole(bytes32,address)` proof

Phase-1 worker file for the external wrapper at pc 214 and the shared guarded `_grantRole`
routine at pc 540.
-/

abbrev grantRoleRoleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev grantRoleAccountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev grantRoleRoleValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I))

abbrev grantRoleAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)

abbrev grantRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (grantRoleRoleValue I)).insert "account"
    (grantRoleAccountValue I)

def grantRoleRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I))

def grantRoleAccountKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)

def grantRoleAdminSlot (I : ExecutionEnv) : UInt256 :=
  roleAdminSlot (grantRoleRoleKey I)

def grantRoleAdminWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminSlot I)

def grantRoleAdminValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleAdminWord evm I))

def grantRoleAdminKey (evm : EVM.State) (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleAdminWord evm I))

def grantRoleSenderKey (evm : EVM.State) : KeyValue :=
  .address evm.executionEnv.source

def grantRoleStoreWithAdmin (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (grantRoleStore I).insert "adminRole" (grantRoleAdminValue evm I)

def grantRoleAdminHasRoleSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (grantRoleAdminKey evm I) (grantRoleSenderKey evm)

def grantRoleTargetSlot (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (grantRoleRoleKey I) (grantRoleAccountKey I)

def grantRoleSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def grantRolePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)
    (grantRoleSetTrueWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)))

def grantRoleAdminEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles", steps := [.mindex (grantRoleRoleKey I), .field "adminRole"] }

def grantRoleAdminHasRoleEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (grantRoleAdminKey evm I), .field "hasRole",
      .mindex (grantRoleSenderKey evm)] }

def grantRoleTargetEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (grantRoleRoleKey I), .field "hasRole",
      .mindex (grantRoleAccountKey I)] }

theorem grantRoleStore_role (I : ExecutionEnv) :
    (grantRoleStore I).get? "role" = some (grantRoleRoleValue I) := by
  rw [grantRoleStore, store_get_ne _ _ (by decide), store_get_self]

theorem grantRoleStore_account (I : ExecutionEnv) :
    (grantRoleStore I).get? "account" = some (grantRoleAccountValue I) := by
  rw [grantRoleStore, store_get_self]

theorem grantRoleStore_roles (I : ExecutionEnv) :
    (grantRoleStore I).get? "_roles" = none := by
  rw [grantRoleStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem grantRoleStoreWithAdmin_role (evm : EVM.State) (I : ExecutionEnv) :
    (grantRoleStoreWithAdmin evm I).get? "role" = some (grantRoleRoleValue I) := by
  rw [grantRoleStoreWithAdmin, store_get_ne _ _ (by decide), grantRoleStore_role]

theorem grantRoleStoreWithAdmin_account (evm : EVM.State) (I : ExecutionEnv) :
    (grantRoleStoreWithAdmin evm I).get? "account" = some (grantRoleAccountValue I) := by
  rw [grantRoleStoreWithAdmin, store_get_ne _ _ (by decide), grantRoleStore_account]

theorem grantRoleStoreWithAdmin_adminRole (evm : EVM.State) (I : ExecutionEnv) :
    (grantRoleStoreWithAdmin evm I).get? "adminRole" = some (grantRoleAdminValue evm I) := by
  rw [grantRoleStoreWithAdmin, store_get_self]

theorem grantRoleStoreWithAdmin_roles (evm : EVM.State) (I : ExecutionEnv) :
    (grantRoleStoreWithAdmin evm I).get? "_roles" = none := by
  rw [grantRoleStoreWithAdmin, store_get_ne _ _ (by decide), grantRoleStore_roles]

theorem evalExpr_grantRole_role (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := grantRoleStore I } evm
      (.var "role") = .ok (grantRoleRoleValue I) := by
  rw [evalExpr?, grantRoleStore_role]
  rfl

theorem evalExpr_grantRole_account (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.var "account") = .ok (grantRoleAccountValue I) := by
  rw [evalExpr?, grantRoleStoreWithAdmin_account]
  rfl

theorem evalExpr_grantRole_role_withAdmin (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.var "role") = .ok (grantRoleRoleValue I) := by
  rw [evalExpr?, grantRoleStoreWithAdmin_role]
  rfl

theorem evalExpr_grantRole_adminRole (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.var "adminRole") = .ok (grantRoleAdminValue evm I) := by
  rw [evalExpr?, grantRoleStoreWithAdmin_adminRole]
  rfl

theorem evalStorageRef_grantRole_admin (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := grantRoleStore I } evm
      (roleAdminRef (.var "role")) = .ok (grantRoleAdminEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleAdminRef,
    evalExpr_grantRole_role, grantRoleAdminEvaledRef, grantRoleRoleValue, grantRoleRoleKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_grantRole_admin (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := grantRoleStore I } evm
      (.storage (roleAdminRef (.var "role"))) = .ok (grantRoleAdminValue evm I) := by
  rw [evalExpr_storage_scalar (t := .bytes bytes32Width)
    (loc := bytes32Loc (grantRoleAdminSlot I))
    (hbase := grantRoleStore_roles I)
    (her := evalStorageRef_grantRole_admin evm I)
    (hty := by
      simp [storageTypeAt?, grantRoleAdminEvaledRef, contract, storageDecls, roleDataSt,
        bytes32St, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bytes32]
  simp [grantRoleAdminValue, grantRoleAdminWord, bytes32Width]

theorem evalStorageRef_grantRole_adminHasRole (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (roleHasRoleRef (.var "adminRole") sender) =
        .ok (grantRoleAdminHasRoleEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef, sender,
    envValue, evalExpr_grantRole_adminRole, grantRoleAdminHasRoleEvaledRef,
    grantRoleAdminValue, grantRoleAdminKey, grantRoleSenderKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_grantRole_adminHasRole_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "adminRole") sender)) = .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleAdminHasRoleSlot evm I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_adminHasRole evm I)
    (hty := by
      simp [storageTypeAt?, grantRoleAdminHasRoleEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_grantRole_adminHasRole_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "adminRole") sender)) = .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleAdminHasRoleSlot evm I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_adminHasRole evm I)
    (hty := by
      simp [storageTypeAt?, grantRoleAdminHasRoleEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

theorem evalStorageRef_grantRole_target (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (roleHasRoleRef (.var "role") (.var "account")) =
        .ok (grantRoleTargetEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef,
    evalExpr_grantRole_role_withAdmin, evalExpr_grantRole_account, grantRoleTargetEvaledRef,
    grantRoleRoleValue, grantRoleRoleKey, grantRoleAccountValue, grantRoleAccountKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_grantRole_target_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleTargetSlot I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_target evm I)
    (hty := by
      simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_grantRole_target_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleTargetSlot I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_target evm I)
    (hty := by
      simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

theorem evalExpr_grantRole_target_not_true (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.unary .not (.storage (roleHasRoleRef (.var "role") (.var "account")))) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption,
    evalExpr_grantRole_target_false evm I hzero]

theorem evalExpr_grantRole_target_not_false (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.unary .not (.storage (roleHasRoleRef (.var "role") (.var "account")))) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption,
    evalExpr_grantRole_target_true evm I hnz]

theorem accessControlStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (grantRoleSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc, grantRoleSetTrueWord] using
    SimpleAuction.simpleAuctionStorageLocStore_bool_true_offset0 evm slot

theorem grantRoleAssignTarget (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      .storage (roleHasRoleRef (.var "role") (.var "account")) (.bool true) =
        .ok ({ contract := contract, locals := grantRoleStoreWithAdmin evm I },
          grantRolePostState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := grantRoleTargetEvaledRef I) (ty := boolSt)
      (loc := boolLoc (grantRoleTargetSlot I))
      (value := .bool true)
      (evm' := grantRolePostState evm I)
      (hbase := grantRoleStoreWithAdmin_roles evm I)
      (her := evalStorageRef_grantRole_target evm I)
      (hty := by
        simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
          boolSt, storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, grantRoleTargetEvaledRef, grantRoleTargetSlot])
      (hscalar := by trivial)
      (hstore := by
        exact accessControlStorageLocStore_bool_true_offset0 evm (grantRoleTargetSlot I))

theorem accessControlGrantRoleBodyReturns_write (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm (grantRoleStore I) grantRoleTransition.body
      (.returned { contract := contract, locals := grantRoleStoreWithAdmin evm I }
        (grantRolePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_grantRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (result := .ok
      ({ contract := contract, locals := grantRoleStoreWithAdmin evm I } : Frame)
      (grantRolePostState evm I))
      (evalExpr_grantRole_target_not_true evm I htarget) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (grantRoleAssignTarget evm I)) ?_
    exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlGrantRoleBodyReturns_noop (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm (grantRoleStore I) grantRoleTransition.body
      (.returned { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_grantRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := grantRoleStoreWithAdmin evm I } : Frame) evm)
      (evalExpr_grantRole_target_not_false evm I htarget) ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlGrantRoleBodyReverts_admin (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (grantRoleStore I) grantRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_grantRole_adminHasRole_false evm I hadmin))

theorem grantRoleSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_grantRole {cd : ByteArray}
    (hsel : ((⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some grantRoleTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ : ByteArray) :=
    (accessControlByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition])
    (post := [hasRoleTransition, renounceRoleTransition, revokeRoleTransition,
      supportsInterfaceTransition]) rfl ?_
    (by rw [selectorOf, grantRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide

end OpenZeppelinBench.AccessControl
