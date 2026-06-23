import Examples.OpenZeppelinBench.AccessControl.Storage
import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `revokeRole(bytes32,address)` proof

Phase-1 worker file for the external wrapper at pc 280 and the shared revoke routine at pc 683.
-/

abbrev revokeRoleRoleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev revokeRoleAccountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev revokeRoleRoleValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev revokeRoleAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (revokeRoleAccountWord I).toNat)

abbrev revokeRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (revokeRoleRoleValue I)).insert "account"
    (revokeRoleAccountValue I)

def revokeRoleRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

def revokeRoleAccountKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (revokeRoleAccountWord I).toNat)

def revokeRoleAdminSlot (I : ExecutionEnv) : UInt256 :=
  roleAdminSlot (revokeRoleRoleKey I)

def revokeRoleAdminWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminSlot I)

def revokeRoleAdminValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleAdminWord evm I))

def revokeRoleAdminKey (evm : EVM.State) (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleAdminWord evm I))

def revokeRoleSenderKey (evm : EVM.State) : KeyValue :=
  .address evm.executionEnv.source

def revokeRoleStoreWithAdmin (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (revokeRoleStore I).insert "adminRole" (revokeRoleAdminValue evm I)

def revokeRoleAdminHasRoleSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (revokeRoleAdminKey evm I) (revokeRoleSenderKey evm)

def revokeRoleTargetSlot (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (revokeRoleRoleKey I) (revokeRoleAccountKey I)

def revokeRoleClearLowByteWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def revokeRolePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)
    (revokeRoleClearLowByteWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)))

def revokeRoleAdminEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles", steps := [.mindex (revokeRoleRoleKey I), .field "adminRole"] }

def revokeRoleAdminHasRoleEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (revokeRoleAdminKey evm I), .field "hasRole",
      .mindex (revokeRoleSenderKey evm)] }

def revokeRoleTargetEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (revokeRoleRoleKey I), .field "hasRole",
      .mindex (revokeRoleAccountKey I)] }

theorem revokeRoleStore_role (I : ExecutionEnv) :
    (revokeRoleStore I).get? "role" = some (revokeRoleRoleValue I) := by
  rw [revokeRoleStore, store_get_ne _ _ (by decide), store_get_self]

theorem revokeRoleStore_account (I : ExecutionEnv) :
    (revokeRoleStore I).get? "account" = some (revokeRoleAccountValue I) := by
  rw [revokeRoleStore, store_get_self]

theorem revokeRoleStore_roles (I : ExecutionEnv) :
    (revokeRoleStore I).get? "_roles" = none := by
  rw [revokeRoleStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem revokeRoleStoreWithAdmin_role (evm : EVM.State) (I : ExecutionEnv) :
    (revokeRoleStoreWithAdmin evm I).get? "role" = some (revokeRoleRoleValue I) := by
  rw [revokeRoleStoreWithAdmin, store_get_ne _ _ (by decide), revokeRoleStore_role]

theorem revokeRoleStoreWithAdmin_account (evm : EVM.State) (I : ExecutionEnv) :
    (revokeRoleStoreWithAdmin evm I).get? "account" = some (revokeRoleAccountValue I) := by
  rw [revokeRoleStoreWithAdmin, store_get_ne _ _ (by decide), revokeRoleStore_account]

theorem revokeRoleStoreWithAdmin_adminRole (evm : EVM.State) (I : ExecutionEnv) :
    (revokeRoleStoreWithAdmin evm I).get? "adminRole" =
      some (revokeRoleAdminValue evm I) := by
  rw [revokeRoleStoreWithAdmin, store_get_self]

theorem revokeRoleStoreWithAdmin_roles (evm : EVM.State) (I : ExecutionEnv) :
    (revokeRoleStoreWithAdmin evm I).get? "_roles" = none := by
  rw [revokeRoleStoreWithAdmin, store_get_ne _ _ (by decide), revokeRoleStore_roles]

theorem evalExpr_revokeRole_role (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := revokeRoleStore I } evm
      (.var "role") = .ok (revokeRoleRoleValue I) := by
  rw [evalExpr?, revokeRoleStore_role]
  rfl

theorem evalExpr_revokeRole_account (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.var "account") = .ok (revokeRoleAccountValue I) := by
  rw [evalExpr?, revokeRoleStoreWithAdmin_account]
  rfl

theorem evalExpr_revokeRole_role_withAdmin (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.var "role") = .ok (revokeRoleRoleValue I) := by
  rw [evalExpr?, revokeRoleStoreWithAdmin_role]
  rfl

theorem evalExpr_revokeRole_adminRole (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.var "adminRole") = .ok (revokeRoleAdminValue evm I) := by
  rw [evalExpr?, revokeRoleStoreWithAdmin_adminRole]
  rfl

theorem evalStorageRef_revokeRole_admin (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := revokeRoleStore I } evm
      (roleAdminRef (.var "role")) = .ok (revokeRoleAdminEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleAdminRef,
    evalExpr_revokeRole_role, revokeRoleAdminEvaledRef, revokeRoleRoleValue, revokeRoleRoleKey,
    valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_revokeRole_admin (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := revokeRoleStore I } evm
      (.storage (roleAdminRef (.var "role"))) = .ok (revokeRoleAdminValue evm I) := by
  rw [evalExpr_storage_scalar (t := .bytes bytes32Width)
    (loc := bytes32Loc (revokeRoleAdminSlot I))
    (hbase := revokeRoleStore_roles I)
    (her := evalStorageRef_revokeRole_admin evm I)
    (hty := by
      simp [storageTypeAt?, revokeRoleAdminEvaledRef, contract, storageDecls, roleDataSt,
        bytes32St, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bytes32]
  simp [revokeRoleAdminValue, revokeRoleAdminWord, bytes32Width]

theorem evalStorageRef_revokeRole_adminHasRole (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (roleHasRoleRef (.var "adminRole") sender) =
        .ok (revokeRoleAdminHasRoleEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef, sender,
    envValue, evalExpr_revokeRole_adminRole, revokeRoleAdminHasRoleEvaledRef,
    revokeRoleAdminValue, revokeRoleAdminKey, revokeRoleSenderKey, valueToKey?,
    EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_revokeRole_adminHasRole_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "adminRole") sender)) = .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (revokeRoleAdminHasRoleSlot evm I))
    (hbase := revokeRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_revokeRole_adminHasRole evm I)
    (hty := by
      simp [storageTypeAt?, revokeRoleAdminHasRoleEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_revokeRole_adminHasRole_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminHasRoleSlot evm I))
        ⟨255⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "adminRole") sender)) = .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (revokeRoleAdminHasRoleSlot evm I))
    (hbase := revokeRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_revokeRole_adminHasRole evm I)
    (hty := by
      simp [storageTypeAt?, revokeRoleAdminHasRoleEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

theorem evalStorageRef_revokeRole_target (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (roleHasRoleRef (.var "role") (.var "account")) =
        .ok (revokeRoleTargetEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef,
    evalExpr_revokeRole_role_withAdmin, evalExpr_revokeRole_account, revokeRoleTargetEvaledRef,
    revokeRoleRoleValue, revokeRoleRoleKey, revokeRoleAccountValue, revokeRoleAccountKey,
    valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_revokeRole_target_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (revokeRoleTargetSlot I))
    (hbase := revokeRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_revokeRole_target evm I)
    (hty := by
      simp [storageTypeAt?, revokeRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_revokeRole_target_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (revokeRoleTargetSlot I))
    (hbase := revokeRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_revokeRole_target evm I)
    (hty := by
      simp [storageTypeAt?, revokeRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

-- PROMOTE -> Reasoning.Storage: packed `bool := false` at byte offset 0.
theorem revokeRolePackedSetFalseWord_eq (w : UInt256) :
    revokeRoleClearLowByteWord w = UInt256.ofNat (256 * (w.toNat / 256)) := by
  unfold revokeRoleClearLowByteWord
  apply u256_inj
  rw [SimpleAuction.simpleAuctionU256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  rw [SimpleAuction.simpleAuctionNatLandClearLow8 w.toNat hwlt]
  have hlt : w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : 256 * (w.toNat / 256) < UInt256.size := by
    simpa [Nat.mul_comm] using hlt
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (w.toNat / 256) 256]
  rw [ulit_toNat' _ hlt']

theorem revokeRolePackedSetFalseWord_toNat (w : UInt256) :
    (revokeRoleClearLowByteWord w).toNat = 256 * (w.toNat / 256) := by
  rw [revokeRolePackedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

theorem accessControlStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (revokeRoleClearLowByteWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord boolLoc revokeRoleClearLowByteWord
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 =
      [0] by native_decide]
  rw [fromBytes'_append, SimpleAuction.simpleAuctionFromBytes'_drop1_wordLE]
  simp [fromBytes']
  simpa [revokeRoleClearLowByteWord] using
    (revokeRolePackedSetFalseWord_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).symm

theorem revokeRoleAssignTarget (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm
      .storage (roleHasRoleRef (.var "role") (.var "account")) (.bool false) =
        .ok ({ contract := contract, locals := revokeRoleStoreWithAdmin evm I },
          revokeRolePostState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := revokeRoleTargetEvaledRef I) (ty := boolSt)
      (loc := boolLoc (revokeRoleTargetSlot I))
      (value := .bool false)
      (evm' := revokeRolePostState evm I)
      (hbase := revokeRoleStoreWithAdmin_roles evm I)
      (her := evalStorageRef_revokeRole_target evm I)
      (hty := by
        simp [storageTypeAt?, revokeRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
          boolSt, storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, revokeRoleTargetEvaledRef, revokeRoleTargetSlot])
      (hscalar := by trivial)
      (hstore := by
        exact accessControlStorageLocStore_bool_false_offset0 evm (revokeRoleTargetSlot I))

theorem accessControlRevokeRoleBodyReturns_write (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm (revokeRoleStore I) revokeRoleTransition.body
      (.returned { contract := contract, locals := revokeRoleStoreWithAdmin evm I }
        (revokeRolePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_revokeRole_admin evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_revokeRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (result := .ok
      ({ contract := contract, locals := revokeRoleStoreWithAdmin evm I } : Frame)
      (revokeRolePostState evm I))
      (evalExpr_revokeRole_target_true evm I htarget) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (revokeRoleAssignTarget evm I)) ?_
    exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlRevokeRoleBodyReturns_noop (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminHasRoleSlot evm I))
        ⟨255⟩ ≠ ⟨0⟩)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm (revokeRoleStore I) revokeRoleTransition.body
      (.returned { contract := contract, locals := revokeRoleStoreWithAdmin evm I } evm none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_revokeRole_admin evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_revokeRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := revokeRoleStoreWithAdmin evm I } : Frame) evm)
      (evalExpr_revokeRole_target_false evm I htarget) ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlRevokeRoleBodyReverts_admin (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (revokeRoleAdminHasRoleSlot evm I))
        ⟨255⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (revokeRoleStore I) revokeRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_revokeRole_admin evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_revokeRole_adminHasRole_false evm I hadmin))

theorem revokeRoleSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_revokeRole {cd : ByteArray}
    (hsel : ((⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some revokeRoleTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ : ByteArray) :=
    (accessControlByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition,
      hasRoleTransition, renounceRoleTransition])
    (post := [supportsInterfaceTransition]) rfl ?_
    (by rw [selectorOf, revokeRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, hasRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, renounceRoleSelectorBytes, hcd]; decide

-- PROMOTE -> Reasoning.ABI: fixed `bytes32,address` calldata decoder.
theorem decodeABIValue_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? bytes32 bytes start =
      some (.fixedBytes bytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [bytes32, bytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  simp [zeroPadding?, readBytes?]

theorem decodeABIValue_bytes32_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? bytes32 bytes start = none := by
  simp only [bytes32, bytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_neg hshort]

theorem decodeABIValues_bytes32_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [bytes32, addr] bytes 0 0 64 64 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, bytes32, addr, bytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  have hcanonVal :
      ↑(ABI.bytesToWord (List.take 32 (List.drop 32 bytes))).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  rw [if_pos hcanonVal]
  simp [UInt256.toNat]

theorem decodeABIValues_bytes32_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [bytes32, addr] bytes 0 0 64 64 = none := by
  simp only [decodeABIValues?, bytes32, addr, bytes32Width, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem decodeABIValues_bytes32_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [bytes32, addr] bytes 0 0 64 64 = none := by
  simp [decodeABIValues?, bytes32, addr, bytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  have hncVal :
      ¬ ↑(ABI.bytesToWord (List.take 32 (List.drop 32 bytes))).val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hnc
  rw [if_neg hncVal]
  simp

theorem accessControlDecode_revokeRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = some (revokeRoleStore I) := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = some (revokeRoleStore I)
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      revokeRoleAccountWord I := by
    simpa [revokeRoleAccountWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_ok (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          revokeRoleAccountWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanonAccount)]
  rw [if_neg (by
    rw [List.length_drop, htlen]
    omega : ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, revokeRoleStore, revokeRoleRoleValue,
    revokeRoleAccountValue]
  rw [hword36]

theorem accessControlDecode_revokeRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_none_short (bytes := I.calldata.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega)]

theorem accessControlDecode_revokeRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem accessControlDecode_revokeRole_none_noncanon_account {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncAccount : ¬ (revokeRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      revokeRoleAccountWord I := by
    simpa [revokeRoleAccountWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_none_noncanon (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          revokeRoleAccountWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hncAccount)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (I.calldata.toList.drop 4).length < 64)]

theorem accessControlRevokeRoleX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨280⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨922⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨294⟩, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨233⟩, push2 ⟨294⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨922⟩, jump (by jump_dest) ]⟩

theorem accessControlRevokeRoleX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨280⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
        [revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hclean : UInt256.eq (revokeRoleAccountWord I)
      (UInt256.land (revokeRoleAccountWord I) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanonAccount
  obtain ⟨_, _, rd922⟩ := accessControlRevokeRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact ⟨_, _, evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup3, calldataload, swap2, pop, push1 ⟨32⟩, dup4, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    dup2, eq, push2 ⟨968⟩, jumpiT (by
      rw [hmask]
      have hc : UInt256.eq
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
          (UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
            solcAddrMask) = ⟨1⟩ := by
        simpa [revokeRoleAccountWord, calldataWord] using hclean
      rw [hc]
      decide) (by jump_dest),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨491⟩, jump (by jump_dest) ]⟩

theorem accessControlRevokeRoleX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨280⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd922⟩ := accessControlRevokeRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlRevokeRoleX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨280⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd922⟩ := accessControlRevokeRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlRevokeRoleX_noncanon_account {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (revokeRoleAccountWord I)
      (UInt256.land (revokeRoleAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨280⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd922⟩ := accessControlRevokeRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup3, calldataload, swap2, pop, push1 ⟨32⟩, dup4, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    dup2, eq, push2 ⟨968⟩, jumpiNT (by
      rw [hmask]
      simpa [revokeRoleAccountWord, calldataWord] using hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

def revokeRoleStorageWordAt (σ : AccountMap) (owner : AccountAddress) (slot : UInt256) : UInt256 :=
  σ.find? owner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

def revokeRoleAdminStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  revokeRoleStorageWordAt σ I.codeOwner (revokeRoleAdminSlot I)

def revokeRoleSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def revokeRoleAdminHasRoleSlotFromWord (adminWord : UInt256) (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminWord)) (.address I.source)

def revokeRoleAdminHasRoleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  revokeRoleStorageWordAt σ I.codeOwner
    (revokeRoleAdminHasRoleSlotFromWord (revokeRoleAdminStorageWord σ I) I)

def revokeRoleTargetStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  revokeRoleStorageWordAt σ I.codeOwner (revokeRoleTargetSlot I)

def revokeRolePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (revokeRoleTargetSlot I)
    (revokeRoleClearLowByteWord (revokeRoleTargetStorageWord σ I))

theorem revokeRoleRoleKeyValueToWord {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (revokeRoleRoleKey I) = revokeRoleRoleWord I := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [revokeRoleRoleKey, keyValueToWord, bytes32Width, hlen]
  unfold revokeRoleRoleWord calldataWord
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide), ← byteArray_toList_eq I.calldata]

theorem revokeRoleKeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem revokeRoleKeyValueToWord_fixedBytes32 (w : UInt256) :
    keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) = w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [keyValueToWord, bytes32Width, hlen]
  apply u256_inj
  have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
    have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      h.trans (fromByteArrayBigEndian_toByteArray w)
  rw [EVM.Word.ofNat, hfrom]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem revokeRoleSourceWord_toNat (I : ExecutionEnv) :
    (revokeRoleSourceWord I).toNat = I.source.val := by
  unfold revokeRoleSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem revokeRoleKeyValueToWord_source (I : ExecutionEnv) :
    keyValueToWord (.address I.source) = revokeRoleSourceWord I := by
  apply u256_inj
  change I.source.val = (UInt256.ofNat I.source.val).toNat
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))]

noncomputable def revokeRoleWordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def revokeRoleWordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def revokeRoleTwoWordHashMem (key slot : UInt256) (mem : ByteArray) : ByteArray :=
  revokeRoleWordAt32Mem slot (revokeRoleWordAt0Mem key mem)

theorem revokeRoleWordAt0Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleWordAt0Mem word mem).size = 96 := by
  unfold revokeRoleWordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem revokeRoleWordAt32Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleWordAt32Mem word mem).size = 96 := by
  unfold revokeRoleWordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem revokeRoleTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleTwoWordHashMem key slot mem).size = 96 := by
  unfold revokeRoleTwoWordHashMem
  exact revokeRoleWordAt32Mem_size slot (revokeRoleWordAt0Mem_size key hmem)

theorem revokeRoleWordAt0Mem_read0 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleWordAt0Mem word mem).readWithPadding 0 32 = UInt256.toByteArray word := by
  unfold revokeRoleWordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray word).size ≤ 32
    rw [toByteArray_size])

theorem revokeRoleWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleWordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleWordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

theorem revokeRoleTwoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleTwoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold revokeRoleTwoWordHashMem revokeRoleWordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [revokeRoleWordAt0Mem_size key hmem]; omega) (by omega),
    revokeRoleWordAt0Mem_read0 key hmem]

theorem revokeRoleTwoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleTwoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold revokeRoleTwoWordHashMem revokeRoleWordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [revokeRoleWordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem revokeRoleTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleTwoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleTwoWordHashMem revokeRoleWordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [revokeRoleWordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [revokeRoleWordAt0Mem_size key hmem])]
  exact revokeRoleWordAt0Mem_read64 key hmem hread64

theorem revokeRoleTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleTwoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [revokeRoleTwoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (revokeRoleTwoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [revokeRoleTwoWordHashMem_size key slot hmem]; omega),
      revokeRoleTwoWordHashMem_read0 key slot hmem]
  have hright :
      (revokeRoleTwoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [revokeRoleTwoWordHashMem_size key slot hmem]; omega),
      revokeRoleTwoWordHashMem_read32 key slot hmem]
  rw [show (revokeRoleTwoWordHashMem key slot mem).extract 0 64 =
      (revokeRoleTwoWordHashMem key slot mem).extract 0 32 ++
        (revokeRoleTwoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

noncomputable def revokeRoleBaseHashMem (role : UInt256) : ByteArray :=
  revokeRoleTwoWordHashMem role ⟨0⟩ solcFreePtrMem

noncomputable def revokeRoleBaseSlot (role : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((revokeRoleBaseHashMem role).readWithPadding 0 64)))

noncomputable def revokeRoleHasRoleAccountMem (role account : UInt256) : ByteArray :=
  revokeRoleWordAt0Mem account (revokeRoleBaseHashMem role)

noncomputable def revokeRoleHasRoleSlotHashMem (role account : UInt256) : ByteArray :=
  revokeRoleWordAt32Mem (revokeRoleBaseSlot role) (revokeRoleHasRoleAccountMem role account)

noncomputable def revokeRoleBaseHashMemFrom (role : UInt256) (mem : ByteArray) : ByteArray :=
  revokeRoleTwoWordHashMem role ⟨0⟩ mem

noncomputable def revokeRoleHasRoleAccountMemFrom
    (role account : UInt256) (mem : ByteArray) : ByteArray :=
  revokeRoleWordAt0Mem account (revokeRoleBaseHashMemFrom role mem)

noncomputable def revokeRoleHasRoleSlotHashMemFrom
    (role account : UInt256) (mem : ByteArray) : ByteArray :=
  revokeRoleWordAt32Mem (revokeRoleBaseSlot role)
    (revokeRoleHasRoleAccountMemFrom role account mem)

theorem revokeRoleBaseHashMem_size (role : UInt256) :
    (revokeRoleBaseHashMem role).size = 96 := by
  unfold revokeRoleBaseHashMem
  exact revokeRoleTwoWordHashMem_size role ⟨0⟩ solcFreePtrMem_size

theorem revokeRoleHasRoleSlotHashMem_size (role account : UInt256) :
    (revokeRoleHasRoleSlotHashMem role account).size = 96 := by
  unfold revokeRoleHasRoleSlotHashMem
  apply revokeRoleWordAt32Mem_size
  unfold revokeRoleHasRoleAccountMem
  exact revokeRoleWordAt0Mem_size account (revokeRoleBaseHashMem_size role)

theorem revokeRoleBaseHashMemFrom_size {mem : ByteArray} (role : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleBaseHashMemFrom role mem).size = 96 := by
  unfold revokeRoleBaseHashMemFrom
  exact revokeRoleTwoWordHashMem_size role ⟨0⟩ hmem

theorem revokeRoleHasRoleSlotHashMemFrom_size {mem : ByteArray} (role account : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleHasRoleSlotHashMemFrom role account mem).size = 96 := by
  unfold revokeRoleHasRoleSlotHashMemFrom
  apply revokeRoleWordAt32Mem_size
  unfold revokeRoleHasRoleAccountMemFrom
  exact revokeRoleWordAt0Mem_size account (revokeRoleBaseHashMemFrom_size role hmem)

theorem revokeRoleBaseHashMem_read0_64 (role : UInt256) :
    (revokeRoleBaseHashMem role).readWithPadding 0 64 =
      UInt256.toByteArray role ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold revokeRoleBaseHashMem
  exact revokeRoleTwoWordHashMem_read0_64 role ⟨0⟩ solcFreePtrMem_size

theorem revokeRoleBaseHashMem_read64 (role : UInt256) :
    (revokeRoleBaseHashMem role).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleBaseHashMem
  exact revokeRoleTwoWordHashMem_read64 role ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem revokeRoleBaseHashMemFrom_read0_64 {mem : ByteArray} (role : UInt256)
    (hmem : mem.size = 96) :
    (revokeRoleBaseHashMemFrom role mem).readWithPadding 0 64 =
      UInt256.toByteArray role ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold revokeRoleBaseHashMemFrom
  exact revokeRoleTwoWordHashMem_read0_64 role ⟨0⟩ hmem

theorem revokeRoleHasRoleSlotHashMem_read0_64 (role account : UInt256) :
    (revokeRoleHasRoleSlotHashMem role account).readWithPadding 0 64 =
      UInt256.toByteArray account ++ UInt256.toByteArray (revokeRoleBaseSlot role) := by
  change (revokeRoleTwoWordHashMem account (revokeRoleBaseSlot role)
      (revokeRoleBaseHashMem role)).readWithPadding 0 64 =
    UInt256.toByteArray account ++ UInt256.toByteArray (revokeRoleBaseSlot role)
  exact revokeRoleTwoWordHashMem_read0_64 account (revokeRoleBaseSlot role)
    (revokeRoleBaseHashMem_size role)

theorem revokeRoleHasRoleSlotHashMemFrom_read0_64 {mem : ByteArray}
    (role account : UInt256) (hmem : mem.size = 96) :
    (revokeRoleHasRoleSlotHashMemFrom role account mem).readWithPadding 0 64 =
      UInt256.toByteArray account ++ UInt256.toByteArray (revokeRoleBaseSlot role) := by
  change (revokeRoleTwoWordHashMem account (revokeRoleBaseSlot role)
      (revokeRoleBaseHashMemFrom role mem)).readWithPadding 0 64 =
    UInt256.toByteArray account ++ UInt256.toByteArray (revokeRoleBaseSlot role)
  exact revokeRoleTwoWordHashMem_read0_64 account (revokeRoleBaseSlot role)
    (revokeRoleBaseHashMemFrom_size role hmem)

theorem revokeRoleHasRoleSlotHashMem_read64 (role account : UInt256) :
    (revokeRoleHasRoleSlotHashMem role account).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change (revokeRoleTwoWordHashMem account (revokeRoleBaseSlot role)
      (revokeRoleBaseHashMem role)).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  apply revokeRoleTwoWordHashMem_read64
  · exact revokeRoleBaseHashMem_size role
  · unfold revokeRoleBaseHashMem
    exact revokeRoleTwoWordHashMem_read64 role ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64

theorem revokeRoleHasRoleSlotHashMemFrom_read64 {mem : ByteArray}
    (role account : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleHasRoleSlotHashMemFrom role account mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change (revokeRoleTwoWordHashMem account (revokeRoleBaseSlot role)
      (revokeRoleBaseHashMemFrom role mem)).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  apply revokeRoleTwoWordHashMem_read64
  · exact revokeRoleBaseHashMemFrom_size role hmem
  · unfold revokeRoleBaseHashMemFrom
    exact revokeRoleTwoWordHashMem_read64 role ⟨0⟩ hmem hread64

theorem revokeRoleHasRoleSlotHashMem_mload64 (role account : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revokeRoleHasRoleSlotHashMem role account).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((revokeRoleHasRoleSlotHashMem role account).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revokeRoleHasRoleSlotHashMem_size]; decide) (by decide)
    (revokeRoleHasRoleSlotHashMem_read64 role account)

theorem revokeRoleHasRoleSlotHashMemFrom_mload64 {mem : ByteArray}
    (role account : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (revokeRoleHasRoleSlotHashMemFrom role account mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((revokeRoleHasRoleSlotHashMemFrom role account mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revokeRoleHasRoleSlotHashMemFrom_size _ _ hmem]; decide)
    (by decide) (revokeRoleHasRoleSlotHashMemFrom_read64 role account hmem hread64)

theorem revokeRoleBaseKeccakSlot (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    revokeRoleBaseSlot (revokeRoleRoleWord I) =
      roleDataSlot (revokeRoleRoleKey I) := by
  unfold revokeRoleBaseSlot roleDataSlot mapSlot
  rw [revokeRoleBaseHashMem_read0_64, revokeRoleRoleKeyValueToWord hsz68]
  exact mappingSlot_single (revokeRoleRoleWord I) ⟨0⟩

theorem revokeRoleAddSlot_eq (slot : UInt256) :
    EVM.word (slot.toNat + 1) = slot + (⟨1⟩ : UInt256) := by
  apply u256_inj
  rw [uadd_toNat]
  change (slot.toNat + 1) % UInt256.size = (slot.toNat + 1) % UInt256.size
  rfl

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `UInt256` addition is commutative.
theorem revokeRoleU256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  simp [uadd_toNat, Nat.add_comm]

theorem revokeRoleAdminSlot_evm (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    revokeRoleAdminSlot I = revokeRoleBaseSlot (revokeRoleRoleWord I) + ⟨1⟩ := by
  unfold revokeRoleAdminSlot roleAdminSlot roleDataSlot mapSlot addSlot
  rw [revokeRoleRoleKeyValueToWord hsz68]
  rw [revokeRoleAddSlot_eq]
  unfold revokeRoleBaseSlot
  rw [revokeRoleBaseHashMem_read0_64]
  rw [uInt256OfByteArray_eq]

theorem revokeRoleBaseKeccakSlot_fixedBytes32 (role : UInt256) :
    revokeRoleBaseSlot role =
      roleDataSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role)) := by
  unfold revokeRoleBaseSlot roleDataSlot mapSlot
  rw [revokeRoleBaseHashMem_read0_64, revokeRoleKeyValueToWord_fixedBytes32]
  exact mappingSlot_single role ⟨0⟩

theorem revokeRoleTargetKeccakSlot (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMem (revokeRoleRoleWord I) (revokeRoleAccountWord I))
          |>.readWithPadding 0 64)))
      = revokeRoleTargetSlot I := by
  rw [revokeRoleHasRoleSlotHashMem_read0_64, revokeRoleBaseKeccakSlot I hsz68]
  unfold revokeRoleTargetSlot roleHasRoleSlot mapSlot
  rw [show keyValueToWord (revokeRoleAccountKey I) = revokeRoleAccountWord I by
    simpa [revokeRoleAccountKey] using
      revokeRoleKeyValueToWord_address_of_canonical (revokeRoleAccountWord I) hcanonAccount]
  exact mappingSlot_single (revokeRoleAccountWord I)
    (roleDataSlot (revokeRoleRoleKey I))

theorem revokeRoleTargetKeccakSlotFrom (I : ExecutionEnv) (mem : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hmem : mem.size = 96)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I)
          (revokeRoleAccountWord I) mem).readWithPadding 0 64)))
      = revokeRoleTargetSlot I := by
  rw [revokeRoleHasRoleSlotHashMemFrom_read0_64 _ _ hmem, revokeRoleBaseKeccakSlot I hsz68]
  unfold revokeRoleTargetSlot roleHasRoleSlot mapSlot
  rw [show keyValueToWord (revokeRoleAccountKey I) = revokeRoleAccountWord I by
    simpa [revokeRoleAccountKey] using
      revokeRoleKeyValueToWord_address_of_canonical (revokeRoleAccountWord I) hcanonAccount]
  exact mappingSlot_single (revokeRoleAccountWord I)
    (roleDataSlot (revokeRoleRoleKey I))

theorem revokeRoleTargetSlot_fixedBytes32 (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus) :
    revokeRoleTargetSlot I =
      roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleRoleWord I)))
        (.address (AccountAddress.ofNat (revokeRoleAccountWord I).toNat)) := by
  unfold revokeRoleTargetSlot roleHasRoleSlot roleDataSlot mapSlot
  rw [revokeRoleRoleKeyValueToWord hsz68, revokeRoleKeyValueToWord_fixedBytes32]
  rw [show keyValueToWord (revokeRoleAccountKey I) = revokeRoleAccountWord I by
    simpa [revokeRoleAccountKey] using
      revokeRoleKeyValueToWord_address_of_canonical (revokeRoleAccountWord I) hcanonAccount]
  rw [revokeRoleKeyValueToWord_address_of_canonical _ hcanonAccount]

theorem revokeRoleAdminHasRoleKeccakSlot (adminRole account : UInt256)
    (hcanonAccount : account.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMem adminRole account)
          |>.readWithPadding 0 64)))
      =
        roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminRole))
          (.address (AccountAddress.ofNat account.toNat)) := by
  rw [revokeRoleHasRoleSlotHashMem_read0_64, revokeRoleBaseKeccakSlot_fixedBytes32]
  unfold roleHasRoleSlot mapSlot
  rw [revokeRoleKeyValueToWord_address_of_canonical _ hcanonAccount]
  exact mappingSlot_single account
    (roleDataSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminRole)))

theorem revokeRoleAdminHasRoleKeccakSlotFrom (adminRole account : UInt256) (mem : ByteArray)
    (hmem : mem.size = 96) (hcanonAccount : account.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom adminRole account mem)
          |>.readWithPadding 0 64)))
      =
        roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminRole))
          (.address (AccountAddress.ofNat account.toNat)) := by
  rw [revokeRoleHasRoleSlotHashMemFrom_read0_64 _ _ hmem,
    revokeRoleBaseKeccakSlot_fixedBytes32]
  unfold roleHasRoleSlot mapSlot
  rw [revokeRoleKeyValueToWord_address_of_canonical _ hcanonAccount]
  exact mappingSlot_single account
    (roleDataSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminRole)))

theorem accessControlX_hasRole_internal {cA gh bl σ σ₀ A I} {g : Sat256}
    {role account ret : UInt256} {R : List UInt256} {mem0 : ByteArray}
    (hmem0 : mem0.size = 96)
    (hread64 : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonAccount : account.toNat < EVM.addressModulus)
    (hret : (D_J accessControlBenchBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024)
    (hslot : UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom role account mem0).readWithPadding 0 64))) =
      roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
        (.address (AccountAddress.ofNat account.toNat)))
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨451⟩ (account :: role :: ret :: R)
      mem0 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.land
        (revokeRoleStorageWordAt σ I.codeOwner
          (roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
            (.address (AccountAddress.ofNat account.toNat)))) ⟨255⟩ :: R)
      (revokeRoleHasRoleSlotHashMemFrom role account mem0) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd451⟩ := hreach
  have rd465 := evm_run rd451 with [
    jumpdest, push0, swap2, dup3,
    raw mstore 0 (revokeRoleWordAt0Mem role mem0)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, dup2,
    raw mstore 0 (revokeRoleBaseHashMemFrom role mem0) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup5,
    raw keccak256 0 (revokeRoleBaseSlot role) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        change UInt256.ofNat (fromByteArrayBigEndian
            (ffi.KEC ((revokeRoleBaseHashMemFrom role mem0).readWithPadding 0 64))) =
          revokeRoleBaseSlot role
        unfold revokeRoleBaseSlot
        rw [revokeRoleBaseHashMemFrom_read0_64 role hmem0,
          revokeRoleBaseHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd485 := evm_run rd465 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap4, swap1, swap4, and, dup5,
    raw mstore 0 (revokeRoleHasRoleAccountMemFrom role account mem0)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonAccount]
        rfl)
      (by decide) (by evm_ov),
    swap2, swap1,
    raw mstore 0 (revokeRoleHasRoleSlotHashMemFrom role account mem0)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0
      (roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
        (.address (AccountAddress.ofNat account.toNat)))
      (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd486⟩ := rd485.sload (by decide) (by evm_ov)
  have hmaskComm :
      UInt256.land ⟨255⟩
          (revokeRoleStorageWordAt σ I.codeOwner
            (roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
              (.address (AccountAddress.ofNat account.toNat)))) =
        UInt256.land
          (revokeRoleStorageWordAt σ I.codeOwner
            (roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
              (.address (AccountAddress.ofNat account.toNat)))) ⟨255⟩ := by
    exact SimpleAuction.simpleAuctionU256_land_comm ⟨255⟩ _
  have rdret := evm_run rd486 with [push1 ⟨255⟩, and, swap1, jump hret]
  change RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ret
    (UInt256.land ⟨255⟩
      (revokeRoleStorageWordAt σ I.codeOwner
        (roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE role))
          (.address (AccountAddress.ofNat account.toNat)))) :: R)
    (revokeRoleHasRoleSlotHashMemFrom role account mem0) (UInt256.ofNat 3) ByteArray.empty
    (cA, σ) _ _ at rdret
  rw [hmaskComm] at rdret
  exact ⟨_, _, by
    simpa [revokeRoleStorageWordAt] using rdret⟩

theorem revokeRoleSourceWord_canonical (I : ExecutionEnv) :
    (revokeRoleSourceWord I).toNat < EVM.addressModulus := by
  rw [revokeRoleSourceWord_toNat]
  exact I.source.isLt

theorem revokeRoleSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (revokeRoleSourceWord I).toNat = I.source := by
  unfold AccountAddress.ofNat
  apply Fin.ext
  rw [revokeRoleSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic `LOG4` reachability.
def revokeRoleStLog4 (s : State) (a b c d e f : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d, e, f], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG4)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 4 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic `LOG4` reachability.
theorem revokeRoleLog4_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG4, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG4
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (revokeRoleStLog4 s a b c d e f t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG4, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log4 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, revokeRoleStLog4]

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic `LOG4` reachability.
theorem RD.revokeRoleLog4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG4, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: f :: t →
        memoryExpansionCost s .LOG4 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 4 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG4 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := revokeRoleLog4_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨revokeRoleStLog4 s a b c d e f t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [revokeRoleStLog4]
        exact hcode
      · simp only [revokeRoleStLog4]
        rw [hpc]
      · simp only [revokeRoleStLog4]
      · simp only [revokeRoleStLog4, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [revokeRoleStLog4]
        exact hmem
      · simp only [revokeRoleStLog4]
        rw [haw, hawout]
      · simp only [revokeRoleStLog4]
        exact hrdata
      · simp only [revokeRoleStLog4]
        exact hacc
      · simp only [revokeRoleStLog4]
        exact hee
      · simp only [revokeRoleStLog4]
        exact hworld

def revokeRoleUnauthorizedSelector : UInt256 :=
  UInt256.shiftLeft (⟨0xe2517d3f⟩ : UInt256) ⟨224⟩

def revokeRoleRevokedTopic : UInt256 :=
  ⟨111369887473982945697897258602409287065386435722986207154590940387224246097691⟩

noncomputable def revokeRoleUnauthorizedAccountMem (account : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask account)).write 0
    (solcReturnMem revokeRoleUnauthorizedSelector) 132 32

noncomputable def revokeRoleUnauthorizedMem (account role : UInt256) : ByteArray :=
  (UInt256.toByteArray role).write 0 (revokeRoleUnauthorizedAccountMem account) 164 32

noncomputable def revokeRoleUnauthorizedSelectorMemFrom (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray revokeRoleUnauthorizedSelector).write 0 mem 128 32

noncomputable def revokeRoleUnauthorizedAccountMemFrom
    (account : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask account)).write 0
    (revokeRoleUnauthorizedSelectorMemFrom mem) 132 32

noncomputable def revokeRoleUnauthorizedMemFrom
    (account role : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray role).write 0 (revokeRoleUnauthorizedAccountMemFrom account mem) 164 32

theorem revokeRoleUnauthorizedAccountMem_size (account : UInt256) :
    (revokeRoleUnauthorizedAccountMem account).size = 164 := by
  unfold revokeRoleUnauthorizedAccountMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  rw [show ((solcReturnMem revokeRoleUnauthorizedSelector).extract (132 + 32) 160).size =
      0 by
    rw [ByteArray.size_extract, solcReturnMem_size]
    norm_num]
  omega

theorem revokeRoleUnauthorizedMem_size (account role : UInt256) :
    (revokeRoleUnauthorizedMem account role).size = 196 := by
  unfold revokeRoleUnauthorizedMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedAccountMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, revokeRoleUnauthorizedAccountMem_size, toByteArray_size]
  rw [show ((revokeRoleUnauthorizedAccountMem account).extract (164 + 32) 164).size =
      0 by
    rw [ByteArray.size_extract, revokeRoleUnauthorizedAccountMem_size]
    norm_num]
  omega

theorem revokeRoleUnauthorizedSelectorMemFrom_size {mem : ByteArray}
    (hmem : mem.size = 96) :
    (revokeRoleUnauthorizedSelectorMemFrom mem).size = 160 := by
  unfold revokeRoleUnauthorizedSelectorMemFrom
  rw [toByteArray_write_eq revokeRoleUnauthorizedSelector mem 128
      (by rw [hmem]; omega) (by rw [hmem]; native_decide),
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    USize.toNat_ofNat_of_lt' (by rw [hmem]; native_decide), hmem, toByteArray_size]

theorem revokeRoleUnauthorizedAccountMemFrom_size {mem : ByteArray}
    (account : UInt256) (hmem : mem.size = 96) :
    (revokeRoleUnauthorizedAccountMemFrom account mem).size = 164 := by
  unfold revokeRoleUnauthorizedAccountMemFrom
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedSelectorMemFrom_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, revokeRoleUnauthorizedSelectorMemFrom_size hmem, toByteArray_size]
  rw [show ((revokeRoleUnauthorizedSelectorMemFrom mem).extract (132 + 32) 160).size =
      0 by
    rw [ByteArray.size_extract, revokeRoleUnauthorizedSelectorMemFrom_size hmem]
    norm_num]
  omega

theorem revokeRoleUnauthorizedMemFrom_size {mem : ByteArray}
    (account role : UInt256) (hmem : mem.size = 96) :
    (revokeRoleUnauthorizedMemFrom account role mem).size = 196 := by
  unfold revokeRoleUnauthorizedMemFrom
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedAccountMemFrom_size account hmem]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, revokeRoleUnauthorizedAccountMemFrom_size account hmem,
    toByteArray_size]
  rw [show ((revokeRoleUnauthorizedAccountMemFrom account mem).extract (164 + 32) 164).size =
      0 by
    rw [ByteArray.size_extract, revokeRoleUnauthorizedAccountMemFrom_size account hmem]
    norm_num]
  omega

theorem revokeRoleUnauthorizedAccountMem_read64 (account : UInt256) :
    (revokeRoleUnauthorizedAccountMem account).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleUnauthorizedAccountMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
  exact solcReturnMem_read64 revokeRoleUnauthorizedSelector

theorem revokeRoleUnauthorizedMem_read64 (account role : UInt256) :
    (revokeRoleUnauthorizedMem account role).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleUnauthorizedMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedAccountMem_size]) (by omega)]
  exact revokeRoleUnauthorizedAccountMem_read64 account

theorem revokeRoleUnauthorizedSelectorMemFrom_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleUnauthorizedSelectorMemFrom mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleUnauthorizedSelectorMemFrom
  rw [toByteArray_write_eq revokeRoleUnauthorizedSelector mem 128
      (by rw [hmem]; omega) (by rw [hmem]; native_decide)]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt' (by rw [hmem]; native_decide), hmem, toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' (by rw [hmem]; native_decide), hmem]
    norm_num)]
  rw [extract_append_left _ _ _ _ (by rw [hmem])]
  rw [← readWithPadding_eq_extract mem 64 (by rw [hmem])]
  exact hread64

theorem revokeRoleUnauthorizedAccountMemFrom_read64 {mem : ByteArray}
    (account : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleUnauthorizedAccountMemFrom account mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleUnauthorizedAccountMemFrom
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedSelectorMemFrom_size hmem]; omega) (by omega)]
  exact revokeRoleUnauthorizedSelectorMemFrom_read64 hmem hread64

theorem revokeRoleUnauthorizedMemFrom_read64 {mem : ByteArray}
    (account role : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (revokeRoleUnauthorizedMemFrom account role mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold revokeRoleUnauthorizedMemFrom
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [revokeRoleUnauthorizedAccountMemFrom_size account hmem]) (by omega)]
  exact revokeRoleUnauthorizedAccountMemFrom_read64 account hmem hread64

theorem revokeRoleUnauthorizedMem_mload64 (account role : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revokeRoleUnauthorizedMem account role).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revokeRoleUnauthorizedMem account role).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revokeRoleUnauthorizedMem_size]; decide) (by decide)
    (revokeRoleUnauthorizedMem_read64 account role)

theorem revokeRoleUnauthorizedMemFrom_mload64 {mem : ByteArray}
    (account role : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revokeRoleUnauthorizedMemFrom account role mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revokeRoleUnauthorizedMemFrom account role mem).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revokeRoleUnauthorizedMemFrom_size _ _ hmem]; decide)
    (by decide) (revokeRoleUnauthorizedMemFrom_read64 account role hmem hread64)

theorem accessControlRevokeRoleX_adminLoaded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨491⟩
      [revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
        revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd491⟩ := hreach
  have hslotRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleBaseHashMem (revokeRoleRoleWord I)).readWithPadding 0 64))) =
        revokeRoleBaseSlot (revokeRoleRoleWord I) := rfl
  have rd508pre := evm_run rd491 with [
    jumpdest, push0, dup3, dup2,
    raw mstore 0 (revokeRoleWordAt0Mem (revokeRoleRoleWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revokeRoleBaseSlot (revokeRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hslotRaw (by decide) (by evm_ov),
    push1 ⟨1⟩, add]
  obtain ⟨_, _, rd509₀⟩ := rd508pre.sload (by decide) (by evm_ov)
  have rd509 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I)
        (⟨491⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
                      ⟨1⟩ +
                    ⟨1⟩ +
                  ⟨1⟩ +
                UInt256.ofNat 2 +
              ⟨1⟩ +
            ⟨1⟩ +
          UInt256.ofNat 2 +
        ⟨1⟩ +
      ⟨1⟩)
        [revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
          ⟨233⟩, sel]
        (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [revokeRoleAdminStorageWord, revokeRoleAdminSlot_evm I hsz68,
        revokeRoleU256_add_comm] using rd509₀⟩
  obtain ⟨_, _, rd509⟩ := rd509
  exact ⟨_, _, evm_run rd509 with [
    push2 ⟨517⟩, dup2, push2 ⟨527⟩, jump (by jump_dest) ]⟩

theorem accessControlRevokeRoleX_onlyRole_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hadmin :
      UInt256.land (revokeRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
        revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨517⟩
      [revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
        (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd527⟩ := hreach
  have rd788 := evm_run rd527 with [
    jumpdest, push2 ⟨537⟩, dup2, caller, push2 ⟨788⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd788 with [
    jumpdest, push2 ⟨798⟩, dup3, dup3, push2 ⟨451⟩, jump (by jump_dest) ]
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨798⟩,
          revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨537⟩,
          revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [revokeRoleSourceWord] using rd451⟩
  have hslot := revokeRoleAdminHasRoleKeccakSlotFrom (revokeRoleAdminStorageWord σ I)
    (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I))
    (revokeRoleBaseHashMem_size _) (revokeRoleSourceWord_canonical I)
  obtain ⟨_, _, rd798₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := revokeRoleAdminStorageWord σ I)
    (account := revokeRoleSourceWord I) (ret := ⟨798⟩)
    (mem0 := revokeRoleBaseHashMem (revokeRoleRoleWord I))
    (R := [revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨537⟩,
      revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
      revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel])
    (revokeRoleBaseHashMem_size _) (revokeRoleBaseHashMem_read64 _)
    (revokeRoleSourceWord_canonical I) (by jump_dest) (by simp) hslot rd451'
  have rd798 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
        (UInt256.land (revokeRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ::
          revokeRoleSourceWord I :: revokeRoleAdminStorageWord σ I :: ⟨537⟩ ::
          revokeRoleAdminStorageWord σ I :: ⟨517⟩ :: revokeRoleAdminStorageWord σ I ::
          revokeRoleAccountWord I :: revokeRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        (revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
          (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [revokeRoleAdminHasRoleStorageWord, revokeRoleAdminHasRoleSlotFromWord,
        revokeRoleSource_ofNat I] using rd798₀⟩
  obtain ⟨_, _, rd798⟩ := rd798
  have rd849 := evm_run rd798 with [
    jumpdest, push2 ⟨849⟩, jumpiT hadmin (by jump_dest) ]
  have rd537 := evm_run rd849 with [
    jumpdest, pop, pop, jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd537 with [
    jumpdest, pop, jump (by jump_dest) ]⟩

theorem accessControlRevokeRoleX_onlyRole_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hadmin :
      UInt256.land (revokeRoleAdminHasRoleStorageWord σ I) ⟨255⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
        revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (revokeRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd527⟩ := hreach
  have rd788 := evm_run rd527 with [
    jumpdest, push2 ⟨537⟩, dup2, caller, push2 ⟨788⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd788 with [
    jumpdest, push2 ⟨798⟩, dup3, dup3, push2 ⟨451⟩, jump (by jump_dest) ]
  let memAdminBase := revokeRoleBaseHashMem (revokeRoleRoleWord I)
  let memAdmin :=
    revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
      (revokeRoleSourceWord I) memAdminBase
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨798⟩,
          revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨537⟩,
          revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
        memAdminBase (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memAdminBase, revokeRoleSourceWord] using rd451⟩
  have hslot := revokeRoleAdminHasRoleKeccakSlotFrom (revokeRoleAdminStorageWord σ I)
    (revokeRoleSourceWord I) memAdminBase
    (revokeRoleBaseHashMem_size _) (revokeRoleSourceWord_canonical I)
  obtain ⟨_, _, rd798₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := revokeRoleAdminStorageWord σ I)
    (account := revokeRoleSourceWord I) (ret := ⟨798⟩)
    (mem0 := memAdminBase)
    (R := [revokeRoleSourceWord I, revokeRoleAdminStorageWord σ I, ⟨537⟩,
      revokeRoleAdminStorageWord σ I, ⟨517⟩, revokeRoleAdminStorageWord σ I,
      revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel])
    (revokeRoleBaseHashMem_size _) (revokeRoleBaseHashMem_read64 _)
    (revokeRoleSourceWord_canonical I) (by jump_dest) (by simp) hslot rd451'
  have rd798 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
        (UInt256.land (revokeRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ::
          revokeRoleSourceWord I :: revokeRoleAdminStorageWord σ I :: ⟨537⟩ ::
          revokeRoleAdminStorageWord σ I :: ⟨517⟩ :: revokeRoleAdminStorageWord σ I ::
          revokeRoleAccountWord I :: revokeRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        memAdmin (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [memAdmin, memAdminBase, revokeRoleAdminHasRoleStorageWord,
        revokeRoleAdminHasRoleSlotFromWord, revokeRoleSource_ofNat I] using rd798₀⟩
  obtain ⟨_, _, rd798⟩ := rd798
  have hmemAdmin : memAdmin.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ (revokeRoleBaseHashMem_size _)
  have hreadAdmin : memAdmin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _
      (revokeRoleBaseHashMem_size _) (revokeRoleBaseHashMem_read64 _)
  have hloadAdmin64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memAdmin.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memAdmin.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemAdmin]; decide) (by decide) hreadAdmin
  have rd803 := evm_run rd798 with [
    jumpdest, push2 ⟨849⟩, jumpiNT (by rw [hadmin]) ]
  have rd815 := evm_run rd803 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost hloadAdmin64
      (by decide) (by evm_ov),
    push4 ⟨3796991295⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (revokeRoleUnauthorizedSelectorMemFrom memAdmin)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd830pre := evm_run rd815 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push1 ⟨4⟩, dup3, add ]
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd830pre
  have hsourceMaskComm :
      UInt256.land (revokeRoleSourceWord I) solcAddrMask =
        UInt256.land solcAddrMask (revokeRoleSourceWord I) := by
    exact SimpleAuction.simpleAuctionU256_land_comm (revokeRoleSourceWord I) solcAddrMask
  have rd830 := evm_run rd830pre with [
    raw mstore 3 (revokeRoleUnauthorizedAccountMemFrom (revokeRoleSourceWord I) memAdmin)
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide, hsourceMaskComm]
        rfl)
      (by decide) (by evm_ov) ]
  have rd837 := evm_run rd830 with [
    push1 ⟨36⟩, dup2, add, dup4, swap1,
    raw mstore 3
      (revokeRoleUnauthorizedMemFrom (revokeRoleSourceWord I)
        (revokeRoleAdminStorageWord σ I) memAdmin)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd848 := evm_run rd837 with [
    push1 ⟨68⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide) mem_cost
      (revokeRoleUnauthorizedMemFrom_mload64 (revokeRoleSourceWord I)
        (revokeRoleAdminStorageWord σ I) hmemAdmin hreadAdmin)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen68 : ((⟨68⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨68⟩ := by
    decide
  have rd848' := rd848
  rw [hlen68] at rd848'
  exact rd848'.rev 0 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by simp)

theorem accessControlRevokeRoleX_revoke_noop {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus)
    (htarget : UInt256.land (revokeRoleTargetStorageWord σ I) ⟨255⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨517⟩
      [revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
        (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) ByteArray.empty := by
  obtain ⟨_, _, rd517⟩ := hreach
  have rd683 := evm_run rd517 with [
    jumpdest, push2 ⟨389⟩, dup4, dup4, push2 ⟨683⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd683 with [
    jumpdest, push0, push2 ⟨694⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  let memOnlyRole :=
    revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
      (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I))
  have hmemOnlyRole : memOnlyRole.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _
      (revokeRoleBaseHashMem_size (revokeRoleRoleWord I))
  have hreadOnlyRole :
      memOnlyRole.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _
      (revokeRoleBaseHashMem_size (revokeRoleRoleWord I))
      (revokeRoleBaseHashMem_read64 (revokeRoleRoleWord I))
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨694⟩, ⟨0⟩,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨389⟩,
          revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
          ⟨233⟩, sel]
        memOnlyRole (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memOnlyRole] using rd451⟩
  have hslot := revokeRoleTargetKeccakSlotFrom I memOnlyRole hsz68 hmemOnlyRole hcanonAccount
  have htargetSlotEq := revokeRoleTargetSlot_fixedBytes32 I hsz68 hcanonAccount
  have hslot' :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I)
            (revokeRoleAccountWord I) memOnlyRole).readWithPadding 0 64))) =
        roleHasRoleSlot
          (.fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleRoleWord I)))
          (.address (AccountAddress.ofNat (revokeRoleAccountWord I).toNat)) := by
    rw [hslot, htargetSlotEq]
  obtain ⟨_, _, rd694₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := revokeRoleRoleWord I) (account := revokeRoleAccountWord I)
    (ret := ⟨694⟩) (mem0 := memOnlyRole)
    (R := [⟨0⟩, revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨389⟩,
      revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
      ⟨233⟩, sel])
    hmemOnlyRole hreadOnlyRole hcanonAccount (by jump_dest) (by simp) hslot' rd451'
  have rd694 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
        (UInt256.land (revokeRoleTargetStorageWord σ I) ⟨255⟩ :: ⟨0⟩ ::
          revokeRoleAccountWord I :: revokeRoleRoleWord I :: ⟨389⟩ ::
          revokeRoleAdminStorageWord σ I :: revokeRoleAccountWord I :: revokeRoleRoleWord I ::
          ⟨233⟩ :: sel :: [])
        (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
          memOnlyRole)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [revokeRoleTargetStorageWord, revokeRoleStorageWordAt, ← htargetSlotEq]
        using rd694₀⟩
  obtain ⟨_, _, rd694⟩ := rd694
  have rd233 := evm_run rd694 with [
    jumpdest, iszero, push2 ⟨676⟩, jumpiT (by rw [htarget]; decide) (by jump_dest),
    jumpdest, pop, push0, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlRevokeRoleX_revoke_write {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus)
    (htarget : UInt256.land (revokeRoleTargetStorageWord σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨517⟩
      [revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
        (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, revokeRolePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd517⟩ := hreach
  have rd683 := evm_run rd517 with [
    jumpdest, push2 ⟨389⟩, dup4, dup4, push2 ⟨683⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd683 with [
    jumpdest, push0, push2 ⟨694⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  let memOnlyRole :=
    revokeRoleHasRoleSlotHashMemFrom (revokeRoleAdminStorageWord σ I)
      (revokeRoleSourceWord I) (revokeRoleBaseHashMem (revokeRoleRoleWord I))
  have hmemOnlyRole : memOnlyRole.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _
      (revokeRoleBaseHashMem_size (revokeRoleRoleWord I))
  have hreadOnlyRole :
      memOnlyRole.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _
      (revokeRoleBaseHashMem_size (revokeRoleRoleWord I))
      (revokeRoleBaseHashMem_read64 (revokeRoleRoleWord I))
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨694⟩, ⟨0⟩,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨389⟩,
          revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
          ⟨233⟩, sel]
        memOnlyRole (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memOnlyRole] using rd451⟩
  have htargetSlotEq := revokeRoleTargetSlot_fixedBytes32 I hsz68 hcanonAccount
  have hslotBase := revokeRoleTargetKeccakSlotFrom I memOnlyRole hsz68 hmemOnlyRole hcanonAccount
  have hslot' :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I)
            (revokeRoleAccountWord I) memOnlyRole).readWithPadding 0 64))) =
        roleHasRoleSlot
          (.fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleRoleWord I)))
          (.address (AccountAddress.ofNat (revokeRoleAccountWord I).toNat)) := by
    rw [hslotBase, htargetSlotEq]
  obtain ⟨_, _, rd694₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := revokeRoleRoleWord I) (account := revokeRoleAccountWord I)
    (ret := ⟨694⟩) (mem0 := memOnlyRole)
    (R := [⟨0⟩, revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨389⟩,
      revokeRoleAdminStorageWord σ I, revokeRoleAccountWord I, revokeRoleRoleWord I,
      ⟨233⟩, sel])
    hmemOnlyRole hreadOnlyRole hcanonAccount (by jump_dest) (by simp) hslot' rd451'
  let memTarget :=
    revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
      memOnlyRole
  have rd694 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
        (UInt256.land (revokeRoleTargetStorageWord σ I) ⟨255⟩ :: ⟨0⟩ ::
          revokeRoleAccountWord I :: revokeRoleRoleWord I :: ⟨389⟩ ::
          revokeRoleAdminStorageWord σ I :: revokeRoleAccountWord I :: revokeRoleRoleWord I ::
          ⟨233⟩ :: sel :: [])
        memTarget (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [memTarget, revokeRoleTargetStorageWord, revokeRoleStorageWordAt, ← htargetSlotEq]
        using rd694₀⟩
  obtain ⟨_, _, rd694⟩ := rd694
  have hmemTarget : memTarget.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ hmemOnlyRole
  have hreadTarget : memTarget.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ hmemOnlyRole hreadOnlyRole
  have rd700 := evm_run rd694 with [
    jumpdest, iszero, push2 ⟨676⟩, jumpiNT (isZero_eq_zero_of_ne htarget) ]
  have rd713pre := evm_run rd700 with [
    push0, dup4, dup2,
    raw mstore 0 (revokeRoleWordAt0Mem (revokeRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (revokeRoleBaseHashMemFrom (revokeRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4]
  have hbaseSlotRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleBaseHashMemFrom (revokeRoleRoleWord I) memTarget)
            |>.readWithPadding 0 64))) =
        revokeRoleBaseSlot (revokeRoleRoleWord I) := by
    unfold revokeRoleBaseSlot
    rw [revokeRoleBaseHashMemFrom_read0_64 _ hmemTarget, revokeRoleBaseHashMem_read0_64]
  have rd723pre := evm_run rd713pre with [
    raw keccak256 0 (revokeRoleBaseSlot (revokeRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hbaseSlotRaw (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and]
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  have haccountClean :
      UInt256.land solcAddrMask (revokeRoleAccountWord I) = revokeRoleAccountWord I :=
    solcAddrMask_clean_left hcanonAccount
  have haccountCleanRight :
      UInt256.land (revokeRoleAccountWord I) solcAddrMask = revokeRoleAccountWord I := by
    rw [SimpleAuction.simpleAuctionU256_land_comm]
    exact haccountClean
  rw [haddrMask, haccountCleanRight] at rd723pre
  have rd731pre := evm_run rd723pre with [
    dup1, dup6,
    raw mstore 0
      (revokeRoleHasRoleAccountMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap3,
    raw mstore 0
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup1, dup4]
  have hslotWrite := revokeRoleTargetKeccakSlotFrom I memTarget hsz68 hmemTarget hcanonAccount
  have rd732 := evm_run rd731pre with [
    raw keccak256 0 (revokeRoleTargetSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslotWrite (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd733₀⟩ := rd732.sload (by decide) (by evm_ov)
  have rd733 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨734⟩
        [revokeRoleTargetStorageWord σ I, revokeRoleTargetSlot I, ⟨64⟩,
          revokeRoleAccountWord I, ⟨0⟩, ⟨0⟩, revokeRoleAccountWord I,
          revokeRoleRoleWord I, ⟨389⟩, revokeRoleAdminStorageWord σ I,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [revokeRoleTargetStorageWord, revokeRoleStorageWordAt] using rd733₀⟩
  obtain ⟨_, _, rd733⟩ := rd733
  have hclearComm :
      UInt256.land (UInt256.lnot ⟨255⟩) (revokeRoleTargetStorageWord σ I) =
        revokeRoleClearLowByteWord (revokeRoleTargetStorageWord σ I) := by
    unfold revokeRoleClearLowByteWord
    exact SimpleAuction.simpleAuctionU256_land_comm (UInt256.lnot ⟨255⟩)
      (revokeRoleTargetStorageWord σ I)
  have rd739pre := evm_run rd733 with [push1 ⟨255⟩, not, and, swap1]
  rw [hclearComm] at rd739pre
  obtain ⟨_, _, rd740₀⟩ := rd739pre.sstore hperm (by decide) (by evm_ov)
  have rd740 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨740⟩
        [⟨64⟩, revokeRoleAccountWord I, ⟨0⟩, ⟨0⟩, revokeRoleAccountWord I,
          revokeRoleRoleWord I, ⟨389⟩, revokeRoleAdminStorageWord σ I,
          revokeRoleAccountWord I, revokeRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, revokeRolePostMap σ I) k C := by
    exact ⟨_, _, by simpa [revokeRolePostMap] using rd740₀⟩
  obtain ⟨_, _, rd740⟩ := rd740
  have hmemEvent :
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
        memTarget).size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ hmemTarget
  have hreadEvent :
      (revokeRoleHasRoleSlotHashMemFrom (revokeRoleRoleWord I) (revokeRoleAccountWord I)
        memTarget).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ hmemTarget hreadTarget
  have rd745pre := evm_run rd740 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (revokeRoleHasRoleSlotHashMemFrom_mload64 (revokeRoleRoleWord I)
        (revokeRoleAccountWord I) hmemTarget hreadTarget)
      (by decide) (by evm_ov),
    caller, swap3, dup7, swap2]
  have rd745 := rd745pre.pushConst revokeRoleRevokedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd780 := evm_run rd745 with [swap2, swap1]
  have rd781 := RD.revokeRoleLog4 0 (UInt256.ofNat 3) rd780 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by simp)
  have rd233 := evm_run rd781 with [
    pop, push1 ⟨1⟩, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlRevokeRoleBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨280⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := revokeRoleSelector_size (by simpa [selIs] using hsel)
  have hd := accessControlDispatch_revokeRole (cd := I.calldata)
    (by simpa [selIs] using hsel)
  let evmE := initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonAccount : (revokeRoleAccountWord I).toNat < EVM.addressModulus
      · have hdec := accessControlDecode_revokeRole_ok (I := I) hsz68 hbig hcanonAccount
        have hadminWord :
            revokeRoleAdminStorageWord σ_evm I = revokeRoleAdminStorageWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner (revokeRoleAdminSlot I) ⟨0⟩
        have hadminHasRoleWord :
            revokeRoleAdminHasRoleStorageWord σ_evm I =
              revokeRoleAdminHasRoleStorageWord σ_solm I := by
          unfold revokeRoleAdminHasRoleStorageWord revokeRoleAdminHasRoleSlotFromWord
          rw [hadminWord]
          simpa [revokeRoleStorageWordAt] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (roleHasRoleSlot
                (.fixedBytes bytes32Width (EVM.Word.toBytesBE (revokeRoleAdminStorageWord σ_solm I)))
                (.address I.source)) ⟨0⟩
        have htargetWord :
            revokeRoleTargetStorageWord σ_evm I = revokeRoleTargetStorageWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner (revokeRoleTargetSlot I) ⟨0⟩
        have rd491 := accessControlRevokeRoleX_decoded (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hcanonAccount hreach
        have rd527 := accessControlRevokeRoleX_adminLoaded (g := Sat256.ofUInt256 g)
          hsz68 rd491
        by_cases hadmin :
            UInt256.land (revokeRoleAdminHasRoleStorageWord σ_evm I) ⟨255⟩ = ⟨0⟩
        · have hadminSolm :
              UInt256.land
                (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                  (revokeRoleAdminHasRoleSlot evmS I)) ⟨255⟩ = ⟨0⟩ := by
            have hword :
                UInt256.land (revokeRoleAdminHasRoleStorageWord σ_solm I) ⟨255⟩ =
                  ⟨0⟩ := by
              simpa [hadminHasRoleWord] using hadmin
            simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
              revokeRoleAdminHasRoleStorageWord, revokeRoleStorageWordAt,
              revokeRoleAdminHasRoleSlotFromWord, revokeRoleAdminHasRoleSlot,
              revokeRoleAdminKey, revokeRoleAdminWord, revokeRoleAdminStorageWord,
              revokeRoleSenderKey] using hword
          have hbody := accessControlRevokeRoleBodyReverts_admin evmS I
            (by simp only [evmS, initState]; exact hwv) hadminSolm
          exact (accessControlRevokeRoleX_onlyRole_revert (g := Sat256.ofUInt256 g)
              hadmin rd527)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hadminNonzero :
              UInt256.land (revokeRoleAdminHasRoleStorageWord σ_evm I) ⟨255⟩ ≠ ⟨0⟩ := hadmin
          have rd517 := accessControlRevokeRoleX_onlyRole_ok (g := Sat256.ofUInt256 g)
            hadminNonzero rd527
          have hadminSolm :
              UInt256.land
                (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                  (revokeRoleAdminHasRoleSlot evmS I)) ⟨255⟩ ≠ ⟨0⟩ := by
            have hword :
                UInt256.land (revokeRoleAdminHasRoleStorageWord σ_solm I) ⟨255⟩ ≠
                  ⟨0⟩ := by
              simpa [hadminHasRoleWord] using hadminNonzero
            simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
              revokeRoleAdminHasRoleStorageWord, revokeRoleStorageWordAt,
              revokeRoleAdminHasRoleSlotFromWord, revokeRoleAdminHasRoleSlot,
              revokeRoleAdminKey, revokeRoleAdminWord, revokeRoleAdminStorageWord,
              revokeRoleSenderKey] using hword
          by_cases htarget :
              UInt256.land (revokeRoleTargetStorageWord σ_evm I) ⟨255⟩ = ⟨0⟩
          · have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (revokeRoleTargetSlot I)) ⟨255⟩ = ⟨0⟩ := by
              have hword :
                  UInt256.land (revokeRoleTargetStorageWord σ_solm I) ⟨255⟩ = ⟨0⟩ := by
                simpa [htargetWord] using htarget
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                revokeRoleTargetStorageWord, revokeRoleStorageWordAt] using hword
            have hbody := accessControlRevokeRoleBodyReturns_noop evmS I
              (by simp only [evmS, initState]; exact hwv) hadminSolm htargetSolm
            exact (accessControlRevokeRoleX_revoke_noop (g := Sat256.ofUInt256 g)
                hsz68 hcanonAccount htarget rd517)
              |>.reEquivExecution hcode hd hdec hbody hAccounts (returnEquiv.void rfl rfl rfl)
          · have htargetNonzero :
                UInt256.land (revokeRoleTargetStorageWord σ_evm I) ⟨255⟩ ≠ ⟨0⟩ := htarget
            have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (revokeRoleTargetSlot I)) ⟨255⟩ ≠ ⟨0⟩ := by
              have hword :
                  UInt256.land (revokeRoleTargetStorageWord σ_solm I) ⟨255⟩ ≠ ⟨0⟩ := by
                simpa [htargetWord] using htargetNonzero
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                revokeRoleTargetStorageWord, revokeRoleStorageWordAt] using hword
            have hbody := accessControlRevokeRoleBodyReturns_write evmS I
              (by simp only [evmS, initState]; exact hwv) hadminSolm htargetSolm
            have hval :
                revokeRoleClearLowByteWord
                    (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                      (revokeRoleTargetSlot I)) =
                  revokeRoleClearLowByteWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                      (revokeRoleTargetSlot I)) := by
              have hword :
                  revokeRoleTargetStorageWord σ_evm I =
                    revokeRoleTargetStorageWord σ_solm I := htargetWord
              simpa [evmE, evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                revokeRoleTargetStorageWord, revokeRoleStorageWordAt] using
                  congrArg revokeRoleClearLowByteWord hword
            have hσPost : EVMStateEquiv (revokeRolePostState evmE I) (revokeRolePostState evmS I) := by
              simpa [revokeRolePostState] using
                accessControlEVMStateEquiv_storageStore_codeOwner hσ (revokeRoleTargetSlot I) hval
            exact (accessControlRevokeRoleX_revoke_write (g := Sat256.ofUInt256 g)
                hperm hsz68 hcanonAccount htargetNonzero rd517)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [revokeRolePostState, evmE, initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by
                  simp [revokeRolePostState, revokeRolePostMap, evmE, initState,
                    storageStore_accountMap,
                    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                    revokeRoleTargetStorageWord, revokeRoleStorageWordAt]))
                hσPost
                (returnEquiv.void rfl rfl rfl)
      · have hdec := accessControlDecode_revokeRole_none_noncanon_account
          (I := I) hsz68 hbig hcanonAccount
        have hnc : UInt256.eq (revokeRoleAccountWord I)
            (UInt256.land (revokeRoleAccountWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonAccount (solcAddrCanonical_of_clean he))
        exact (accessControlRevokeRoleX_noncanon_account (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_revokeRole_none_huge (I := I) hbigge
      exact (accessControlRevokeRoleX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := accessControlDecode_revokeRole_none_short (I := I) hsz4 hshort
    exact (accessControlRevokeRoleX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
