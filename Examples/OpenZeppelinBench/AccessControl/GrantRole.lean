import Examples.OpenZeppelinBench.AccessControl.Storage
import Examples.OpenZeppelinBench.AccessControl.RevokeRole
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

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
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev grantRoleAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)

abbrev grantRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (grantRoleRoleValue I)).insert "account"
    (grantRoleAccountValue I)

def grantRoleRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

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
  decide +native

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

theorem evalStorageRef_grantRole_admin (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := grantRoleStore I } evm
      (roleAdminRef (.var "role")) = .ok (grantRoleAdminEvaledRef I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleAdminRef,
    evalExpr_grantRole_role, grantRoleAdminEvaledRef, grantRoleRoleValue, grantRoleRoleKey,
    accessControlValueToKey_bytes32_of_length hlen, EvalResult.bind, EvalResult.ofOption, bind,
    pure]

theorem evalExpr_grantRole_admin (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := grantRoleStore I } evm
      (.storage (roleAdminRef (.var "role"))) = .ok (grantRoleAdminValue evm I) := by
  rw [evalExpr_storage_scalar (t := .bytes bytes32Width)
    (loc := bytes32Loc (grantRoleAdminSlot I))
    (hbase := grantRoleStore_roles I)
    (her := evalStorageRef_grantRole_admin evm I hsz68)
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
    grantRoleAdminValue, grantRoleAdminKey, grantRoleSenderKey,
    accessControlValueToKey_bytes32_toBytesBE, accessControlValueToKey_address,
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

theorem evalStorageRef_grantRole_target (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (roleHasRoleRef (.var "role") (.var "account")) =
        .ok (grantRoleTargetEvaledRef I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef,
    evalExpr_grantRole_role_withAdmin, evalExpr_grantRole_account, grantRoleTargetEvaledRef,
    grantRoleRoleValue, grantRoleRoleKey, grantRoleAccountValue, grantRoleAccountKey,
    accessControlValueToKey_bytes32_of_length hlen, accessControlValueToKey_address,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_grantRole_target_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleTargetSlot I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_target evm I hsz68)
    (hty := by
      simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_grantRole_target_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) = .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (grantRoleTargetSlot I))
    (hbase := grantRoleStoreWithAdmin_roles evm I)
    (her := evalStorageRef_grantRole_target evm I hsz68)
    (hty := by
      simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

theorem evalExpr_grantRole_target_not_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.unary .not (.storage (roleHasRoleRef (.var "role") (.var "account")))) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption,
    evalExpr_grantRole_target_false evm I hsz68 hzero]

theorem evalExpr_grantRole_target_not_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := grantRoleStoreWithAdmin evm I } evm
      (.unary .not (.storage (roleHasRoleRef (.var "role") (.var "account")))) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption,
    evalExpr_grantRole_target_true evm I hsz68 hnz]

theorem grantRoleAssignTarget (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
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
      (her := evalStorageRef_grantRole_target evm I hsz68)
      (hty := by
        simp [storageTypeAt?, grantRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
          boolSt, storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, grantRoleTargetEvaledRef, grantRoleTargetSlot])
      (hscalar := by trivial)
      (hstore := by
        simpa [boolLoc, boolOffset0Loc, grantRoleSetTrueWord] using
          storageLocStore_bool_true_offset0 evm (grantRoleTargetSlot I))

theorem accessControlGrantRoleBodyReturns_write (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
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
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I hsz68)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_grantRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (result := .ok
      ({ contract := contract, locals := grantRoleStoreWithAdmin evm I } : Frame)
      (grantRolePostState evm I))
      (evalExpr_grantRole_target_not_true evm I hsz68 htarget) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (grantRoleAssignTarget evm I hsz68)) ?_
    exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlGrantRoleBodyReturns_noop (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
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
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I hsz68)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_grantRole_adminHasRole_true evm I hadmin)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := grantRoleStoreWithAdmin evm I } : Frame) evm)
      (evalExpr_grantRole_target_not_false evm I hsz68 htarget) ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlGrantRoleBodyReverts_admin (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hadmin : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grantRoleAdminHasRoleSlot evm I))
        ⟨255⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (grantRoleStore I) grantRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_grantRole_admin evm I hsz68)) ?_
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
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition])
    (post := [hasRoleTransition, renounceRoleTransition, revokeRoleTransition,
      supportsInterfaceTransition]) rfl rfl ?_
    (by rw [selectorOf, grantRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide

theorem accessControlDecode_grantRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = some (grantRoleStore I) := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = some (grantRoleStore I)
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, grantRoleStore,
    grantRoleRoleValue, grantRoleAccountValue, grantRoleAccountWord]
    using decodeCalldata_bytes32_address_ok (cd := I.calldata) (x := "role")
      (y := "account") hsz68 hbig hcanonAccount

theorem accessControlDecode_grantRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_short (cd := I.calldata) (x := "role")
      (y := "account") hsz4 hshort

theorem accessControlDecode_grantRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_huge (cd := I.calldata) (x := "role")
      (y := "account") hbig

theorem accessControlDecode_grantRole_none_noncanon_account {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncAccount : ¬ (grantRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, grantRoleAccountWord]
    using decodeCalldata_bytes32_address_none_noncanon (cd := I.calldata) (x := "role")
      (y := "account") hsz68 hbig hncAccount

theorem accessControlGrantRoleX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨214⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨922⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨228⟩, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨233⟩, push2 ⟨228⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨922⟩, jump (by jump_dest) ]⟩

theorem accessControlGrantRoleX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨214⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨353⟩
        [grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hclean : UInt256.eq (grantRoleAccountWord I)
      (UInt256.land (grantRoleAccountWord I) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanonAccount
  obtain ⟨_, _, rd922⟩ := accessControlGrantRoleX_toDecoder (cA := cA) (gh := gh)
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
        simpa [grantRoleAccountWord, calldataWord] using hclean
      rw [hc]
      decide) (by jump_dest),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨353⟩, jump (by jump_dest) ]⟩

theorem accessControlGrantRoleX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨214⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd922⟩ := accessControlGrantRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlGrantRoleX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (_hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨214⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd922⟩ := accessControlGrantRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlGrantRoleX_noncanon_account {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (grantRoleAccountWord I)
      (UInt256.land (grantRoleAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨214⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd922⟩ := accessControlGrantRoleX_toDecoder (cA := cA) (gh := gh)
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
      simpa [grantRoleAccountWord, calldataWord] using hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

def grantRoleStorageWordAt (σ : AccountMap) (owner : AccountAddress) (slot : UInt256) : UInt256 :=
  revokeRoleStorageWordAt σ owner slot

def grantRoleAdminStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grantRoleStorageWordAt σ I.codeOwner (grantRoleAdminSlot I)

def grantRoleSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def grantRoleAdminHasRoleSlotFromWord (adminWord : UInt256) (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminWord)) (.address I.source)

def grantRoleAdminHasRoleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grantRoleStorageWordAt σ I.codeOwner
    (grantRoleAdminHasRoleSlotFromWord (grantRoleAdminStorageWord σ I) I)

def grantRoleTargetStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grantRoleStorageWordAt σ I.codeOwner (grantRoleTargetSlot I)

def grantRolePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (grantRoleTargetSlot I)
    (grantRoleSetTrueWord (grantRoleTargetStorageWord σ I))

theorem grantRoleRoleKeyValueToWord {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (grantRoleRoleKey I) = grantRoleRoleWord I := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [grantRoleRoleKey, keyValueToWord, bytes32Width, hlen]
  unfold grantRoleRoleWord calldataWord
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide), ← byteArray_toList_eq I.calldata]

theorem grantRoleSourceWord_toNat (I : ExecutionEnv) :
    (grantRoleSourceWord I).toNat = I.source.val := by
  unfold grantRoleSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem grantRoleSourceWord_canonical (I : ExecutionEnv) :
    (grantRoleSourceWord I).toNat < EVM.addressModulus := by
  rw [grantRoleSourceWord_toNat]
  exact I.source.isLt

theorem grantRoleSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (grantRoleSourceWord I).toNat = I.source := by
  unfold AccountAddress.ofNat
  apply Fin.ext
  rw [grantRoleSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem grantRoleBaseKeccakSlot (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    revokeRoleBaseSlot (grantRoleRoleWord I) =
      roleDataSlot (grantRoleRoleKey I) := by
  unfold revokeRoleBaseSlot roleDataSlot mapSlot
  rw [revokeRoleBaseHashMem_read0_64, grantRoleRoleKeyValueToWord hsz68]
  exact mappingSlot_single (grantRoleRoleWord I) ⟨0⟩

theorem grantRoleAdminSlot_evm (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    grantRoleAdminSlot I = revokeRoleBaseSlot (grantRoleRoleWord I) + ⟨1⟩ := by
  unfold grantRoleAdminSlot roleAdminSlot roleDataSlot mapSlot addSlot
  rw [grantRoleRoleKeyValueToWord hsz68]
  rw [revokeRoleAddSlot_eq]
  unfold revokeRoleBaseSlot
  rw [revokeRoleBaseHashMem_read0_64]
  rw [uInt256OfByteArray_eq]

theorem grantRoleTargetKeccakSlotFrom (I : ExecutionEnv) (mem : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hmem : mem.size = 96)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I)
          (grantRoleAccountWord I) mem).readWithPadding 0 64)))
      = grantRoleTargetSlot I := by
  rw [revokeRoleHasRoleSlotHashMemFrom_read0_64 _ _ hmem, grantRoleBaseKeccakSlot I hsz68]
  unfold grantRoleTargetSlot roleHasRoleSlot mapSlot
  rw [show keyValueToWord (grantRoleAccountKey I) = grantRoleAccountWord I by
    simpa [grantRoleAccountKey] using
      keyValueToWord_address_of_canonical (grantRoleAccountWord I) hcanonAccount]
  exact mappingSlot_single (grantRoleAccountWord I)
    (roleDataSlot (grantRoleRoleKey I))

theorem grantRoleTargetSlot_fixedBytes32 (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus) :
  grantRoleTargetSlot I =
      roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I)))
        (.address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)) := by
  unfold grantRoleTargetSlot roleHasRoleSlot roleDataSlot mapSlot
  rw [grantRoleRoleKeyValueToWord hsz68]
  have hrole :
      keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I))) =
        grantRoleRoleWord I := by
    simpa [bytes32Width] using keyValueToWord_fixedBytes32 (grantRoleRoleWord I)
  rw [hrole]
  rw [show keyValueToWord (grantRoleAccountKey I) = grantRoleAccountWord I by
    simpa [grantRoleAccountKey] using
      keyValueToWord_address_of_canonical (grantRoleAccountWord I) hcanonAccount]
  rw [keyValueToWord_address_of_canonical _ hcanonAccount]

theorem grantRoleAdminHasRoleKeccakSlotFrom (adminRole account : UInt256) (mem : ByteArray)
    (hmem : mem.size = 96) (hcanonAccount : account.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom adminRole account mem)
          |>.readWithPadding 0 64)))
      =
        roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE adminRole))
          (.address (AccountAddress.ofNat account.toNat)) := by
  exact revokeRoleAdminHasRoleKeccakSlotFrom adminRole account mem hmem hcanonAccount

theorem accessControlGrantRoleX_adminLoaded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨353⟩
      [grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
        grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd353⟩ := hreach
  have hslotRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleBaseHashMem (grantRoleRoleWord I)).readWithPadding 0 64))) =
        revokeRoleBaseSlot (grantRoleRoleWord I) := rfl
  have rd370pre := evm_run rd353 with [
    jumpdest, push0, dup3, dup2,
    raw mstore 0 (revokeRoleWordAt0Mem (grantRoleRoleWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revokeRoleBaseSlot (grantRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hslotRaw (by decide) (by evm_ov),
    push1 ⟨1⟩, add]
  obtain ⟨_, _, rd371₀⟩ := rd370pre.sload (by decide) (by evm_ov)
  have rd371 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨371⟩
        [grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
          ⟨233⟩, sel]
        (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [grantRoleAdminStorageWord, grantRoleStorageWordAt, grantRoleAdminSlot_evm I hsz68,
        u256_add_comm] using rd371₀⟩
  obtain ⟨_, _, rd371⟩ := rd371
  exact ⟨_, _, evm_run rd371 with [
    push2 ⟨379⟩, dup2, push2 ⟨527⟩, jump (by jump_dest) ]⟩

theorem accessControlGrantRoleX_onlyRole_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hadmin :
      UInt256.land (grantRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
        grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨379⟩
      [grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
        (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd527⟩ := hreach
  have rd788 := evm_run rd527 with [
    jumpdest, push2 ⟨537⟩, dup2, caller, push2 ⟨788⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd788 with [
    jumpdest, push2 ⟨798⟩, dup3, dup3, push2 ⟨451⟩, jump (by jump_dest) ]
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨798⟩,
          grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨537⟩,
          grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [grantRoleSourceWord] using rd451⟩
  have hslot := grantRoleAdminHasRoleKeccakSlotFrom (grantRoleAdminStorageWord σ I)
    (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I))
    (revokeRoleBaseHashMem_size _) (grantRoleSourceWord_canonical I)
  obtain ⟨_, _, rd798₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := grantRoleAdminStorageWord σ I)
    (account := grantRoleSourceWord I) (ret := ⟨798⟩)
    (mem0 := revokeRoleBaseHashMem (grantRoleRoleWord I))
    (R := [grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨537⟩,
      grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
      grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel])
    (revokeRoleBaseHashMem_size _) (revokeRoleBaseHashMem_read64 _)
    (grantRoleSourceWord_canonical I) (by jump_dest) (by simp) hslot rd451'
  have rd798 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
        (UInt256.land (grantRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ::
          grantRoleSourceWord I :: grantRoleAdminStorageWord σ I :: ⟨537⟩ ::
          grantRoleAdminStorageWord σ I :: ⟨379⟩ :: grantRoleAdminStorageWord σ I ::
          grantRoleAccountWord I :: grantRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        (revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
          (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [grantRoleAdminHasRoleStorageWord, grantRoleStorageWordAt,
        grantRoleAdminHasRoleSlotFromWord, grantRoleSource_ofNat I] using rd798₀⟩
  obtain ⟨_, _, rd798⟩ := rd798
  have rd849 := evm_run rd798 with [
    jumpdest, push2 ⟨849⟩, jumpiT hadmin (by jump_dest) ]
  have rd537 := evm_run rd849 with [
    jumpdest, pop, pop, jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd537 with [
    jumpdest, pop, jump (by jump_dest) ]⟩

theorem accessControlGrantRoleX_onlyRole_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hadmin :
      UInt256.land (grantRoleAdminHasRoleStorageWord σ I) ⟨255⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
        grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
      (revokeRoleBaseHashMem (grantRoleRoleWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd527⟩ := hreach
  have rd788 := evm_run rd527 with [
    jumpdest, push2 ⟨537⟩, dup2, caller, push2 ⟨788⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd788 with [
    jumpdest, push2 ⟨798⟩, dup3, dup3, push2 ⟨451⟩, jump (by jump_dest) ]
  let memAdminBase := revokeRoleBaseHashMem (grantRoleRoleWord I)
  let memAdmin :=
    revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
      (grantRoleSourceWord I) memAdminBase
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨798⟩,
          grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨537⟩,
          grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
        memAdminBase (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memAdminBase, grantRoleSourceWord] using rd451⟩
  have hslot := grantRoleAdminHasRoleKeccakSlotFrom (grantRoleAdminStorageWord σ I)
    (grantRoleSourceWord I) memAdminBase
    (revokeRoleBaseHashMem_size _) (grantRoleSourceWord_canonical I)
  obtain ⟨_, _, rd798₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := grantRoleAdminStorageWord σ I)
    (account := grantRoleSourceWord I) (ret := ⟨798⟩)
    (mem0 := memAdminBase)
    (R := [grantRoleSourceWord I, grantRoleAdminStorageWord σ I, ⟨537⟩,
      grantRoleAdminStorageWord σ I, ⟨379⟩, grantRoleAdminStorageWord σ I,
      grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel])
    (revokeRoleBaseHashMem_size _) (revokeRoleBaseHashMem_read64 _)
    (grantRoleSourceWord_canonical I) (by jump_dest) (by simp) hslot rd451'
  have rd798 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
        (UInt256.land (grantRoleAdminHasRoleStorageWord σ I) ⟨255⟩ ::
          grantRoleSourceWord I :: grantRoleAdminStorageWord σ I :: ⟨537⟩ ::
          grantRoleAdminStorageWord σ I :: ⟨379⟩ :: grantRoleAdminStorageWord σ I ::
          grantRoleAccountWord I :: grantRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        memAdmin (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [memAdmin, memAdminBase, grantRoleAdminHasRoleStorageWord,
        grantRoleStorageWordAt, grantRoleAdminHasRoleSlotFromWord,
        grantRoleSource_ofNat I] using rd798₀⟩
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
      UInt256.land (grantRoleSourceWord I) solcAddrMask =
        UInt256.land solcAddrMask (grantRoleSourceWord I) := by
    exact u256_land_comm (grantRoleSourceWord I) solcAddrMask
  have rd830 := evm_run rd830pre with [
    raw mstore 3 (revokeRoleUnauthorizedAccountMemFrom (grantRoleSourceWord I) memAdmin)
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide, hsourceMaskComm]
        rfl)
      (by decide) (by evm_ov) ]
  have rd837 := evm_run rd830 with [
    push1 ⟨36⟩, dup2, add, dup4, swap1,
    raw mstore 3
      (revokeRoleUnauthorizedMemFrom (grantRoleSourceWord I)
        (grantRoleAdminStorageWord σ I) memAdmin)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd848 := evm_run rd837 with [
    push1 ⟨68⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide) mem_cost
      (revokeRoleUnauthorizedMemFrom_mload64 (grantRoleSourceWord I)
        (grantRoleAdminStorageWord σ I) hmemAdmin hreadAdmin)
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
      decide +native)
    (by simp)

def grantRoleGrantedTopic : UInt256 :=
  ⟨21498167346302451094516930465084812798900530214793017313261708129848854408973⟩

theorem accessControlGrantRoleX_grant_noop {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus)
    (htarget : UInt256.land (grantRoleTargetStorageWord σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨379⟩
      [grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
        (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) ByteArray.empty := by
  obtain ⟨_, _, rd379⟩ := hreach
  have rd540 := evm_run rd379 with [
    jumpdest, push2 ⟨389⟩, dup4, dup4, push2 ⟨540⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd540 with [
    jumpdest, push0, push2 ⟨551⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  let memOnlyRole :=
    revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
      (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I))
  have hmemOnlyRole : memOnlyRole.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _
      (revokeRoleBaseHashMem_size (grantRoleRoleWord I))
  have hreadOnlyRole :
      memOnlyRole.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _
      (revokeRoleBaseHashMem_size (grantRoleRoleWord I))
      (revokeRoleBaseHashMem_read64 (grantRoleRoleWord I))
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [grantRoleAccountWord I, grantRoleRoleWord I, ⟨551⟩, ⟨0⟩,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩,
          grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
          ⟨233⟩, sel]
        memOnlyRole (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memOnlyRole] using rd451⟩
  have hslot := grantRoleTargetKeccakSlotFrom I memOnlyRole hsz68 hmemOnlyRole hcanonAccount
  have htargetSlotEq := grantRoleTargetSlot_fixedBytes32 I hsz68 hcanonAccount
  have hslot' :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I)
            (grantRoleAccountWord I) memOnlyRole).readWithPadding 0 64))) =
        roleHasRoleSlot
          (.fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I)))
          (.address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)) := by
    rw [hslot, htargetSlotEq]
  obtain ⟨_, _, rd551₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := grantRoleRoleWord I) (account := grantRoleAccountWord I)
    (ret := ⟨551⟩) (mem0 := memOnlyRole)
    (R := [⟨0⟩, grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩,
      grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
      ⟨233⟩, sel])
    hmemOnlyRole hreadOnlyRole hcanonAccount (by jump_dest) (by simp) hslot' rd451'
  have rd551 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨551⟩
        (UInt256.land (grantRoleTargetStorageWord σ I) ⟨255⟩ :: ⟨0⟩ ::
          grantRoleAccountWord I :: grantRoleRoleWord I :: ⟨389⟩ ::
          grantRoleAdminStorageWord σ I :: grantRoleAccountWord I :: grantRoleRoleWord I ::
          ⟨233⟩ :: sel :: [])
        (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
          memOnlyRole)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [grantRoleTargetStorageWord, grantRoleStorageWordAt, ← htargetSlotEq]
        using rd551₀⟩
  obtain ⟨_, _, rd551⟩ := rd551
  have rd233 := evm_run rd551 with [
    jumpdest, push2 ⟨676⟩, jumpiT htarget (by jump_dest),
    jumpdest, pop, push0, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlGrantRoleX_grant_write {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus)
    (htarget : UInt256.land (grantRoleTargetStorageWord σ I) ⟨255⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨379⟩
      [grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
        ⟨233⟩, sel]
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
        (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, grantRolePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd379⟩ := hreach
  have rd540 := evm_run rd379 with [
    jumpdest, push2 ⟨389⟩, dup4, dup4, push2 ⟨540⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd540 with [
    jumpdest, push0, push2 ⟨551⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  let memOnlyRole :=
    revokeRoleHasRoleSlotHashMemFrom (grantRoleAdminStorageWord σ I)
      (grantRoleSourceWord I) (revokeRoleBaseHashMem (grantRoleRoleWord I))
  have hmemOnlyRole : memOnlyRole.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _
      (revokeRoleBaseHashMem_size (grantRoleRoleWord I))
  have hreadOnlyRole :
      memOnlyRole.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _
      (revokeRoleBaseHashMem_size (grantRoleRoleWord I))
      (revokeRoleBaseHashMem_read64 (grantRoleRoleWord I))
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [grantRoleAccountWord I, grantRoleRoleWord I, ⟨551⟩, ⟨0⟩,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩,
          grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
          ⟨233⟩, sel]
        memOnlyRole (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [memOnlyRole] using rd451⟩
  have htargetSlotEq := grantRoleTargetSlot_fixedBytes32 I hsz68 hcanonAccount
  have hslotBase := grantRoleTargetKeccakSlotFrom I memOnlyRole hsz68 hmemOnlyRole hcanonAccount
  have hslot' :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I)
            (grantRoleAccountWord I) memOnlyRole).readWithPadding 0 64))) =
        roleHasRoleSlot
          (.fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleRoleWord I)))
          (.address (AccountAddress.ofNat (grantRoleAccountWord I).toNat)) := by
    rw [hslotBase, htargetSlotEq]
  obtain ⟨_, _, rd551₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := grantRoleRoleWord I) (account := grantRoleAccountWord I)
    (ret := ⟨551⟩) (mem0 := memOnlyRole)
    (R := [⟨0⟩, grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩,
      grantRoleAdminStorageWord σ I, grantRoleAccountWord I, grantRoleRoleWord I,
      ⟨233⟩, sel])
    hmemOnlyRole hreadOnlyRole hcanonAccount (by jump_dest) (by simp) hslot' rd451'
  let memTarget :=
    revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
      memOnlyRole
  have rd551 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨551⟩
        (UInt256.land (grantRoleTargetStorageWord σ I) ⟨255⟩ :: ⟨0⟩ ::
          grantRoleAccountWord I :: grantRoleRoleWord I :: ⟨389⟩ ::
          grantRoleAdminStorageWord σ I :: grantRoleAccountWord I :: grantRoleRoleWord I ::
          ⟨233⟩ :: sel :: [])
        memTarget (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [memTarget, grantRoleTargetStorageWord, grantRoleStorageWordAt, ← htargetSlotEq]
        using rd551₀⟩
  obtain ⟨_, _, rd551⟩ := rd551
  have hmemTarget : memTarget.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ hmemOnlyRole
  have hreadTarget : memTarget.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ hmemOnlyRole hreadOnlyRole
  have rd556 := evm_run rd551 with [
    jumpdest, push2 ⟨676⟩, jumpiNT (by rw [htarget]) ]
  have rd569pre := evm_run rd556 with [
    push0, dup4, dup2,
    raw mstore 0 (revokeRoleWordAt0Mem (grantRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (revokeRoleBaseHashMemFrom (grantRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4]
  have hbaseSlotRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleBaseHashMemFrom (grantRoleRoleWord I) memTarget)
            |>.readWithPadding 0 64))) =
        revokeRoleBaseSlot (grantRoleRoleWord I) := by
    unfold revokeRoleBaseSlot
    rw [revokeRoleBaseHashMemFrom_read0_64 _ hmemTarget, revokeRoleBaseHashMem_read0_64]
  have rd579pre := evm_run rd569pre with [
    raw keccak256 0 (revokeRoleBaseSlot (grantRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hbaseSlotRaw (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and]
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  have haccountClean :
      UInt256.land solcAddrMask (grantRoleAccountWord I) = grantRoleAccountWord I :=
    solcAddrMask_clean_left hcanonAccount
  have haccountCleanRight :
      UInt256.land (grantRoleAccountWord I) solcAddrMask = grantRoleAccountWord I := by
    rw [u256_land_comm]
    exact haccountClean
  rw [haddrMask, haccountCleanRight] at rd579pre
  have rd585pre := evm_run rd579pre with [
    dup5,
    raw mstore 0
      (revokeRoleHasRoleAccountMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1]
  have hslotWrite := grantRoleTargetKeccakSlotFrom I memTarget hsz68 hmemTarget hcanonAccount
  have rd588 := evm_run rd585pre with [
    raw keccak256 0 (grantRoleTargetSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslotWrite (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd589₀⟩ := rd588.sload (by decide) (by evm_ov)
  have rd589 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨589⟩
        [grantRoleTargetStorageWord σ I, grantRoleTargetSlot I, ⟨0⟩,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩, grantRoleAdminStorageWord σ I,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [grantRoleTargetStorageWord, grantRoleStorageWordAt] using rd589₀⟩
  obtain ⟨_, _, rd589⟩ := rd589
  have hsetLandComm :
      UInt256.land (UInt256.lnot ⟨255⟩) (grantRoleTargetStorageWord σ I) =
        UInt256.land (grantRoleTargetStorageWord σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩)
      (grantRoleTargetStorageWord σ I)
  have rd597pre := evm_run rd589 with [
    push1 ⟨255⟩, not, and, push1 ⟨1⟩, or, swap1]
  have hsetWord :
      UInt256.lor ⟨1⟩
          (UInt256.land (UInt256.lnot ⟨255⟩) (grantRoleTargetStorageWord σ I)) =
        grantRoleSetTrueWord (grantRoleTargetStorageWord σ I) := by
    rw [hsetLandComm, u256_lor_comm]
    rfl
  rw [hsetWord] at rd597pre
  obtain ⟨_, _, rd598₀⟩ := rd597pre.sstore hperm (by decide) (by evm_ov)
  have rd598 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨598⟩
        [⟨0⟩, grantRoleAccountWord I, grantRoleRoleWord I, ⟨389⟩,
          grantRoleAdminStorageWord σ I,
          grantRoleAccountWord I, grantRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, grantRolePostMap σ I) k C := by
    exact ⟨_, _, by simpa [grantRolePostMap] using rd598₀⟩
  obtain ⟨_, _, rd598⟩ := rd598
  have hmemEvent :
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
        memTarget).size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ hmemTarget
  have hreadEvent :
      (revokeRoleHasRoleSlotHashMemFrom (grantRoleRoleWord I) (grantRoleAccountWord I)
        memTarget).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ hmemTarget hreadTarget
  have rd604 := evm_run rd598 with [
    push2 ⟨604⟩, caller, swap1, jump (by jump_dest) ]
  have rd625pre := evm_run rd604 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup3,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup5]
  have rd658 := rd625pre.pushConst grantRoleGrantedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd668 := evm_run rd658 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (revokeRoleHasRoleSlotHashMemFrom_mload64 (grantRoleRoleWord I)
        (grantRoleAccountWord I) hmemTarget hreadTarget)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (revokeRoleHasRoleSlotHashMemFrom_mload64 (grantRoleRoleWord I)
        (grantRoleAccountWord I) hmemTarget hreadTarget)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen0 : ((⟨128⟩ : UInt256).sub ⟨128⟩) = ⟨0⟩ := by
    decide
  have rd668' := rd668
  rw [hlen0] at rd668'
  have rd669 := RD.log4 0 (UInt256.ofNat 3) rd668' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      decide +native)
    (by decide) (by simp)
  have rd233 := evm_run rd669 with [
    pop, push1 ⟨1⟩, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlGrantRoleBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨214⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := grantRoleSelector_size (by simpa [selIs] using hsel)
  have hd := accessControlDispatch_grantRole (cd := I.calldata)
    (by simpa [selIs] using hsel)
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonAccount : (grantRoleAccountWord I).toNat < EVM.addressModulus
      · have hdec := accessControlDecode_grantRole_ok (I := I) hsz68 hbig hcanonAccount
        have hadminWord :
            grantRoleAdminStorageWord σ_evm I = grantRoleAdminStorageWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner (grantRoleAdminSlot I) ⟨0⟩
        have hadminHasRoleWord :
            grantRoleAdminHasRoleStorageWord σ_evm I =
              grantRoleAdminHasRoleStorageWord σ_solm I := by
          unfold grantRoleAdminHasRoleStorageWord grantRoleAdminHasRoleSlotFromWord
          rw [hadminWord]
          simpa [grantRoleStorageWordAt, revokeRoleStorageWordAt] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (roleHasRoleSlot
                (.fixedBytes bytes32Width (EVM.Word.toBytesBE (grantRoleAdminStorageWord σ_solm I)))
                (.address I.source)) ⟨0⟩
        have htargetWord :
            grantRoleTargetStorageWord σ_evm I = grantRoleTargetStorageWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner (grantRoleTargetSlot I) ⟨0⟩
        have rd353 := accessControlGrantRoleX_decoded (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hcanonAccount hreach
        have rd527 := accessControlGrantRoleX_adminLoaded (g := Sat256.ofUInt256 g)
          hsz68 rd353
        by_cases hadmin :
            UInt256.land (grantRoleAdminHasRoleStorageWord σ_evm I) ⟨255⟩ = ⟨0⟩
        · have hadminSolm :
              UInt256.land
                (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                  (grantRoleAdminHasRoleSlot evmS I)) ⟨255⟩ = ⟨0⟩ := by
            have hword :
                UInt256.land (grantRoleAdminHasRoleStorageWord σ_solm I) ⟨255⟩ =
                  ⟨0⟩ := by
              simpa [hadminHasRoleWord] using hadmin
            simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
              grantRoleAdminHasRoleStorageWord, grantRoleStorageWordAt,
              revokeRoleStorageWordAt, grantRoleAdminHasRoleSlotFromWord,
              grantRoleAdminHasRoleSlot, grantRoleAdminKey, grantRoleAdminWord,
              grantRoleAdminStorageWord, grantRoleSenderKey] using hword
          have hbody := accessControlGrantRoleBodyReverts_admin evmS I hsz68
            (by simp only [evmS, initState]; exact hwv) hadminSolm
          exact (accessControlGrantRoleX_onlyRole_revert (g := Sat256.ofUInt256 g)
              hadmin rd527)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hadminNonzero :
              UInt256.land (grantRoleAdminHasRoleStorageWord σ_evm I) ⟨255⟩ ≠ ⟨0⟩ := hadmin
          have rd379 := accessControlGrantRoleX_onlyRole_ok (g := Sat256.ofUInt256 g)
            hadminNonzero rd527
          have hadminSolm :
              UInt256.land
                (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                  (grantRoleAdminHasRoleSlot evmS I)) ⟨255⟩ ≠ ⟨0⟩ := by
            have hword :
                UInt256.land (grantRoleAdminHasRoleStorageWord σ_solm I) ⟨255⟩ ≠
                  ⟨0⟩ := by
              simpa [hadminHasRoleWord] using hadminNonzero
            simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
              grantRoleAdminHasRoleStorageWord, grantRoleStorageWordAt,
              revokeRoleStorageWordAt, grantRoleAdminHasRoleSlotFromWord,
              grantRoleAdminHasRoleSlot, grantRoleAdminKey, grantRoleAdminWord,
              grantRoleAdminStorageWord, grantRoleSenderKey] using hword
          by_cases htarget :
              UInt256.land (grantRoleTargetStorageWord σ_evm I) ⟨255⟩ = ⟨0⟩
          · have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (grantRoleTargetSlot I)) ⟨255⟩ = ⟨0⟩ := by
              have hword :
                  UInt256.land (grantRoleTargetStorageWord σ_solm I) ⟨255⟩ = ⟨0⟩ := by
                simpa [htargetWord] using htarget
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                grantRoleTargetStorageWord, grantRoleStorageWordAt, revokeRoleStorageWordAt] using
                  hword
            have hbody := accessControlGrantRoleBodyReturns_write evmS I hsz68
              (by simp only [evmS, initState]; exact hwv) hadminSolm htargetSolm
            have hval :
                grantRoleSetTrueWord
                    (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                      (grantRoleTargetSlot I)) =
                  grantRoleSetTrueWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                      (grantRoleTargetSlot I)) := by
              have hword :
                  grantRoleTargetStorageWord σ_evm I =
                    grantRoleTargetStorageWord σ_solm I := htargetWord
              simpa [evmE, evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                grantRoleTargetStorageWord, grantRoleStorageWordAt, revokeRoleStorageWordAt] using
                  congrArg grantRoleSetTrueWord hword
            have hσPost : EVMStateEquiv (grantRolePostState evmE I) (grantRolePostState evmS I) := by
              simpa [grantRolePostState] using
                accessControlEVMStateEquiv_storageStore_codeOwner hσ (grantRoleTargetSlot I) hval
            exact (accessControlGrantRoleX_grant_write (g := Sat256.ofUInt256 g)
                hperm hsz68 hcanonAccount htarget rd379)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [grantRolePostState, evmE, initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by
                  simp [grantRolePostState, grantRolePostMap, evmE, initState,
                    storageStore_accountMap,
                    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                    grantRoleTargetStorageWord, grantRoleStorageWordAt,
                    revokeRoleStorageWordAt]))
                hσPost
                (returnEquiv.fallthrough rfl rfl (by decide +native))
          · have htargetNonzero :
                UInt256.land (grantRoleTargetStorageWord σ_evm I) ⟨255⟩ ≠ ⟨0⟩ := htarget
            have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (grantRoleTargetSlot I)) ⟨255⟩ ≠ ⟨0⟩ := by
              have hword :
                  UInt256.land (grantRoleTargetStorageWord σ_solm I) ⟨255⟩ ≠ ⟨0⟩ := by
                simpa [htargetWord] using htargetNonzero
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                grantRoleTargetStorageWord, grantRoleStorageWordAt, revokeRoleStorageWordAt] using
                  hword
            have hbody := accessControlGrantRoleBodyReturns_noop evmS I hsz68
              (by simp only [evmS, initState]; exact hwv) hadminSolm htargetSolm
            exact (accessControlGrantRoleX_grant_noop (g := Sat256.ofUInt256 g)
                hsz68 hcanonAccount htargetNonzero rd379)
              |>.reEquivExecution hcode hd hdec hbody hAccounts (returnEquiv.fallthrough rfl rfl (by decide +native))
      · have hdec := accessControlDecode_grantRole_none_noncanon_account
          (I := I) hsz68 hbig hcanonAccount
        have hnc : UInt256.eq (grantRoleAccountWord I)
            (UInt256.land (grantRoleAccountWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonAccount (solcAddrCanonical_of_clean he))
        exact (accessControlGrantRoleX_noncanon_account (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_grantRole_none_huge (I := I) hbigge
      exact (accessControlGrantRoleX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := accessControlDecode_grantRole_none_short (I := I) hsz4 hshort
    exact (accessControlGrantRoleX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
