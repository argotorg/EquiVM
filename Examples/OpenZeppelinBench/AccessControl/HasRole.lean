import Examples.OpenZeppelinBench.AccessControl.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `hasRole(bytes32,address)` proof

Phase-1 worker file for the external wrapper at pc 254 and the nested `_roles` mapping read at
pc 451.
-/

abbrev hasRoleRoleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev hasRoleAccountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev hasRoleRoleBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev hasRoleRoleValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (hasRoleRoleBytes I)

abbrev hasRoleAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (hasRoleAccountWord I).toNat)

abbrev hasRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (hasRoleRoleValue I)).insert "account" (hasRoleAccountValue I)

abbrev hasRoleRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (hasRoleRoleBytes I)

abbrev hasRoleAccountKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (hasRoleAccountWord I).toNat)

def hasRoleSlot (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot (hasRoleRoleKey I) (hasRoleAccountKey I)

def hasRoleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (hasRoleSlot I) ⟨0⟩)

abbrev hasRoleMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (hasRoleStorageWord σ I) ⟨255⟩

abbrev hasRoleReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (hasRoleMaskedWord σ I))

theorem hasRoleSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x91, 0xd1, 0x48, 0x54]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x91, 0xd1, 0x48, 0x54]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_hasRole {cd : ByteArray}
    (hsel : ((⟨#[0x91, 0xd1, 0x48, 0x54]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some hasRoleTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x91, 0xd1, 0x48, 0x54]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition])
    (post := [renounceRoleTransition, revokeRoleTransition, supportsInterfaceTransition])
    rfl rfl ?_ (by rw [selectorOf, hasRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide

theorem accessControlDecode_hasRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (hasRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = some (hasRoleStore I) := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = some (hasRoleStore I)
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, hasRoleStore,
    hasRoleRoleValue, hasRoleRoleBytes, hasRoleAccountValue, hasRoleAccountWord]
    using decodeCalldata_bytes32_address_ok (cd := I.calldata) (x := "role")
      (y := "account") hsz68 hbig hcanonAccount

theorem accessControlDecode_hasRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_short (cd := I.calldata) (x := "role")
      (y := "account") hsz4 hshort

theorem accessControlDecode_hasRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_huge (cd := I.calldata) (x := "role")
      (y := "account") hbig

theorem accessControlDecode_hasRole_none_noncanon_account {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncAccount : ¬ (hasRoleAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "account"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, hasRoleAccountWord]
    using decodeCalldata_bytes32_address_none_noncanon (cd := I.calldata) (x := "role")
      (y := "account") hsz68 hbig hncAccount

theorem hasRoleStore_role (I : ExecutionEnv) :
    (hasRoleStore I).get? "role" = some (hasRoleRoleValue I) := by
  rw [hasRoleStore, store_get_ne _ _ (by decide), store_get_self]

theorem hasRoleStore_account (I : ExecutionEnv) :
    (hasRoleStore I).get? "account" = some (hasRoleAccountValue I) := by
  rw [hasRoleStore, store_get_self]

theorem hasRoleStore_role_getElem? (I : ExecutionEnv) :
    (hasRoleStore I)["role"]? = some (hasRoleRoleValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, hasRoleStore_role]

theorem hasRoleStore_account_getElem? (I : ExecutionEnv) :
    (hasRoleStore I)["account"]? = some (hasRoleAccountValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, hasRoleStore_account]

theorem hasRoleStore_roles (I : ExecutionEnv) :
    (hasRoleStore I).get? "_roles" = none := by
  rw [hasRoleStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def hasRoleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (hasRoleRoleKey I), .field "hasRole", .mindex (hasRoleAccountKey I)] }

theorem evalStorageRef_hasRole (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := hasRoleStore I } evm
      (roleHasRoleRef (.var "role") (.var "account")) =
        EvalResult.ok (hasRoleEvaledRef I) := by
  have hgrole := hasRoleStore_role_getElem? I
  have hgaccount := hasRoleStore_account_getElem? I
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
    hasRoleEvaledRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, Std.HashMap.get?_eq_getElem?, hgrole, hgaccount, hasRoleRoleValue,
    hasRoleAccountValue]

theorem evalExpr_hasRole_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := hasRoleStore I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "account"))) =
        .ok (wordToElem .bool
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (hasRoleSlot I)) ⟨255⟩)) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (hbase := by simpa [roleHasRoleRef] using hasRoleStore_roles I)
    (her := evalStorageRef_hasRole evm I)
    (hty := by
      simp [storageTypeAt?, hasRoleEvaledRef, contract, storageDecls, roleDataSt, boolSt,
        storageTypeStep?])
    (hloc := by
      show config.storage.layout (hasRoleEvaledRef I) =
        fun _ => some (boolLoc (hasRoleSlot I))
      simp [config, storageLayout, hasRoleEvaledRef, hasRoleSlot, roleHasRoleSlot,
        roleDataSlot])]
  rw [accessControlStorageLocLoad_bool_offset0 evm (hasRoleSlot I)]

theorem accessControlHasRoleBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (hasRoleStore I) hasRoleTransition.body
      (.returned { contract := contract, locals := hasRoleStore I } evm
        (some (wordToElem .bool
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (hasRoleSlot I)) ⟨255⟩)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [roleHasRoleRef] using evalExpr_hasRole_storage evm I)

theorem hasRoleRoleKeyValueToWord {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (hasRoleRoleKey I) = hasRoleRoleWord I := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (hasRoleRoleBytes I).length = 32 := by
    rw [hasRoleRoleBytes, List.length_take, List.length_drop, htlen]
    omega
  simp [hasRoleRoleKey, keyValueToWord, bytes32Width, hasRoleRoleBytes, hlen]
  unfold hasRoleRoleWord calldataWord
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide), ← byteArray_toList_eq I.calldata]

-- PROMOTE -> Common.lean: generic two-word scratch-memory helpers.
noncomputable def accessControlWordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def accessControlWordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def accessControlTwoWordHashMem (key slot : UInt256) (mem : ByteArray) : ByteArray :=
  accessControlWordAt32Mem slot (accessControlWordAt0Mem key mem)

theorem accessControlWordAt0Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (accessControlWordAt0Mem word mem).size = 96 := by
  unfold accessControlWordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem accessControlWordAt32Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (accessControlWordAt32Mem word mem).size = 96 := by
  unfold accessControlWordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem accessControlTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (accessControlTwoWordHashMem key slot mem).size = 96 := by
  unfold accessControlTwoWordHashMem
  exact accessControlWordAt32Mem_size slot (accessControlWordAt0Mem_size key hmem)

theorem accessControlWordAt0Mem_read0 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (accessControlWordAt0Mem word mem).readWithPadding 0 32 = UInt256.toByteArray word := by
  unfold accessControlWordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray word).size ≤ 32
    rw [toByteArray_size])

theorem accessControlWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (accessControlWordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold accessControlWordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

theorem accessControlTwoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (accessControlTwoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold accessControlTwoWordHashMem accessControlWordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [accessControlWordAt0Mem_size key hmem]; omega) (by omega),
    accessControlWordAt0Mem_read0 key hmem]

theorem accessControlTwoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (accessControlTwoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold accessControlTwoWordHashMem accessControlWordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [accessControlWordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem accessControlTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (accessControlTwoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold accessControlTwoWordHashMem accessControlWordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [accessControlWordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [accessControlWordAt0Mem_size key hmem])]
  exact accessControlWordAt0Mem_read64 key hmem hread64

theorem accessControlTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (accessControlTwoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [accessControlTwoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (accessControlTwoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [accessControlTwoWordHashMem_size key slot hmem]; omega),
      accessControlTwoWordHashMem_read0 key slot hmem]
  have hright :
      (accessControlTwoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [accessControlTwoWordHashMem_size key slot hmem]; omega),
      accessControlTwoWordHashMem_read32 key slot hmem]
  rw [show (accessControlTwoWordHashMem key slot mem).extract 0 64 =
      (accessControlTwoWordHashMem key slot mem).extract 0 32 ++
        (accessControlTwoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

noncomputable def hasRoleBaseHashMem (role : UInt256) : ByteArray :=
  accessControlTwoWordHashMem role ⟨0⟩ solcFreePtrMem

noncomputable def hasRoleBaseSlot (role : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((hasRoleBaseHashMem role).readWithPadding 0 64)))

noncomputable def hasRoleAccountMem (role account : UInt256) : ByteArray :=
  accessControlWordAt0Mem account (hasRoleBaseHashMem role)

noncomputable def hasRoleSlotHashMem (role account : UInt256) : ByteArray :=
  accessControlWordAt32Mem (hasRoleBaseSlot role) (hasRoleAccountMem role account)

noncomputable def hasRoleReturnMem (role account val : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0
    (hasRoleSlotHashMem role account) 128 32

theorem hasRoleBaseHashMem_size (role : UInt256) :
    (hasRoleBaseHashMem role).size = 96 := by
  unfold hasRoleBaseHashMem
  exact accessControlTwoWordHashMem_size role ⟨0⟩ solcFreePtrMem_size

theorem hasRoleSlotHashMem_size (role account : UInt256) :
    (hasRoleSlotHashMem role account).size = 96 := by
  unfold hasRoleSlotHashMem
  apply accessControlWordAt32Mem_size
  unfold hasRoleAccountMem
  exact accessControlWordAt0Mem_size account (hasRoleBaseHashMem_size role)

theorem hasRoleBaseHashMem_read0_64 (role : UInt256) :
    (hasRoleBaseHashMem role).readWithPadding 0 64 =
      UInt256.toByteArray role ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold hasRoleBaseHashMem
  exact accessControlTwoWordHashMem_read0_64 role ⟨0⟩ solcFreePtrMem_size

theorem hasRoleSlotHashMem_read0_64 (role account : UInt256) :
    (hasRoleSlotHashMem role account).readWithPadding 0 64 =
      UInt256.toByteArray account ++ UInt256.toByteArray (hasRoleBaseSlot role) := by
  change (accessControlTwoWordHashMem account (hasRoleBaseSlot role)
      (hasRoleBaseHashMem role)).readWithPadding 0 64 =
    UInt256.toByteArray account ++ UInt256.toByteArray (hasRoleBaseSlot role)
  exact accessControlTwoWordHashMem_read0_64 account (hasRoleBaseSlot role)
    (hasRoleBaseHashMem_size role)

theorem hasRoleSlotHashMem_read64 (role account : UInt256) :
    (hasRoleSlotHashMem role account).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change (accessControlTwoWordHashMem account (hasRoleBaseSlot role)
      (hasRoleBaseHashMem role)).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  apply accessControlTwoWordHashMem_read64
  · exact hasRoleBaseHashMem_size role
  · unfold hasRoleBaseHashMem
    exact accessControlTwoWordHashMem_read64 role ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64

theorem hasRoleSlotHashMem_mload64 (role account : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (hasRoleSlotHashMem role account).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((hasRoleSlotHashMem role account).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [hasRoleSlotHashMem_size]; decide) (by decide)
    (hasRoleSlotHashMem_read64 role account)

theorem hasRoleReturnMem_size (role account val : UInt256) :
    (hasRoleReturnMem role account val).size = 160 := by
  unfold hasRoleReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hasRoleSlotHashMem_size]; omega)
      (by rw [hasRoleSlotHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hasRoleSlotHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem hasRoleReturnMem_read64 (role account val : UInt256) :
    (hasRoleReturnMem role account val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold hasRoleReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hasRoleSlotHashMem_size]; omega)
      (by rw [hasRoleSlotHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hasRoleSlotHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hasRoleSlotHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [hasRoleSlotHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [hasRoleSlotHashMem_size]),
    hasRoleSlotHashMem_read64]

theorem hasRoleReturnMem_mload64 (role account val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (hasRoleReturnMem role account val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((hasRoleReturnMem role account val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [hasRoleReturnMem_size]; decide) (by decide)
    (hasRoleReturnMem_read64 role account val)

theorem hasRoleReturnMem_read128 (role account val : UInt256) :
    (hasRoleReturnMem role account val).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)) := by
  unfold hasRoleReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hasRoleSlotHashMem_size]; omega)
      (by rw [hasRoleSlotHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, hasRoleSlotHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (hasRoleSlotHashMem role account ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (hasRoleSlotHashMem role account).size)))
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) 128 160 (by
        rw [ByteArray.size_append, hasRoleSlotHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, hasRoleSlotHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).size ≤ 32
    rw [toByteArray_size])

theorem hasRoleBaseKeccakSlot (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    hasRoleBaseSlot (hasRoleRoleWord I) =
      roleDataSlot (hasRoleRoleKey I) := by
  unfold hasRoleBaseSlot roleDataSlot mapSlot
  rw [hasRoleBaseHashMem_read0_64, hasRoleRoleKeyValueToWord hsz68]
  exact mappingSlot_single (hasRoleRoleWord I) ⟨0⟩

theorem hasRoleOuterKeccakSlot (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonAccount : (hasRoleAccountWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((hasRoleSlotHashMem (hasRoleRoleWord I) (hasRoleAccountWord I))
          |>.readWithPadding 0 64)))
      = hasRoleSlot I := by
  rw [hasRoleSlotHashMem_read0_64, hasRoleBaseKeccakSlot I hsz68]
  unfold hasRoleSlot roleHasRoleSlot mapSlot
  rw [keyValueToWord_address_of_canonical _ hcanonAccount]
  exact mappingSlot_single (hasRoleAccountWord I)
    (roleDataSlot (hasRoleRoleKey I))

theorem accessControlHasRoleX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨922⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨268⟩, ⟨145⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨145⟩, push2 ⟨268⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨922⟩, jump (by jump_dest) ]⟩

theorem accessControlHasRoleX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (hasRoleAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [hasRoleAccountWord I, hasRoleRoleWord I, ⟨145⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hclean : UInt256.eq (hasRoleAccountWord I)
      (UInt256.land (hasRoleAccountWord I) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanonAccount
  obtain ⟨_, _, rd922⟩ := accessControlHasRoleX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact ⟨_, _, evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup3, calldataload, swap2, pop, push1 ⟨32⟩, dup4, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    dup2, eq, push2 ⟨968⟩,
    jumpiT (by
      change UInt256.eq (hasRoleAccountWord I)
          (UInt256.land (hasRoleAccountWord I)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) ≠ ⟨0⟩
      rw [hmask, hclean]
      decide) (by jump_dest),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨451⟩, jump (by jump_dest) ]⟩

theorem accessControlX_hasRole {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonAccount : (hasRoleAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (hasRoleReturnWord σ I)) := by
  obtain ⟨_, _, rd451⟩ := accessControlHasRoleX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonAccount hreach
  have hslot := hasRoleOuterKeccakSlot I hsz68 hcanonAccount
  have rd465 := evm_run rd451 with [
    jumpdest, push0, swap2, dup3,
    raw mstore 0 (accessControlWordAt0Mem (hasRoleRoleWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, dup2,
    raw mstore 0 (hasRoleBaseHashMem (hasRoleRoleWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup5,
    raw keccak256 0 (hasRoleBaseSlot (hasRoleRoleWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd485 := evm_run rd465 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap4, swap1, swap4, and, dup5,
    raw mstore 0 (hasRoleAccountMem (hasRoleRoleWord I) (hasRoleAccountWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonAccount]
        rfl)
      (by decide) (by evm_ov),
    swap2, swap1,
    raw mstore 0 (hasRoleSlotHashMem (hasRoleRoleWord I) (hasRoleAccountWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (hasRoleSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd486⟩ := rd485.sload (by decide) (by evm_ov)
  have hmaskComm : UInt256.land ⟨255⟩ (hasRoleStorageWord σ I) =
      UInt256.land (hasRoleStorageWord σ I) ⟨255⟩ := by
    exact u256_land_comm ⟨255⟩ (hasRoleStorageWord σ I)
  have rd145 := evm_run rd486 with [
    push1 ⟨255⟩, and, swap1, jump (by jump_dest) ]
  have rd157 := evm_run rd145 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (hasRoleSlotHashMem_mload64 (hasRoleRoleWord I) (hasRoleAccountWord I))
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (hasRoleReturnMem (hasRoleRoleWord I) (hasRoleAccountWord I)
        (hasRoleMaskedWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold hasRoleReturnMem hasRoleMaskedWord
        rw [← hmaskComm]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add ]
  simpa [hasRoleReturnWord, hasRoleMaskedWord, hmaskComm] using
    (evm_run rd157 with [
      jumpdest, push1 ⟨64⟩,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
        mem_cost
        (hasRoleReturnMem_mload64 (hasRoleRoleWord I) (hasRoleAccountWord I)
          (hasRoleMaskedWord σ I))
        (by decide) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret 0 (UInt256.toByteArray (hasRoleReturnWord σ I)) (by decide)
        mem_cost
        (by
          rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
          change (hasRoleReturnMem (hasRoleRoleWord I) (hasRoleAccountWord I)
              (hasRoleMaskedWord σ I)).readWithPadding 128 32 =
            UInt256.toByteArray (hasRoleReturnWord σ I)
          rw [hasRoleReturnWord]
          exact hasRoleReturnMem_read128 (hasRoleRoleWord I) (hasRoleAccountWord I)
            (hasRoleMaskedWord σ I))
        (by evm_ov) ])

theorem accessControlHasRoleX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd922⟩ := accessControlHasRoleX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlHasRoleX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd922⟩ := accessControlHasRoleX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlHasRoleX_noncanon_account {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (hasRoleAccountWord I)
      (UInt256.land (hasRoleAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨254⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd922⟩ := accessControlHasRoleX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup3, calldataload, swap2, pop, push1 ⟨32⟩, dup4, add,
    calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    dup2, eq, push2 ⟨968⟩,
    jumpiNT (by
      change UInt256.eq (hasRoleAccountWord I)
          (UInt256.land (hasRoleAccountWord I)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩
      rw [hmask, hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlHasRoleBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x91, 0xd1, 0x48, 0x54]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨254⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := hasRoleSelector_size hsel
  have hd := accessControlDispatch_hasRole (cd := I.calldata) (by simpa [selIs] using hsel)
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonAccount : (hasRoleAccountWord I).toNat < EVM.addressModulus
      · have hdec := accessControlDecode_hasRole_ok (I := I) hsz68 hbig hcanonAccount
        have hword : hasRoleStorageWord σ_evm I = hasRoleStorageWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (hasRoleSlot I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (hasRoleStore I)
              hasRoleTransition.body
              (.returned { contract := contract, locals := hasRoleStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some (wordToElem .bool (hasRoleMaskedWord σ_solm I)))) := by
          simpa [hasRoleStorageWord, hasRoleMaskedWord, hasRoleSlot, initState,
            Solm.EVM.storageLoad, State.lookupAccount] using
              accessControlHasRoleBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
        have hretVal :
            (some (wordToElem .bool (hasRoleMaskedWord σ_solm I)) : Option Value) =
              some (wordToElem .bool (hasRoleMaskedWord σ_evm I)) := by
          simp [hasRoleMaskedWord, hword.symm]
        exact (accessControlX_hasRole (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hcanonAccount hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody hretVal hAccounts
            (returnEquiv_of_encode (by
              simpa [hasRoleMaskedWord, hasRoleReturnWord] using
                boolWordReturnEncoding (hasRoleStorageWord σ_evm I)))
      · have hdec := accessControlDecode_hasRole_none_noncanon_account
          (I := I) hsz68 hbig hcanonAccount
        have hnc : UInt256.eq (hasRoleAccountWord I)
            (UInt256.land (hasRoleAccountWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonAccount (solcAddrCanonical_of_clean he))
        exact (accessControlHasRoleX_noncanon_account (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_hasRole_none_huge (I := I) hbigge
      exact (accessControlHasRoleX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := accessControlDecode_hasRole_none_short (I := I) hsz4 hshort
    exact (accessControlHasRoleX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
