import Examples.OpenZeppelinBench.AccessControl.RevokeRole
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `renounceRole(bytes32,address)` proof

Phase-1 worker file for the external wrapper at pc 235 and the shared guarded revoke routine.
-/

abbrev renounceRoleRoleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev renounceRoleCallerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev renounceRoleRoleValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev renounceRoleCallerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (renounceRoleCallerWord I).toNat)

abbrev renounceRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (renounceRoleRoleValue I)).insert "callerConfirmation"
    (renounceRoleCallerValue I)

def renounceRoleCallerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (renounceRoleCallerWord I).toNat)

def renounceRoleTargetSlot (I : ExecutionEnv) : UInt256 :=
  roleHasRoleSlot
    (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32))
    (renounceRoleCallerKey I)

def renounceRoleClearLowByteWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def renounceRolePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)
    (renounceRoleClearLowByteWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)))

def renounceRoleSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def renounceRoleTargetEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles",
    steps := [.mindex (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)),
      .field "hasRole", .mindex (renounceRoleCallerKey I)] }

def renounceRoleStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (renounceRoleTargetSlot I) ⟨0⟩)

abbrev renounceRoleMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (renounceRoleStorageWord σ I) ⟨255⟩

def renounceRolePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (renounceRoleTargetSlot I)
    (renounceRoleClearLowByteWord (renounceRoleStorageWord σ I))

theorem renounceRoleSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_renounceRole {cd : ByteArray}
    (hsel : ((⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ : ByteArray) == cd.extract 0 4) =
      true) :
    dispatchMsg contract cd = some renounceRoleTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition,
      hasRoleTransition])
    (post := [revokeRoleTransition, supportsInterfaceTransition]) rfl rfl ?_
    (by rw [selectorOf, renounceRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, hasRoleSelectorBytes, hcd]; decide

theorem accessControlDecode_renounceRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata =
        some (renounceRoleStore I) := by
  show decodeCalldata ["role", "callerConfirmation"] [bytes32, addr] I.calldata =
    some (renounceRoleStore I)
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, renounceRoleStore,
    renounceRoleRoleValue, renounceRoleCallerValue, renounceRoleCallerWord]
    using decodeCalldata_bytes32_address_ok (cd := I.calldata) (x := "role")
      (y := "callerConfirmation") hsz68 hbig hcanon

theorem accessControlDecode_renounceRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "callerConfirmation"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_short (cd := I.calldata) (x := "role")
      (y := "callerConfirmation") hsz4 hshort

theorem accessControlDecode_renounceRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "callerConfirmation"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_address_none_huge (cd := I.calldata) (x := "role")
      (y := "callerConfirmation") hbig

theorem accessControlDecode_renounceRole_none_noncanon_caller {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncCaller : ¬ (renounceRoleCallerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role", "callerConfirmation"] [bytes32, addr] I.calldata = none
  simpa [bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, renounceRoleCallerWord]
    using decodeCalldata_bytes32_address_none_noncanon (cd := I.calldata) (x := "role")
      (y := "callerConfirmation") hsz68 hbig hncCaller

theorem renounceRoleSourceWord_toNat (I : ExecutionEnv) :
    (renounceRoleSourceWord I).toNat = I.source.val := by
  unfold renounceRoleSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem renounceRoleSourceWord_canonical (I : ExecutionEnv) :
    (renounceRoleSourceWord I).toNat < EVM.addressModulus := by
  rw [renounceRoleSourceWord_toNat]
  exact I.source.isLt

theorem renounceRoleSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (renounceRoleSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [renounceRoleSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem renounceRoleCallerWord_eq_sourceWord_of_address {I : ExecutionEnv}
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (haddr : AccountAddress.ofNat (renounceRoleCallerWord I).toNat = I.source) :
    renounceRoleCallerWord I = renounceRoleSourceWord I := by
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  rw [renounceRoleSourceWord_toNat]
  exact hval

theorem renounceRoleCallerAddress_eq_source_of_word {I : ExecutionEnv}
    (hword : renounceRoleCallerWord I = renounceRoleSourceWord I) :
    AccountAddress.ofNat (renounceRoleCallerWord I).toNat = I.source := by
  rw [hword, renounceRoleSource_ofNat]

-- PROMOTE -> Common.lean: generic two-word scratch-memory helpers.
noncomputable def renounceRoleWordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def renounceRoleWordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def renounceRoleTwoWordHashMem (key slot : UInt256) (mem : ByteArray) :
    ByteArray :=
  renounceRoleWordAt32Mem slot (renounceRoleWordAt0Mem key mem)

theorem renounceRoleWordAt0Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleWordAt0Mem word mem).size = 96 := by
  unfold renounceRoleWordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem renounceRoleWordAt32Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleWordAt32Mem word mem).size = 96 := by
  unfold renounceRoleWordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem renounceRoleTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleTwoWordHashMem key slot mem).size = 96 := by
  unfold renounceRoleTwoWordHashMem
  exact renounceRoleWordAt32Mem_size slot (renounceRoleWordAt0Mem_size key hmem)

theorem renounceRoleWordAt0Mem_read0 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleWordAt0Mem word mem).readWithPadding 0 32 = UInt256.toByteArray word := by
  unfold renounceRoleWordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray word).size ≤ 32
    rw [toByteArray_size])

theorem renounceRoleWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (renounceRoleWordAt0Mem word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold renounceRoleWordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega) (by rw [hmem])]
  exact hread64

theorem renounceRoleTwoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleTwoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold renounceRoleTwoWordHashMem renounceRoleWordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [renounceRoleWordAt0Mem_size key hmem]; omega) (by omega),
    renounceRoleWordAt0Mem_read0 key hmem]

theorem renounceRoleTwoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleTwoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold renounceRoleTwoWordHashMem renounceRoleWordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [renounceRoleWordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem renounceRoleTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (renounceRoleTwoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold renounceRoleTwoWordHashMem renounceRoleWordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [renounceRoleWordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [renounceRoleWordAt0Mem_size key hmem])]
  exact renounceRoleWordAt0Mem_read64 key hmem hread64

theorem renounceRoleTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (renounceRoleTwoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [renounceRoleTwoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (renounceRoleTwoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [renounceRoleTwoWordHashMem_size key slot hmem]; omega),
      renounceRoleTwoWordHashMem_read0 key slot hmem]
  have hright :
      (renounceRoleTwoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [renounceRoleTwoWordHashMem_size key slot hmem]; omega),
      renounceRoleTwoWordHashMem_read32 key slot hmem]
  rw [show (renounceRoleTwoWordHashMem key slot mem).extract 0 64 =
      (renounceRoleTwoWordHashMem key slot mem).extract 0 32 ++
        (renounceRoleTwoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

noncomputable def renounceRoleBaseHashMem (role : UInt256) : ByteArray :=
  renounceRoleTwoWordHashMem role ⟨0⟩ solcFreePtrMem

noncomputable def renounceRoleBaseSlotFromWord (role : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((renounceRoleBaseHashMem role).readWithPadding 0 64)))

noncomputable def renounceRoleAccountMem (role account : UInt256) : ByteArray :=
  renounceRoleWordAt0Mem account (renounceRoleBaseHashMem role)

noncomputable def renounceRoleSlotHashMem (role account : UInt256) : ByteArray :=
  renounceRoleWordAt32Mem (renounceRoleBaseSlotFromWord role)
    (renounceRoleAccountMem role account)

theorem renounceRoleBaseHashMem_size (role : UInt256) :
    (renounceRoleBaseHashMem role).size = 96 := by
  unfold renounceRoleBaseHashMem
  exact renounceRoleTwoWordHashMem_size role ⟨0⟩ solcFreePtrMem_size

theorem renounceRoleSlotHashMem_size (role account : UInt256) :
    (renounceRoleSlotHashMem role account).size = 96 := by
  unfold renounceRoleSlotHashMem
  apply renounceRoleWordAt32Mem_size
  unfold renounceRoleAccountMem
  exact renounceRoleWordAt0Mem_size account (renounceRoleBaseHashMem_size role)

theorem renounceRoleBaseHashMem_read0_64 (role : UInt256) :
    (renounceRoleBaseHashMem role).readWithPadding 0 64 =
      UInt256.toByteArray role ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold renounceRoleBaseHashMem
  exact renounceRoleTwoWordHashMem_read0_64 role ⟨0⟩ solcFreePtrMem_size

theorem renounceRoleSlotHashMem_read0_64 (role account : UInt256) :
    (renounceRoleSlotHashMem role account).readWithPadding 0 64 =
      UInt256.toByteArray account ++ UInt256.toByteArray (renounceRoleBaseSlotFromWord role) := by
  change (renounceRoleTwoWordHashMem account (renounceRoleBaseSlotFromWord role)
      (renounceRoleBaseHashMem role)).readWithPadding 0 64 =
    UInt256.toByteArray account ++ UInt256.toByteArray (renounceRoleBaseSlotFromWord role)
  exact renounceRoleTwoWordHashMem_read0_64 account (renounceRoleBaseSlotFromWord role)
    (renounceRoleBaseHashMem_size role)

theorem renounceRoleSlotHashMem_read64 (role account : UInt256) :
    (renounceRoleSlotHashMem role account).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change (renounceRoleTwoWordHashMem account (renounceRoleBaseSlotFromWord role)
      (renounceRoleBaseHashMem role)).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  apply renounceRoleTwoWordHashMem_read64
  · exact renounceRoleBaseHashMem_size role
  · unfold renounceRoleBaseHashMem
    exact renounceRoleTwoWordHashMem_read64 role ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64

theorem renounceRoleSlotHashMem_mload64 (role account : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (renounceRoleSlotHashMem role account).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((renounceRoleSlotHashMem role account).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [renounceRoleSlotHashMem_size]; decide) (by decide)
    (renounceRoleSlotHashMem_read64 role account)

theorem renounceRoleRoleKeyValueToWord {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    keyValueToWord (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)) =
      renounceRoleRoleWord I := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [keyValueToWord, bytes32Width, hlen]
  unfold renounceRoleRoleWord calldataWord
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide)]
  rw [byteArray_toList_eq]

theorem renounceRoleBaseKeccakSlot (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    renounceRoleBaseSlotFromWord (renounceRoleRoleWord I) =
      roleDataSlot (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)) := by
  unfold renounceRoleBaseSlotFromWord roleDataSlot mapSlot
  rw [renounceRoleBaseHashMem_read0_64, renounceRoleRoleKeyValueToWord hsz68]
  exact mappingSlot_single (renounceRoleRoleWord I) ⟨0⟩

theorem renounceRoleOuterKeccakSlot (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((renounceRoleSlotHashMem (renounceRoleRoleWord I) (renounceRoleCallerWord I))
          |>.readWithPadding 0 64))) =
      renounceRoleTargetSlot I := by
  rw [renounceRoleSlotHashMem_read0_64, renounceRoleBaseKeccakSlot I hsz68]
  unfold renounceRoleTargetSlot roleHasRoleSlot mapSlot renounceRoleCallerKey
  rw [keyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single (renounceRoleCallerWord I)
    (roleDataSlot (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)))

theorem renounceRoleTargetSlot_fixedBytes32 (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus) :
  renounceRoleTargetSlot I =
      roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE (renounceRoleRoleWord I)))
        (.address (AccountAddress.ofNat (renounceRoleCallerWord I).toNat)) := by
  unfold renounceRoleTargetSlot roleHasRoleSlot roleDataSlot mapSlot renounceRoleCallerKey
  rw [renounceRoleRoleKeyValueToWord hsz68]
  have hrole :
      keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE (renounceRoleRoleWord I))) =
        renounceRoleRoleWord I := by
    simpa [bytes32Width] using keyValueToWord_fixedBytes32 (renounceRoleRoleWord I)
  rw [hrole]

theorem renounceRolePostState_accountMap (evm : EVM.State) (I : ExecutionEnv) :
    (renounceRolePostState evm I).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (renounceRoleTargetSlot I)
        (renounceRoleClearLowByteWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I))) := by
  simp [renounceRolePostState, storageStore_accountMap]

theorem renounceRolePostState_createdAccounts (evm : EVM.State) (I : ExecutionEnv) :
    (renounceRolePostState evm I).createdAccounts = evm.createdAccounts := by
  simp [renounceRolePostState, storageStore_createdAccounts]

theorem renounceRolePostState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (renounceRolePostState evm I).executionEnv = evm.executionEnv := by
  simp [renounceRolePostState, storageStore_executionEnv]

theorem renounceRoleStore_role (I : ExecutionEnv) :
    (renounceRoleStore I).get? "role" = some (renounceRoleRoleValue I) := by
  rw [renounceRoleStore, store_get_ne _ _ (by decide), store_get_self]

theorem renounceRoleStore_callerConfirmation (I : ExecutionEnv) :
    (renounceRoleStore I).get? "callerConfirmation" =
      some (renounceRoleCallerValue I) := by
  rw [renounceRoleStore, store_get_self]

theorem renounceRoleStore_roles (I : ExecutionEnv) :
    (renounceRoleStore I).get? "_roles" = none := by
  rw [renounceRoleStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_renounceRole_role (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.var "role") = .ok (renounceRoleRoleValue I) := by
  rw [evalExpr?, renounceRoleStore_role]
  rfl

theorem evalExpr_renounceRole_callerConfirmation (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.var "callerConfirmation") = .ok (renounceRoleCallerValue I) := by
  rw [evalExpr?, renounceRoleStore_callerConfirmation]
  rfl

theorem evalExpr_renounceRole_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_renounceRole_callerConfirmation_eq_true (evm : EVM.State)
    (I : ExecutionEnv)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat =
      evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.binary .eq (.var "callerConfirmation") sender) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_renounceRole_callerConfirmation,
    evalExpr_renounceRole_sender, bind, EvalResult.bind, evalBinaryOp?]
  unfold renounceRoleCallerValue
  rw [hcaller]
  simp [BEq.beq]

theorem evalExpr_renounceRole_callerConfirmation_eq_false (evm : EVM.State)
    (I : ExecutionEnv)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat ≠
      evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.binary .eq (.var "callerConfirmation") sender) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_renounceRole_callerConfirmation,
    evalExpr_renounceRole_sender, bind, EvalResult.bind, evalBinaryOp?]
  unfold renounceRoleCallerValue
  rw [show ((.address (AccountAddress.ofNat (renounceRoleCallerWord I).toNat) : Value) ==
      .address evm.executionEnv.source) = false by
    simp [BEq.beq, hcaller]]

theorem evalStorageRef_renounceRole_target (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := renounceRoleStore I } evm
      (roleHasRoleRef (.var "role") (.var "callerConfirmation")) =
        .ok (renounceRoleTargetEvaledRef I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef,
    evalExpr_renounceRole_role, evalExpr_renounceRole_callerConfirmation,
    renounceRoleTargetEvaledRef, renounceRoleRoleValue, renounceRoleCallerValue,
    renounceRoleCallerKey, accessControlValueToKey_bytes32_of_length hlen,
    accessControlValueToKey_address, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem evalExpr_renounceRole_target_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "callerConfirmation"))) =
        .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (renounceRoleTargetSlot I))
    (hbase := renounceRoleStore_roles I)
    (her := evalStorageRef_renounceRole_target evm I hsz68)
    (hty := by
      simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_renounceRole_target_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "callerConfirmation"))) =
        .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (renounceRoleTargetSlot I))
    (hbase := renounceRoleStore_roles I)
    (her := evalStorageRef_renounceRole_target evm I hsz68)
    (hty := by
      simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

theorem renounceRoleAssignTarget (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := renounceRoleStore I } evm
      .storage (roleHasRoleRef (.var "role") (.var "callerConfirmation")) (.bool false) =
        .ok ({ contract := contract, locals := renounceRoleStore I },
          renounceRolePostState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := renounceRoleTargetEvaledRef I) (ty := boolSt)
      (loc := boolLoc (renounceRoleTargetSlot I))
      (value := .bool false)
      (evm' := renounceRolePostState evm I)
      (hbase := renounceRoleStore_roles I)
      (her := evalStorageRef_renounceRole_target evm I hsz68)
      (hty := by
        simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
          boolSt, storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, renounceRoleTargetEvaledRef, renounceRoleTargetSlot])
      (hscalar := by trivial)
      (hstore := by
        simpa [boolLoc, boolOffset0Loc, renounceRoleClearLowByteWord] using
          storageLocStore_bool_false_offset0 evm (renounceRoleTargetSlot I))

theorem accessControlRenounceRoleBodyReturns_write (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat = evm.executionEnv.source)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm (renounceRoleStore I) renounceRoleTransition.body
      (.returned { contract := contract, locals := renounceRoleStore I }
        (renounceRolePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_renounceRole_callerConfirmation_eq_true evm I hcaller)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (result := .ok
      ({ contract := contract, locals := renounceRoleStore I } : Frame)
      (renounceRolePostState evm I))
      (evalExpr_renounceRole_target_true evm I hsz68 htarget) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (renounceRoleAssignTarget evm I hsz68)) ?_
    exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlRenounceRoleBodyReturns_noop (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat = evm.executionEnv.source)
    (htarget : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm (renounceRoleStore I) renounceRoleTransition.body
      (.returned { contract := contract, locals := renounceRoleStore I } evm none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_renounceRole_callerConfirmation_eq_true evm I hcaller)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := renounceRoleStore I } : Frame) evm)
      (evalExpr_renounceRole_target_false evm I hsz68 htarget) ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.nil

theorem accessControlRenounceRoleBodyReverts_caller (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller :
      AccountAddress.ofNat (renounceRoleCallerWord I).toNat ≠ evm.executionEnv.source) :
    ExecTransitionBody config contract evm (renounceRoleStore I) renounceRoleTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_renounceRole_callerConfirmation_eq_false evm I hcaller))

def renounceRoleBadConfirmationSelector : UInt256 :=
  UInt256.shiftLeft (⟨860608793⟩ : UInt256) ⟨225⟩

theorem accessControlRenounceRoleX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨235⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨922⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨249⟩, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨233⟩, push2 ⟨249⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨922⟩, jump (by jump_dest) ]⟩

theorem accessControlRenounceRoleX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨235⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨395⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hclean : UInt256.eq (renounceRoleCallerWord I)
      (UInt256.land (renounceRoleCallerWord I) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  obtain ⟨_, _, rd922⟩ := accessControlRenounceRoleX_toDecoder (cA := cA) (gh := gh)
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
        simpa [renounceRoleCallerWord, calldataWord] using hclean
      rw [hc]
      decide) (by jump_dest),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨395⟩, jump (by jump_dest) ]⟩

theorem accessControlRenounceRoleX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨235⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd922⟩ := accessControlRenounceRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlRenounceRoleX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨235⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd922⟩ := accessControlRenounceRoleX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd922 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨939⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlRenounceRoleX_noncanon_caller {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (renounceRoleCallerWord I)
      (UInt256.land (renounceRoleCallerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨235⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd922⟩ := accessControlRenounceRoleX_toDecoder (cA := cA) (gh := gh)
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
      simpa [renounceRoleCallerWord, calldataWord] using hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlRenounceRoleX_caller_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat = I.source)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨395⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨436⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd395⟩ := hreach
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  have hcleanRight :
      UInt256.land (renounceRoleCallerWord I) solcAddrMask = renounceRoleCallerWord I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean_left hcanon
  have hword := renounceRoleCallerWord_eq_sourceWord_of_address hcanon hcaller
  exact ⟨_, _, evm_run rd395 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, caller,
    eq, push2 ⟨436⟩, jumpiT (by
      rw [haddrMask, hcleanRight, hword]
      change UInt256.eq (renounceRoleSourceWord I) (renounceRoleSourceWord I) ≠ ⟨0⟩
      rw [u256_eq_refl]
      decide) (by jump_dest) ]⟩

theorem accessControlRenounceRoleX_caller_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (hcaller : AccountAddress.ofNat (renounceRoleCallerWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨395⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd395⟩ := hreach
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  have hcleanRight :
      UInt256.land (renounceRoleCallerWord I) solcAddrMask = renounceRoleCallerWord I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean_left hcanon
  have heqZero :
      UInt256.eq (UInt256.ofNat I.source.val)
          (UInt256.land (renounceRoleCallerWord I) solcAddrMask) =
        ⟨0⟩ := by
    change UInt256.eq (renounceRoleSourceWord I)
        (UInt256.land (renounceRoleCallerWord I) solcAddrMask) = ⟨0⟩
    rw [hcleanRight]
    apply u256_eq_of_ne
    intro hsrc
    apply hcaller
    exact renounceRoleCallerAddress_eq_source_of_word hsrc.symm
  have rd412 := evm_run rd395 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, caller,
    eq, push2 ⟨436⟩, jumpiNT (by rw [haddrMask, heqZero]) ]
  have rd424 := evm_run rd412 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (solcFreePtrMem_mload64) (by decide) (by evm_ov),
    push4 ⟨860608793⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (solcReturnMem renounceRoleBadConfirmationSelector)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd435 := evm_run rd424 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide) mem_cost
      (solcReturnMem_mload64 renounceRoleBadConfirmationSelector)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have hlen4 : ((⟨4⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨4⟩ := by
    decide
  have rd435' := rd435
  rw [hlen4] at rd435'
  exact rd435'.rev 0 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by simp)

theorem accessControlRenounceRoleX_revoke_noop {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (htarget : renounceRoleMaskedWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨436⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) ByteArray.empty := by
  obtain ⟨_, _, rd436⟩ := hreach
  have rd683 := evm_run rd436 with [
    jumpdest, push2 ⟨446⟩, dup3, dup3, push2 ⟨683⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd683 with [
    jumpdest, push0, push2 ⟨694⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨694⟩, ⟨0⟩,
          renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨446⟩,
          renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, rd451⟩
  have hslot := revokeRoleAdminHasRoleKeccakSlotFrom (renounceRoleRoleWord I)
    (renounceRoleCallerWord I) solcFreePtrMem solcFreePtrMem_size hcanon
  obtain ⟨_, _, rd694₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := renounceRoleRoleWord I) (account := renounceRoleCallerWord I)
    (ret := ⟨694⟩) (mem0 := solcFreePtrMem)
    (R := [⟨0⟩, renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨446⟩,
      renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel])
    solcFreePtrMem_size solcFreePtrMem_read64 hcanon (by jump_dest) (by simp) hslot rd451'
  have htargetSlotEq := renounceRoleTargetSlot_fixedBytes32 I hsz68 hcanon
  have rd694 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
        (renounceRoleMaskedWord σ I :: ⟨0⟩ :: renounceRoleCallerWord I ::
          renounceRoleRoleWord I :: ⟨446⟩ :: renounceRoleCallerWord I ::
          renounceRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
          solcFreePtrMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [renounceRoleMaskedWord, renounceRoleStorageWord, revokeRoleStorageWordAt,
        ← htargetSlotEq] using rd694₀⟩
  obtain ⟨_, _, rd694⟩ := rd694
  have rd233 := evm_run rd694 with [
    jumpdest, iszero, push2 ⟨676⟩, jumpiT (by rw [htarget]; decide) (by jump_dest),
    jumpdest, pop, push0, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlRenounceRoleX_revoke_write {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus)
    (htarget : renounceRoleMaskedWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨436⟩
      [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, renounceRolePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd436⟩ := hreach
  have rd683 := evm_run rd436 with [
    jumpdest, push2 ⟨446⟩, dup3, dup3, push2 ⟨683⟩, jump (by jump_dest) ]
  have rd451 := evm_run rd683 with [
    jumpdest, push0, push2 ⟨694⟩, dup4, dup4, push2 ⟨451⟩, jump (by jump_dest) ]
  have rd451' :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
        [renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨694⟩, ⟨0⟩,
          renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨446⟩,
          renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, rd451⟩
  have hslot := revokeRoleAdminHasRoleKeccakSlotFrom (renounceRoleRoleWord I)
    (renounceRoleCallerWord I) solcFreePtrMem solcFreePtrMem_size hcanon
  obtain ⟨_, _, rd694₀⟩ := accessControlX_hasRole_internal
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (role := renounceRoleRoleWord I) (account := renounceRoleCallerWord I)
    (ret := ⟨694⟩) (mem0 := solcFreePtrMem)
    (R := [⟨0⟩, renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨446⟩,
      renounceRoleCallerWord I, renounceRoleRoleWord I, ⟨233⟩, sel])
    solcFreePtrMem_size solcFreePtrMem_read64 hcanon (by jump_dest) (by simp) hslot rd451'
  let memTarget :=
    revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
      solcFreePtrMem
  have htargetSlotEq := renounceRoleTargetSlot_fixedBytes32 I hsz68 hcanon
  have rd694 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
        (renounceRoleMaskedWord σ I :: ⟨0⟩ :: renounceRoleCallerWord I ::
          renounceRoleRoleWord I :: ⟨446⟩ :: renounceRoleCallerWord I ::
          renounceRoleRoleWord I :: ⟨233⟩ :: sel :: [])
        memTarget (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [memTarget, renounceRoleMaskedWord, renounceRoleStorageWord,
        revokeRoleStorageWordAt, ← htargetSlotEq] using rd694₀⟩
  obtain ⟨_, _, rd694⟩ := rd694
  have hmemTarget : memTarget.size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ solcFreePtrMem_size
  have hreadTarget : memTarget.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have rd700 := evm_run rd694 with [
    jumpdest, iszero, push2 ⟨676⟩, jumpiNT (isZero_eq_zero_of_ne htarget) ]
  have rd713pre := evm_run rd700 with [
    push0, dup4, dup2,
    raw mstore 0 (revokeRoleWordAt0Mem (renounceRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (revokeRoleBaseHashMemFrom (renounceRoleRoleWord I) memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4]
  have hbaseSlotRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleBaseHashMemFrom (renounceRoleRoleWord I) memTarget)
            |>.readWithPadding 0 64))) =
        revokeRoleBaseSlot (renounceRoleRoleWord I) := by
    unfold revokeRoleBaseSlot
    rw [revokeRoleBaseHashMemFrom_read0_64 _ hmemTarget, revokeRoleBaseHashMem_read0_64]
  have rd723pre := evm_run rd713pre with [
    raw keccak256 0 (revokeRoleBaseSlot (renounceRoleRoleWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hbaseSlotRaw (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and]
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  have hcallerClean :
      UInt256.land solcAddrMask (renounceRoleCallerWord I) = renounceRoleCallerWord I :=
    solcAddrMask_clean_left hcanon
  have hcallerCleanRight :
      UInt256.land (renounceRoleCallerWord I) solcAddrMask = renounceRoleCallerWord I := by
    rw [u256_land_comm]
    exact hcallerClean
  rw [haddrMask, hcallerCleanRight] at rd723pre
  have rd731pre := evm_run rd723pre with [
    dup1, dup6,
    raw mstore 0
      (revokeRoleHasRoleAccountMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap3,
    raw mstore 0
      (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
        memTarget)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup1, dup4]
  have hslotWrite :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I)
            (renounceRoleCallerWord I) memTarget).readWithPadding 0 64))) =
        renounceRoleTargetSlot I := by
    rw [revokeRoleAdminHasRoleKeccakSlotFrom (renounceRoleRoleWord I)
      (renounceRoleCallerWord I) memTarget hmemTarget hcanon, ← htargetSlotEq]
  have rd732 := evm_run rd731pre with [
    raw keccak256 0 (renounceRoleTargetSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslotWrite (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd733₀⟩ := rd732.sload (by decide) (by evm_ov)
  have rd733 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨734⟩
        [renounceRoleStorageWord σ I, renounceRoleTargetSlot I, ⟨64⟩,
          renounceRoleCallerWord I, ⟨0⟩, ⟨0⟩, renounceRoleCallerWord I,
          renounceRoleRoleWord I, ⟨446⟩, renounceRoleCallerWord I,
          renounceRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [renounceRoleStorageWord, revokeRoleStorageWordAt] using rd733₀⟩
  obtain ⟨_, _, rd733⟩ := rd733
  have hclearComm :
      UInt256.land (UInt256.lnot ⟨255⟩) (renounceRoleStorageWord σ I) =
        renounceRoleClearLowByteWord (renounceRoleStorageWord σ I) := by
    unfold renounceRoleClearLowByteWord
    exact u256_land_comm (UInt256.lnot ⟨255⟩)
      (renounceRoleStorageWord σ I)
  have rd739pre := evm_run rd733 with [push1 ⟨255⟩, not, and, swap1]
  rw [hclearComm] at rd739pre
  obtain ⟨_, _, rd740₀⟩ := rd739pre.sstore hperm (by decide) (by evm_ov)
  have rd740 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨740⟩
        [⟨64⟩, renounceRoleCallerWord I, ⟨0⟩, ⟨0⟩, renounceRoleCallerWord I,
          renounceRoleRoleWord I, ⟨446⟩, renounceRoleCallerWord I,
          renounceRoleRoleWord I, ⟨233⟩, sel]
        (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
          memTarget)
        (UInt256.ofNat 3) ByteArray.empty (cA, renounceRolePostMap σ I) k C := by
    exact ⟨_, _, by simpa [renounceRolePostMap] using rd740₀⟩
  obtain ⟨_, _, rd740⟩ := rd740
  have hmemEvent :
      (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
        memTarget).size = 96 := by
    exact revokeRoleHasRoleSlotHashMemFrom_size _ _ hmemTarget
  have hreadEvent :
      (revokeRoleHasRoleSlotHashMemFrom (renounceRoleRoleWord I) (renounceRoleCallerWord I)
        memTarget).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact revokeRoleHasRoleSlotHashMemFrom_read64 _ _ hmemTarget hreadTarget
  have rd745pre := evm_run rd740 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (revokeRoleHasRoleSlotHashMemFrom_mload64 (renounceRoleRoleWord I)
        (renounceRoleCallerWord I) hmemTarget hreadTarget)
      (by decide) (by evm_ov),
    caller, swap3, dup7, swap2]
  have rd745 := rd745pre.pushConst revokeRoleRevokedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd780 := evm_run rd745 with [swap2, swap1]
  have rd781 := RD.log4 0 (UInt256.ofNat 3) rd780 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by simp)
  have rd233 := evm_run rd781 with [
    pop, push1 ⟨1⟩, push2 ⟨347⟩, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest),
    jumpdest]
  exact rd233.stop (by decide) (by evm_ov)

theorem accessControlRenounceRoleBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨235⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := renounceRoleSelector_size (by simpa [selIs] using hsel)
  have hd := accessControlDispatch_renounceRole (cd := I.calldata)
    (by simpa [selIs] using hsel)
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus
      · have hdec := accessControlDecode_renounceRole_ok (I := I) hsz68 hbig hcanon
        have htargetWord :
            renounceRoleStorageWord σ_evm I = renounceRoleStorageWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (renounceRoleTargetSlot I) ⟨0⟩
        have rd395 := accessControlRenounceRoleX_decoded (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hcanon hreach
        by_cases hcaller :
            AccountAddress.ofNat (renounceRoleCallerWord I).toNat = I.source
        · have rd436 := accessControlRenounceRoleX_caller_ok (g := Sat256.ofUInt256 g)
            hcanon hcaller rd395
          have hcallerSolm :
              AccountAddress.ofNat (renounceRoleCallerWord I).toNat = evmS.executionEnv.source := by
            simpa [evmS, initState] using hcaller
          by_cases htarget : renounceRoleMaskedWord σ_evm I = ⟨0⟩
          · have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (renounceRoleTargetSlot I)) ⟨255⟩ = ⟨0⟩ := by
              have hmaskEq :
                  renounceRoleMaskedWord σ_evm I = renounceRoleMaskedWord σ_solm I := by
                unfold renounceRoleMaskedWord
                rw [htargetWord]
              have hword : renounceRoleMaskedWord σ_solm I = ⟨0⟩ := by
                rw [← hmaskEq]
                exact htarget
              simpa [renounceRoleMaskedWord, renounceRoleStorageWord, evmS, initState,
                Solm.EVM.storageLoad, State.lookupAccount] using hword
            have hbody := accessControlRenounceRoleBodyReturns_noop evmS I hsz68
              (by simp only [evmS, initState]; exact hwv) hcallerSolm htargetSolm
            exact (accessControlRenounceRoleX_revoke_noop (g := Sat256.ofUInt256 g)
                hsz68 hcanon htarget rd436)
              |>.reEquivExecution hcode hd hdec hbody hAccounts (returnEquiv.fallthrough rfl rfl (by native_decide))
          · have htargetNonzero : renounceRoleMaskedWord σ_evm I ≠ ⟨0⟩ := htarget
            have htargetSolm :
                UInt256.land
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                    (renounceRoleTargetSlot I)) ⟨255⟩ ≠ ⟨0⟩ := by
              have hmaskEq :
                  renounceRoleMaskedWord σ_evm I = renounceRoleMaskedWord σ_solm I := by
                unfold renounceRoleMaskedWord
                rw [htargetWord]
              have hword : renounceRoleMaskedWord σ_solm I ≠ ⟨0⟩ := by
                rw [← hmaskEq]
                exact htargetNonzero
              simpa [renounceRoleMaskedWord, renounceRoleStorageWord, evmS, initState,
                Solm.EVM.storageLoad, State.lookupAccount] using hword
            have hbody := accessControlRenounceRoleBodyReturns_write evmS I hsz68
              (by simp only [evmS, initState]; exact hwv) hcallerSolm htargetSolm
            have hval :
                renounceRoleClearLowByteWord
                    (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                      (renounceRoleTargetSlot I)) =
                  renounceRoleClearLowByteWord
                    (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                      (renounceRoleTargetSlot I)) := by
              simpa [evmE, evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                renounceRoleStorageWord] using congrArg renounceRoleClearLowByteWord htargetWord
            have hσPost :
                EVMStateEquiv (renounceRolePostState evmE I) (renounceRolePostState evmS I) := by
              simpa [renounceRolePostState] using
                accessControlEVMStateEquiv_storageStore_codeOwner hσ (renounceRoleTargetSlot I) hval
            exact (accessControlRenounceRoleX_revoke_write (g := Sat256.ofUInt256 g)
                hperm hsz68 hcanon htargetNonzero rd436)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [renounceRolePostState, evmE, initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by
                  simp [renounceRolePostState, renounceRolePostMap, evmE, initState,
                    storageStore_accountMap, Solm.EVM.storageLoad, State.lookupAccount,
                    Account.lookupStorage, renounceRoleStorageWord]))
                hσPost
                (returnEquiv.fallthrough rfl rfl (by native_decide))
        · have hcallerSolm :
              AccountAddress.ofNat (renounceRoleCallerWord I).toNat ≠ evmS.executionEnv.source := by
            simpa [evmS, initState] using hcaller
          have hbody := accessControlRenounceRoleBodyReverts_caller evmS I
            (by simp only [evmS, initState]; exact hwv) hcallerSolm
          exact (accessControlRenounceRoleX_caller_revert (g := Sat256.ofUInt256 g)
              hcanon hcaller rd395)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := accessControlDecode_renounceRole_none_noncanon_caller
          (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (renounceRoleCallerWord I)
            (UInt256.land (renounceRoleCallerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (accessControlRenounceRoleX_noncanon_caller (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_renounceRole_none_huge (I := I) hbigge
      exact (accessControlRenounceRoleX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := accessControlDecode_renounceRole_none_short (I := I) hsz4 hshort
    exact (accessControlRenounceRoleX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
