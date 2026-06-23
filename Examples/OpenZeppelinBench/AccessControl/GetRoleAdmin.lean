import Examples.OpenZeppelinBench.AccessControl.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl `getRoleAdmin(bytes32)` proof

The body decodes a single `bytes32`, reads `_roles[role].adminRole`, and returns the
full storage word.
-/

abbrev getRoleAdminRoleWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev getRoleAdminRoleBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev getRoleAdminRoleValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (getRoleAdminRoleBytes I)

abbrev getRoleAdminStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "role" (getRoleAdminRoleValue I)

abbrev getRoleAdminRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (getRoleAdminRoleBytes I)

def getRoleAdminEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_roles", steps := [.mindex (getRoleAdminRoleKey I), .field "adminRole"] }

def getRoleAdminSlot (I : ExecutionEnv) : UInt256 :=
  roleAdminSlot (getRoleAdminRoleKey I)

def getRoleAdminLoc (I : ExecutionEnv) : StorageLoc :=
  bytes32Loc (getRoleAdminSlot I)

def getRoleAdminBaseSlot (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray
    (ffi.KEC (UInt256.toByteArray (getRoleAdminRoleWord I) ++
      UInt256.toByteArray (⟨0⟩ : UInt256)))

def getRoleAdminWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (getRoleAdminSlot I) ⟨0⟩)

def getRoleAdminCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (getRoleAdminSlot I)

theorem getRoleAdminWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    getRoleAdminWord σ I = getRoleAdminWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (getRoleAdminSlot I) ⟨0⟩

theorem getRoleAdminKeyValueToWord {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (getRoleAdminRoleKey I) = getRoleAdminRoleWord I := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (getRoleAdminRoleBytes I).length = 32 := by
    rw [getRoleAdminRoleBytes, List.length_take, List.length_drop, htlen]
    omega
  simp [keyValueToWord, bytes32Width, getRoleAdminRoleBytes, hlen]
  unfold getRoleAdminRoleWord calldataWord
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide)]
  rw [byteArray_toList_eq]

theorem getRoleAdminAddSlot_eq (slot : UInt256) :
    EVM.word (slot.toNat + 1) = slot + (⟨1⟩ : UInt256) := by
  apply u256_inj
  rw [uadd_toNat]
  change (slot.toNat + 1) % UInt256.size = (slot.toNat + 1) % UInt256.size
  rfl

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `UInt256` addition is commutative.
theorem getRoleAdminU256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  simp [uadd_toNat, Nat.add_comm]

theorem getRoleAdminSlot_evm (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    getRoleAdminSlot I = getRoleAdminBaseSlot I + ⟨1⟩ := by
  unfold getRoleAdminSlot roleAdminSlot roleDataSlot mapSlot addSlot getRoleAdminRoleKey
  rw [getRoleAdminKeyValueToWord hsz36]
  rw [getRoleAdminAddSlot_eq]
  rfl

theorem accessControlGetRoleAdminSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem accessControlDispatch_getRoleAdmin {cd : ByteArray}
    (hsel : ((⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ : ByteArray) == cd.extract 0 4) =
      true) :
    dispatchMsg contract cd = some getRoleAdminTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ : ByteArray) :=
    (accessControlByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [defaultAdminRoleTransition])
    (post := [grantRoleTransition, hasRoleTransition, renounceRoleTransition,
      revokeRoleTransition, supportsInterfaceTransition])
    rfl ?_ (by rw [selectorOf, getRoleAdminSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]
  decide

-- PROMOTE -> Reasoning.ABI: single fixed-bytes32 calldata decoder.
theorem accessControlDecode_getRoleAdmin_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata =
        some (getRoleAdminStore I) := by
  show decodeCalldata ["role"] [bytes32] I.calldata = some (getRoleAdminStore I)
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes32].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes32].isEmpty = false ∧
      2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 =
      some ((I.calldata.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have htake : List.take 32 ((I.calldata.toList.drop 4).take 32) =
      (I.calldata.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ I.calldata.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, bytes32, ABI.decodeABIValues?,
    ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad,
    getRoleAdminStore, getRoleAdminRoleValue, getRoleAdminRoleBytes, bytes32Width, htake,
    hnotArgShort]

theorem accessControlDecode_getRoleAdmin_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role"] [bytes32] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes32].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes32].isEmpty = false ∧
      2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, bytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem accessControlDecode_getRoleAdmin_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["role"] [bytes32] I.calldata = none
  unfold decodeCalldata
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have hHuge : [bytes32].isEmpty = false ∧
        2 ^ 255 ≤ (I.calldata.toList.drop 4).length := by
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      simp
      omega
    have hnotDyn : ¬ ([bytes32].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
      simp [bytes32, isDynamicABIType]
    rw [if_neg hnotDyn, if_pos hHuge]

theorem accessControlGetRoleAdminBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
  ExecTransitionBody config contract evm (getRoleAdminStore I) getRoleAdminTransition.body
      (.returned { contract := contract, locals := getRoleAdminStore I } evm
        (some (.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (getRoleAdminCurrent evm I))))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her :
          evalStorageRef config { contract := contract, locals := getRoleAdminStore I } evm
            (roleAdminRef (.var "role")) = .ok (getRoleAdminEvaledRef I) := by
        simp [evalStorageRef, evalStorageRefStep, roleAdminRef, getRoleAdminStore,
          getRoleAdminRoleValue, getRoleAdminRoleKey, getRoleAdminEvaledRef, valueToKey?,
          EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
      have hty :
          storageTypeAt? contract.storage (getRoleAdminEvaledRef I) =
            some (.elem (.bytes bytes32Width)) := by
        simp [getRoleAdminEvaledRef, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          roleDataStruct, roleDataSt, bytes32St]
      have hloc :
          config.storage.layout (getRoleAdminEvaledRef I) = fun _ => some (getRoleAdminLoc I) := by
        funext evm'
        simp [config, storageLayout, getRoleAdminEvaledRef, getRoleAdminLoc, getRoleAdminSlot]
      rw [evalExpr_storage_scalar (t := .bytes bytes32Width)
        (hbase := by simp [getRoleAdminStore, roleAdminRef])
        (her := her) (hty := hty) (hloc := hloc)]
      rw [show storageLocLoad evm (getRoleAdminLoc I) =
          .fixedBytes bytes32Width
            (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (getRoleAdminSlot I))) by
        simpa [getRoleAdminLoc] using
          accessControlStorageLocLoad_bytes32 evm (getRoleAdminSlot I)]
      simp [getRoleAdminCurrent])

/-! ## EVM scratch memory and trace -/

-- PROMOTE -> Common.lean: generic two-word scratch-memory helpers.
noncomputable def getRoleAdminWordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def getRoleAdminWordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def getRoleAdminTwoWordHashMem (key slot : UInt256) (mem : ByteArray) :
    ByteArray :=
  getRoleAdminWordAt32Mem slot (getRoleAdminWordAt0Mem key mem)

theorem getRoleAdminWordAt0Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminWordAt0Mem word mem).size = 96 := by
  unfold getRoleAdminWordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem getRoleAdminWordAt32Mem_size {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminWordAt32Mem word mem).size = 96 := by
  unfold getRoleAdminWordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem getRoleAdminTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminTwoWordHashMem key slot mem).size = 96 := by
  unfold getRoleAdminTwoWordHashMem
  exact getRoleAdminWordAt32Mem_size slot (getRoleAdminWordAt0Mem_size key hmem)

theorem getRoleAdminWordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (getRoleAdminWordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold getRoleAdminWordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

theorem getRoleAdminTwoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminTwoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold getRoleAdminTwoWordHashMem getRoleAdminWordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [getRoleAdminWordAt0Mem_size key hmem]; omega) (by omega)]
  unfold getRoleAdminWordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem getRoleAdminTwoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminTwoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold getRoleAdminTwoWordHashMem getRoleAdminWordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [getRoleAdminWordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem getRoleAdminTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (getRoleAdminTwoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold getRoleAdminTwoWordHashMem getRoleAdminWordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [getRoleAdminWordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [getRoleAdminWordAt0Mem_size key hmem])]
  exact getRoleAdminWordAt0Mem_read64 key hmem hread64

set_option maxHeartbeats 800000 in
theorem getRoleAdminTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (getRoleAdminTwoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [getRoleAdminTwoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (getRoleAdminTwoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [getRoleAdminTwoWordHashMem_size key slot hmem]; omega),
      getRoleAdminTwoWordHashMem_read0 key slot hmem]
  have hright :
      (getRoleAdminTwoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [getRoleAdminTwoWordHashMem_size key slot hmem]; omega),
      getRoleAdminTwoWordHashMem_read32 key slot hmem]
  rw [show (getRoleAdminTwoWordHashMem key slot mem).extract 0 64 =
      (getRoleAdminTwoWordHashMem key slot mem).extract 0 32 ++
        (getRoleAdminTwoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

noncomputable def getRoleAdminRoleMem (I : ExecutionEnv) : ByteArray :=
  getRoleAdminWordAt0Mem (getRoleAdminRoleWord I) solcFreePtrMem

noncomputable def getRoleAdminHashMem (I : ExecutionEnv) : ByteArray :=
  getRoleAdminTwoWordHashMem (getRoleAdminRoleWord I) ⟨0⟩ solcFreePtrMem

noncomputable def getRoleAdminReturnMem (I : ExecutionEnv) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (getRoleAdminHashMem I) 128 32

theorem getRoleAdminRoleMem_size (I : ExecutionEnv) :
    (getRoleAdminRoleMem I).size = 96 := by
  unfold getRoleAdminRoleMem
  exact getRoleAdminWordAt0Mem_size (getRoleAdminRoleWord I) solcFreePtrMem_size

theorem getRoleAdminHashMem_size (I : ExecutionEnv) :
    (getRoleAdminHashMem I).size = 96 := by
  unfold getRoleAdminHashMem
  exact getRoleAdminTwoWordHashMem_size (getRoleAdminRoleWord I) ⟨0⟩ solcFreePtrMem_size

theorem getRoleAdminHashMem_read64 (I : ExecutionEnv) :
    (getRoleAdminHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold getRoleAdminHashMem
  exact getRoleAdminTwoWordHashMem_read64 (getRoleAdminRoleWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem getRoleAdminHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (getRoleAdminHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRoleAdminHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [getRoleAdminHashMem_size]; decide) (by decide)
    (getRoleAdminHashMem_read64 I)

theorem getRoleAdminHashMem_read0_64 (I : ExecutionEnv) :
    (getRoleAdminHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (getRoleAdminRoleWord I) ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold getRoleAdminHashMem
  exact getRoleAdminTwoWordHashMem_read0_64 (getRoleAdminRoleWord I) ⟨0⟩
    solcFreePtrMem_size

theorem getRoleAdminBaseKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((getRoleAdminHashMem I).readWithPadding
          (⟨0⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat))) =
      getRoleAdminBaseSlot I := by
  rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
    show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  rw [getRoleAdminHashMem_read0_64]
  unfold getRoleAdminBaseSlot
  exact mappingSlot_single (getRoleAdminRoleWord I) ⟨0⟩

theorem getRoleAdminReturnMem_size (I : ExecutionEnv) (val : UInt256) :
    (getRoleAdminReturnMem I val).size = 160 := by
  unfold getRoleAdminReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [getRoleAdminHashMem_size]; omega)
      (by rw [getRoleAdminHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, getRoleAdminHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem getRoleAdminReturnMem_read64 (I : ExecutionEnv) (val : UInt256) :
    (getRoleAdminReturnMem I val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold getRoleAdminReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [getRoleAdminHashMem_size]; omega)
      (by rw [getRoleAdminHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, getRoleAdminHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, getRoleAdminHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [getRoleAdminHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [getRoleAdminHashMem_size]),
    getRoleAdminHashMem_read64]

theorem getRoleAdminReturnMem_mload64 (I : ExecutionEnv) (val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (getRoleAdminReturnMem I val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRoleAdminReturnMem I val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [getRoleAdminReturnMem_size]; decide) (by decide)
    (getRoleAdminReturnMem_read64 I val)

theorem getRoleAdminReturnMem_read128 (I : ExecutionEnv) (val : UInt256) :
    (getRoleAdminReturnMem I val).readWithPadding 128 32 = UInt256.toByteArray val := by
  unfold getRoleAdminReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [getRoleAdminHashMem_size]; omega)
      (by rw [getRoleAdminHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, getRoleAdminHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (getRoleAdminHashMem I ++ ffi.ByteArray.zeroes (USize.ofNat (128 - (getRoleAdminHashMem I).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, getRoleAdminHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, getRoleAdminHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

theorem accessControlGetRoleAdminX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨166⟩ [accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨899⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨180⟩, ⟨200⟩, accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd166⟩ := hreach
  exact ⟨_, _, evm_run rd166 with [
    jumpdest, push2 ⟨200⟩, push2 ⟨180⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨899⟩, jump (by jump_dest) ]⟩

theorem accessControlGetRoleAdminX_decodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨166⟩ [accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd899⟩ := accessControlGetRoleAdminX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hreach
  exact evm_run rd899 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨915⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem accessControlGetRoleAdminX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨166⟩ [accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨180⟩
      [getRoleAdminRoleWord I, ⟨200⟩, accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd899⟩ := accessControlGetRoleAdminX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hreach
  have rd915 := evm_run rd899 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨915⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  have rd180 := evm_run rd915 with [jumpdest, pop, calldataload, swap2, swap1, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa [getRoleAdminRoleWord, calldataWord] using rd180⟩

theorem accessControlGetRoleAdminX {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD accessControlBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨166⟩ [accessControlSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret accessControlBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (getRoleAdminWord σ I)) := by
  obtain ⟨_, _, rd180⟩ := accessControlGetRoleAdminX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hsz36 hsize hszhi hreach
  have hslot := getRoleAdminBaseKeccakSlot I
  have rd194pre := evm_run rd180 with [
    jumpdest, push0, swap1, dup2,
    raw mstore 0 (getRoleAdminRoleMem I) (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (getRoleAdminHashMem I) (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (getRoleAdminBaseSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    push1 ⟨1⟩, add]
  obtain ⟨_, _, rd198₀⟩ := rd194pre.sload (by decide) (by evm_ov)
  have rd198 :
      ∃ k C, RD accessControlBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨198⟩
        [getRoleAdminWord σ I, ⟨200⟩, accessControlSelWord I]
        (getRoleAdminHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      have hpc198 :
          (⟨180⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
                        ⟨1⟩ +
                      ⟨1⟩ +
                    ⟨1⟩ +
                  UInt256.ofNat 2 +
                ⟨1⟩ +
              ⟨1⟩ +
            UInt256.ofNat 2 +
          ⟨1⟩ +
          ⟨1⟩ : UInt256) = ⟨198⟩ := by
        decide
      simpa [hpc198, getRoleAdminWord, getRoleAdminSlot_evm I hsz36,
        getRoleAdminU256_add_comm] using rd198₀⟩
  obtain ⟨_, _, rd198⟩ := rd198
  have rd200 := evm_run rd198 with [swap1, jump (by jump_dest)]
  have rd157 := evm_run rd200 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (getRoleAdminHashMem_mload64 I)
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (getRoleAdminReturnMem I (getRoleAdminWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨157⟩, jump (by jump_dest) ]
  exact evm_run rd157 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (getRoleAdminReturnMem_mload64 I (getRoleAdminWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (getRoleAdminWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide]
        exact getRoleAdminReturnMem_read128 I (getRoleAdminWord σ I))
      (by evm_ov) ]

theorem accessControlGetRoleAdminBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = accessControlBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩)
    (hreach : ∃ k C, RD accessControlBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨166⟩
      [accessControlSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := accessControlGetRoleAdminSelector_size hsel
  have hd := accessControlDispatch_getRoleAdmin (cd := I.calldata) (by
    simpa [selIs] using hsel)
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hdec := accessControlDecode_getRoleAdmin_ok (I := I) hsz36 hbig
      have hword : getRoleAdminWord σ_evm I = getRoleAdminWord σ_solm I :=
        getRoleAdminWord_accountMapEquiv hAccounts
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (getRoleAdminStore I) getRoleAdminTransition.body
            (.returned { contract := contract, locals := getRoleAdminStore I }
              (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
              (some (.fixedBytes bytes32Width
                (EVM.Word.toBytesBE (getRoleAdminWord σ_solm I))))) := by
        simpa [getRoleAdminCurrent, getRoleAdminWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using
          accessControlGetRoleAdminBodyReturns
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv)
      exact (accessControlGetRoleAdminX (g := Sat256.ofUInt256 g) hsz36 hsize hbig hreach)
        |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]; rfl) hAccounts
          (returnEquiv_of_encode (accessControlBytes32ReturnEncoding (getRoleAdminWord σ_evm I)))
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := accessControlDecode_getRoleAdmin_none_huge (I := I) hbigge
      have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
        solcDecodeLenCheckHuge_4_32 hbigge hsize
      exact (accessControlGetRoleAdminX_decodeRevert (g := Sat256.ofUInt256 g) hslt hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := accessControlDecode_getRoleAdmin_none_short (I := I) hsz4 hshort
    have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
      solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
    exact (accessControlGetRoleAdminX_decodeRevert (g := Sat256.ofUInt256 g) hslt hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.AccessControl
