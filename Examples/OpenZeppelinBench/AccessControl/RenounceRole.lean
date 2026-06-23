import Examples.OpenZeppelinBench.AccessControl.Storage
import Examples.SimpleAuction.Storage
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
    (accessControlByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [defaultAdminRoleTransition, getRoleAdminTransition, grantRoleTransition,
      hasRoleTransition])
    (post := [revokeRoleTransition, supportsInterfaceTransition]) rfl ?_
    (by rw [selectorOf, renounceRoleSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, defaultAdminRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, getRoleAdminSelectorBytes, hcd]; decide
  · rw [selectorOf, grantRoleSelectorBytes, hcd]; decide
  · rw [selectorOf, hasRoleSelectorBytes, hcd]; decide

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

theorem accessControlDecode_renounceRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (renounceRoleCallerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata =
        some (renounceRoleStore I) := by
  show decodeCalldata ["role", "callerConfirmation"] [bytes32, addr] I.calldata =
    some (renounceRoleStore I)
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
      renounceRoleCallerWord I := by
    simpa [renounceRoleCallerWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, isDynamicABIType])]
  rw [if_neg (by
    rintro ⟨_, hc⟩
    rw [List.length_drop, htlen] at hc
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_ok (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          renounceRoleCallerWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanon)]
  rw [if_neg (by
    rw [List.length_drop, htlen]
    omega : ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, renounceRoleStore, renounceRoleRoleValue,
    renounceRoleCallerValue]
  rw [hword36]

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

theorem renounceRoleKeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem renounceRoleU256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show (Fin.land a.val b.val).val = (Fin.land b.val a.val).val
  simp only [Fin.land]
  exact congrArg (fun n => n % UInt256.size) (Nat.land_comm a.val.val b.val.val)

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
  rw [renounceRoleKeyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single (renounceRoleCallerWord I)
    (roleDataSlot (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)))

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

theorem evalStorageRef_renounceRole_target (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := renounceRoleStore I } evm
      (roleHasRoleRef (.var "role") (.var "callerConfirmation")) =
        .ok (renounceRoleTargetEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, roleHasRoleRef,
    evalExpr_renounceRole_role, evalExpr_renounceRole_callerConfirmation,
    renounceRoleTargetEvaledRef, renounceRoleRoleValue, renounceRoleCallerValue,
    renounceRoleCallerKey, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem evalExpr_renounceRole_target_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "callerConfirmation"))) =
        .ok (.bool true) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (renounceRoleTargetSlot I))
    (hbase := renounceRoleStore_roles I)
    (her := evalStorageRef_renounceRole_target evm I)
    (hty := by
      simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_true evm _ hnz]

theorem evalExpr_renounceRole_target_false (evm : EVM.State) (I : ExecutionEnv)
    (hzero : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (renounceRoleTargetSlot I)) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := renounceRoleStore I } evm
      (.storage (roleHasRoleRef (.var "role") (.var "callerConfirmation"))) =
        .ok (.bool false) := by
  rw [evalExpr_storage_scalar (t := .bool)
    (loc := boolLoc (renounceRoleTargetSlot I))
    (hbase := renounceRoleStore_roles I)
    (her := evalStorageRef_renounceRole_target evm I)
    (hty := by
      simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
        boolSt, storageTypeStep?])
    (hloc := by
      rfl)]
  rw [accessControlStorageLocLoad_bool_offset0_false evm _ hzero]

-- PROMOTE -> Reasoning.Storage: packed `bool := false` at byte offset 0.
theorem renounceRolePackedSetFalseWord_eq (w : UInt256) :
    renounceRoleClearLowByteWord w = UInt256.ofNat (256 * (w.toNat / 256)) := by
  unfold renounceRoleClearLowByteWord
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

theorem renounceRolePackedSetFalseWord_toNat (w : UInt256) :
    (renounceRoleClearLowByteWord w).toNat = 256 * (w.toNat / 256) := by
  rw [renounceRolePackedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

theorem renounceRoleStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (renounceRoleClearLowByteWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord boolLoc renounceRoleClearLowByteWord
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
  simpa [renounceRoleClearLowByteWord] using
    (renounceRolePackedSetFalseWord_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).symm

theorem renounceRoleAssignTarget (evm : EVM.State) (I : ExecutionEnv) :
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
      (her := evalStorageRef_renounceRole_target evm I)
      (hty := by
        simp [storageTypeAt?, renounceRoleTargetEvaledRef, contract, storageDecls, roleDataSt,
          boolSt, storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, renounceRoleTargetEvaledRef, renounceRoleTargetSlot])
      (hscalar := by trivial)
      (hstore := by
        exact renounceRoleStorageLocStore_bool_false_offset0 evm (renounceRoleTargetSlot I))

theorem accessControlRenounceRoleBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcaller :
      AccountAddress.ofNat (renounceRoleCallerWord I).toNat = evm.executionEnv.source) :
    ExecTransitionBody config contract evm (renounceRoleStore I) renounceRoleTransition.body
      (.returned { contract := contract, locals := renounceRoleStore I }
        (renounceRolePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_renounceRole_callerConfirmation_eq_true evm I hcaller)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (renounceRoleAssignTarget evm I)) ?_
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

end OpenZeppelinBench.AccessControl
