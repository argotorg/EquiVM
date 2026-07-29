import Benchmarks.Dss.Dai.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `burn(address,uint256)` -/

abbrev burnUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev burnUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (burnUsrWord I)

abbrev burnWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev burnSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev burnUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (burnUsrWord I).toNat)

abbrev burnWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnWadWord I).toNat)

abbrev burnUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (burnUsrWord I).toNat)

abbrev burnSpenderKey (evm : EVM.State) : KeyValue :=
  .address evm.executionEnv.source

abbrev burnStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (burnUsrValue I)).insert "wad" (burnWadValue I)

def burnUsrSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (burnUsrKey I)

def burnAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (burnUsrKey I) (burnSpenderKey evm)

abbrev burnTotalSupplySlot : UInt256 :=
  ⟨1⟩

def burnUsrBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (burnUsrSlot I)

def burnAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (burnAllowanceSlot evm I)

def burnTotalSupplyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner burnTotalSupplySlot

def burnAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnAllowanceWord evm I).toNat - (burnWadWord I).toNat)

def burnUsrDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat)

def burnSupplyDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat)

def burnAfterAllowanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (burnAllowanceSlot evm I)
    (burnAllowanceDebitWord evm I)

theorem burnAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (burnAfterAllowanceState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp [burnAfterAllowanceState, storageStore_executionEnv]

theorem burnAfterAllowance_source (evm : EVM.State) (I : ExecutionEnv) :
    (burnAfterAllowanceState evm I).executionEnv.source = evm.executionEnv.source := by
  simp [burnAfterAllowanceState, storageStore_executionEnv]

def burnAfterUsrDebitState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (burnUsrSlot I)
    (burnUsrDebitWord evm I)

theorem burnAfterUsrDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (burnAfterUsrDebitState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp [burnAfterUsrDebitState, storageStore_executionEnv]

def burnPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (burnAfterUsrDebitState evm I)
    (burnAfterUsrDebitState evm I).executionEnv.codeOwner burnTotalSupplySlot
    (burnSupplyDebitWord (burnAfterUsrDebitState evm I) I)

abbrev burnUsrBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (burnUsrKey I)] }

abbrev burnAllowanceRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps := [.mindex (burnUsrKey I), .mindex (burnSpenderKey evm)] }

abbrev burnTotalSupplyRef : EvaledStorageRef :=
  { base := "totalSupply", steps := [] }

theorem burnStore_get_usr (I : ExecutionEnv) :
    (burnStore I).get? "usr" = some (burnUsrValue I) := by
  unfold burnStore
  rw [store_get_ne
    (L := (∅ : Store).insert "usr" (burnUsrValue I))
    (k := "wad") (a := "usr") (burnWadValue I) (by native_decide)]
  simp

theorem burnStore_get_wad (I : ExecutionEnv) :
    (burnStore I).get? "wad" = some (burnWadValue I) := by
  unfold burnStore
  simp

theorem burnStore_balanceOf (I : ExecutionEnv) :
    (burnStore I).get? "balanceOf" = none := by
  unfold burnStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem burnStore_allowance (I : ExecutionEnv) :
    (burnStore I).get? "allowance" = none := by
  unfold burnStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem burnStore_totalSupply (I : ExecutionEnv) :
    (burnStore I).get? "totalSupply" = none := by
  unfold burnStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem burnStore_index_usr (I : ExecutionEnv) :
    (burnStore I)["usr"] = burnUsrValue I := by
  unfold burnStore
  simp [Std.HashMap.getElem_insert]

theorem burnUsrSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    burnUsrSlot I = mapSlot (burnUsrMaskedWord I) ⟨2⟩ := by
  unfold burnUsrSlot balanceOfSlot burnUsrKey burnUsrMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem burnAllowanceSlot_eq_mapSlot_masked (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source) :
    burnAllowanceSlot evm I = mapSlot (solcSourceWord I) (mapSlot (burnUsrMaskedWord I) ⟨3⟩) := by
  unfold burnAllowanceSlot allowanceSlot allowanceOwnerSlot burnUsrKey burnSpenderKey
    burnUsrMaskedWord solcSourceWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]
  simp [hsource]

theorem burnUsrMaskedWord_canonical (I : ExecutionEnv) :
    (burnUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold burnUsrMaskedWord
  rw [u256_land_comm solcAddrMask (burnUsrWord I)]
  exact solcAddrMask_result_canonical (burnUsrWord I)

noncomputable abbrev burnUsrHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ solcFreePtrMem

noncomputable abbrev burnAllowanceHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (burnUsrMaskedWord I) I (burnUsrHashMem I)

noncomputable abbrev burnAllowanceReloadHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (burnUsrMaskedWord I) I (burnAllowanceHashMem I)

noncomputable abbrev burnAllowanceStoreHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceReloadHashMem I)

noncomputable abbrev burnAllowancePostStoreHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceStoreHashMem I)

noncomputable abbrev burnTailUsrStoreMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩
    (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem)

noncomputable abbrev burnTailLogMem (mem : ByteArray) (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (burnTailUsrStoreMem mem I) (burnWadWord I)

abbrev burnEvmUsrSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (burnUsrMaskedWord I) ⟨2⟩

abbrev burnEvmAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (solcSourceWord I) (mapSlot (burnUsrMaskedWord I) ⟨3⟩)

abbrev burnEvmTailUsrBalanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (burnEvmUsrSlot I)

abbrev burnEvmAllowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (burnEvmAllowanceSlot I)

abbrev burnEvmAllowanceDebitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (burnEvmAllowanceWord σ I) (burnWadWord I)

abbrev burnEvmAfterAllowanceAccountMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (burnEvmAllowanceSlot I)
    (burnEvmAllowanceDebitWord σ I)

abbrev burnEvmTailUsrDebitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (burnEvmTailUsrBalanceWord σ I) (burnWadWord I)

abbrev burnEvmTailAfterUsrAccountMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (burnEvmUsrSlot I) (burnEvmTailUsrDebitWord σ I)

abbrev burnEvmTailSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord (burnEvmTailAfterUsrAccountMap σ I) I burnTotalSupplySlot

abbrev burnEvmTailSupplyDebitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (burnEvmTailSupplyWord σ I) (burnWadWord I)

abbrev burnEvmTailPostAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (burnEvmTailAfterUsrAccountMap σ I) burnTotalSupplySlot
    (burnEvmTailSupplyDebitWord σ I)

theorem burnUsrHashMem_size (I : ExecutionEnv) :
    (burnUsrHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩ solcFreePtrMem_size

theorem burnUsrHashMem_read64 (I : ExecutionEnv) :
    (burnUsrHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (burnUsrMaskedWord I) ⟨2⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem burnAllowanceHashMem_size (I : ExecutionEnv) :
    (burnAllowanceHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnUsrHashMem_size I)

theorem burnAllowanceHashMem_read64 (I : ExecutionEnv) :
    (burnAllowanceHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnUsrHashMem_size I) (burnUsrHashMem_read64 I)

theorem burnAllowanceReloadHashMem_size (I : ExecutionEnv) :
    (burnAllowanceReloadHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceHashMem_size I)

theorem burnAllowanceReloadHashMem_read64 (I : ExecutionEnv) :
    (burnAllowanceReloadHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceHashMem_size I) (burnAllowanceHashMem_read64 I)

theorem burnAllowanceStoreHashMem_size (I : ExecutionEnv) :
    (burnAllowanceStoreHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceReloadHashMem_size I)

theorem burnAllowanceStoreHashMem_read64 (I : ExecutionEnv) :
    (burnAllowanceStoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceReloadHashMem_size I) (burnAllowanceReloadHashMem_read64 I)

theorem burnAllowancePostStoreHashMem_size (I : ExecutionEnv) :
    (burnAllowancePostStoreHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceStoreHashMem_size I)

theorem burnAllowancePostStoreHashMem_read64 (I : ExecutionEnv) :
    (burnAllowancePostStoreHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (burnUsrMaskedWord I) I
    (burnAllowanceStoreHashMem_size I) (burnAllowanceStoreHashMem_read64 I)

theorem burnTailUsrStoreMem_size {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96) :
    (burnTailUsrStoreMem mem I).size = 96 := by
  exact twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩
    (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩ hmem)

theorem burnTailUsrStoreMem_read64 {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (burnTailUsrStoreMem mem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (burnUsrMaskedWord I) ⟨2⟩
    (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩ hmem)
    (twoWordHashMem_read64 (burnUsrMaskedWord I) ⟨2⟩ hmem hread64)

theorem burnTailLogMem_mload64 {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnTailLogMem mem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((burnTailLogMem mem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 (burnWadWord I)
    (burnTailUsrStoreMem_size I hmem)
    (burnTailUsrStoreMem_read64 I hmem hread64)

theorem daiBurnX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨946⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3336⟩
        [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd968⟩ := RD.daiAddressUint256ExternalLenOk
    (entry := ⟨946⟩) (ret := ⟨686⟩) (routine := ⟨3336⟩) hreach
    dai_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd3336⟩ := RD.daiAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨946⟩) (ret := ⟨686⟩) (routine := ⟨3336⟩) (R := [sel])
    rd968 dai_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [burnWadWord, burnUsrMaskedWord, burnUsrWord, calldataWord] using rd3336⟩

theorem daiBurnX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨946⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressUint256ExternalShort
    (entry := ⟨946⟩) (ret := ⟨686⟩) (routine := ⟨3336⟩)
    hreach dai_address_uint256_external_entry_wf hsz4 hsize hshort

set_option maxHeartbeats 4000000 in
theorem daiBurnX_initialBalanceOkCont {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (henough :
      (burnWadWord I).toNat ≤ (solcSlotWord σ I (burnEvmUsrSlot I)).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3336⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnUsrHashMem I).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnUsrHashMem, burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I)
        solcFreePtrMem_size
  have hmaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (burnUsrHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [burnEvmTailUsrBalanceWord, burnEvmUsrSlot, solcSlotWord] using rdLoadedRaw
  have hgt :
      UInt256.gt (burnWadWord I) (solcSlotWord σ I (burnEvmUsrSlot I)) = ⟨0⟩ :=
    ugt_zero henough
  have rdGt := evm_run rdLoaded with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdIszero := evm_run rdGt with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdIszero
  have rdPush := evm_run rdIszero with [raw push2 ⟨3440⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_initialBalanceOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (henough :
      (burnWadWord I).toNat ≤ (solcSlotWord σ I (burnEvmUsrSlot I)).toNat)
    (h : RD daiBytecode I g s0 ⟨3336⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiBurnX_initialBalanceOkCont (I := I) (ret := ⟨686⟩) (S := [sel])
    henough (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 4000000 in
theorem daiBurnX_initialBalanceRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hlt : (solcSlotWord σ I (burnEvmUsrSlot I)).toNat < (burnWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3336⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnUsrHashMem I).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnUsrHashMem, burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I)
        solcFreePtrMem_size
  have hmaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (burnUsrHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [burnEvmTailUsrBalanceWord, burnEvmUsrSlot, solcSlotWord] using rdLoadedRaw
  have hgt :
      UInt256.gt (burnWadWord I) (solcSlotWord σ I (burnEvmUsrSlot I)) = ⟨1⟩ :=
    ugt_one hlt
  have rdGt := evm_run rdLoaded with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdIszero := evm_run rdGt with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdIszero
  have rdPush := evm_run rdIszero with [raw push2 ⟨3440⟩ (by native_decide) (by evm_ov)]
  have rdTail := rdPush.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3369⟩)
    (len := ⟨24⟩)
    (rawWord := ⟨0x4461692f696e73756666696369656e742d62616c616e6365⟩)
    (shift := ⟨64⟩)
    (word := ⟨0x4461692f696e73756666696369656e742d62616c616e63650000000000000000⟩)
    (op := .PUSH24)
    (width := 24)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    transferFromInsufficientBalanceWord
    (burnUsrHashMem_size I)
    (burnUsrHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_initialBalanceRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hlt : (solcSlotWord σ I (burnEvmUsrSlot I)).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3336⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiBurnX_initialBalanceRevertCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hlt (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

theorem burnUsrMaskedWord_eq_solcSourceWord_of_address_eq (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (burnUsrWord I).toNat = I.source) :
    burnUsrMaskedWord I = solcSourceWord I := by
  have hmask := keyValueToWord_address_ofNat_mask (burnUsrWord I)
  rw [heq, keyValueToWord_address] at hmask
  exact hmask.symm

theorem burn_address_eq_of_usrMaskedWord_eq (I : ExecutionEnv)
    (heq : burnUsrMaskedWord I = solcSourceWord I) :
    AccountAddress.ofNat (burnUsrWord I).toNat = I.source := by
  have hmaskAddr :
      AccountAddress.ofNat (burnUsrWord I).toNat =
        AccountAddress.ofNat (UInt256.land (burnUsrWord I) solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change (burnUsrWord I).val.val % AccountAddress.size =
      Nat.land (burnUsrWord I).val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hmasked :
      AccountAddress.ofNat (UInt256.land (burnUsrWord I) solcAddrMask).toNat = I.source := by
    apply solcMaskedAddress_eq_source_of_word_eq
    rw [u256_land_comm]
    simpa [burnUsrMaskedWord] using heq
  exact hmaskAddr.trans hmasked

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSkipSenderCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (heq : burnUsrMaskedWord I = solcSourceWord I)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have heqWord :
      UInt256.eq (solcSourceWord I) (burnUsrMaskedWord I) = ⟨1⟩ := by
    rw [heq]
    exact u256_eq_refl (solcSourceWord I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdMasked
  have rdEq := evm_run rdMasked with [
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [heqWord] at rdEq
  have rdCond := evm_run rdEq with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3502⟩ (by native_decide) (by evm_ov)]
  have rd3502 := rdCond.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rdNeedFalse := evm_run rd3502 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by native_decide]
    at rdNeedFalse
  have rdPush := evm_run rdNeedFalse with [raw push2 ⟨3710⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSkipSender {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (heq : burnUsrMaskedWord I = solcSourceWord I)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiBurnX_allowanceSkipSenderCont (I := I) (ret := ⟨686⟩) (S := [sel])
    heq (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceLoadedCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3502⟩
      ((UInt256.isZero (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256))
          (burnEvmAllowanceWord σ I)))
        :: burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have heqZero :
      UInt256.eq (solcSourceWord I) (burnUsrMaskedWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hne hbad.symm)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdMasked
  have rdEq := evm_run rdMasked with [
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [heqZero] at rdEq
  have rdCond := evm_run rdEq with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3502⟩ (by native_decide) (by evm_ov)]
  have rdFall := rdCond.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoadStart := evm_run rdFall with [raw pop (by native_decide) (by evm_ov)]
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
            (burnUsrHashMem I)).readWithPadding 0 64))) =
        mapSlot (burnUsrMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (burnUsrMaskedWord I)
        (burnUsrHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnAllowanceHashMem I).readWithPadding 0 64))) =
        burnEvmAllowanceSlot I := by
    unfold burnAllowanceHashMem solcNestedMappingCallerHashMem
    simpa [burnEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (burnUsrMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨3⟩
          (burnUsrHashMem_size I))
  have rdLoadMasked := evm_run rdLoadStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdLoadMasked
  have rdInnerKeyPrefix := evm_run rdLoadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) (burnUsrHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnUsrHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (mapSlot (burnUsrMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnUsrHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (burnAllowanceHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (burnEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [burnEvmAllowanceWord, burnEvmAllowanceSlot] using rdLoadedRaw
  have rdMaxCheck := evm_run rdLoaded with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [UInt256.lnot] using rdMaxCheck⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceLoaded {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3502⟩
      [UInt256.isZero (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256))
          (burnEvmAllowanceWord σ I)),
        burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiBurnX_allowanceLoadedCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hne (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSkipMaxCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hmax : (burnEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiBurnX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hword : burnEvmAllowanceWord σ I = UInt256.lnot (⟨0⟩ : UInt256) := by
    apply u256_inj
    rw [hmax, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (burnEvmAllowanceWord σ I) = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl (UInt256.lnot (⟨0⟩ : UInt256))
  rw [heqMax] at rdLoaded
  have rdNeedFalse := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by native_decide]
    at rdNeedFalse
  have rdPush := evm_run rdNeedFalse with [raw push2 ⟨3710⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSkipMax {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hmax : (burnEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiBurnX_allowanceSkipMaxCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hne hmax (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSpendCheckOkCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3627⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnAllowanceReloadHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiBurnX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ burnEvmAllowanceWord σ I := by
    intro hword
    apply hnotMax
    rw [← hword, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (burnEvmAllowanceWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hneq
  rw [heqMax] at rdLoaded
  have rdNeedTrue := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ from by native_decide]
    at rdNeedTrue
  have rdPushSkip := evm_run rdNeedTrue with [raw push2 ⟨3710⟩ (by native_decide) (by evm_ov)]
  have rdCheckStart := rdPushSkip.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
            (burnAllowanceHashMem I)).readWithPadding 0 64))) =
        mapSlot (burnUsrMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (burnUsrMaskedWord I)
        (burnAllowanceHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnAllowanceReloadHashMem I).readWithPadding 0 64))) =
        burnEvmAllowanceSlot I := by
    unfold burnAllowanceReloadHashMem solcNestedMappingCallerHashMem
    simpa [burnEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (burnUsrMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨3⟩
          (burnAllowanceHashMem_size I))
  have rdReloadMasked := evm_run rdCheckStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) (burnAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (mapSlot (burnUsrMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnAllowanceHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (burnAllowanceReloadHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (burnEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [burnEvmAllowanceWord, burnEvmAllowanceSlot] using rdReloadedRaw
  have hgt :
      UInt256.gt (burnWadWord I) (burnEvmAllowanceWord σ I) = ⟨0⟩ :=
    ugt_zero hallowEnough
  have rdGt := evm_run rdReloaded with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdOk := evm_run rdGt with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3627⟩ (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rdOk
  exact ⟨_, _, rdOk.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceSpendCheckOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3627⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnAllowanceReloadHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiBurnX_allowanceSpendCheckOkCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hne hnotMax hallowEnough (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_insufficientAllowanceTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3551⟩ stk mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨26⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨26⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst transferFromInsufficientAllowanceWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨26⟩ transferFromInsufficientAllowanceWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨26⟩ transferFromInsufficientAllowanceWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hlt : (burnEvmAllowanceWord σ I).toNat < (burnWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiBurnX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ burnEvmAllowanceWord σ I := by
    intro hword
    apply hnotMax
    rw [← hword, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (burnEvmAllowanceWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hneq
  rw [heqMax] at rdLoaded
  have rdNeedTrue := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ from by native_decide]
    at rdNeedTrue
  have rdPushSkip := evm_run rdNeedTrue with [raw push2 ⟨3710⟩ (by native_decide) (by evm_ov)]
  have rdCheckStart := rdPushSkip.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
            (burnAllowanceHashMem I)).readWithPadding 0 64))) =
        mapSlot (burnUsrMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (burnUsrMaskedWord I)
        (burnAllowanceHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnAllowanceReloadHashMem I).readWithPadding 0 64))) =
        burnEvmAllowanceSlot I := by
    unfold burnAllowanceReloadHashMem solcNestedMappingCallerHashMem
    simpa [burnEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (burnUsrMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨3⟩
          (burnAllowanceHashMem_size I))
  have rdReloadMasked := evm_run rdCheckStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) (burnAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (mapSlot (burnUsrMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩ (burnAllowanceHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (burnAllowanceReloadHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (burnEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [burnEvmAllowanceWord, burnEvmAllowanceSlot] using rdReloadedRaw
  have hgt :
      UInt256.gt (burnWadWord I) (burnEvmAllowanceWord σ I) = ⟨1⟩ :=
    ugt_one hlt
  have rdGt := evm_run rdReloaded with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdFail := evm_run rdGt with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3627⟩ (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rdFail
  have rdTail := rdFail.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact daiBurnX_insufficientAllowanceTail
    (I := I) (σ := σ)
    (burnAllowanceReloadHashMem_size I)
    (burnAllowanceReloadHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)
    rdTail

set_option maxHeartbeats 1000000 in
theorem daiBurnX_allowanceRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hlt : (burnEvmAllowanceWord σ I).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiBurnX_allowanceRevertCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hne hnotMax hlt (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_spendToTailCont {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnAllowancePostStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmAfterAllowanceAccountMap σ I) k' C' := by
  obtain ⟨_, _, rd3627⟩ :=
    daiBurnX_allowanceSpendCheckOkCont (I := I) (ret := ret) (S := S)
      hne hnotMax hallowEnough hSlen h
  have rd3628 := evm_run rd3627 with [raw jumpdest (by native_decide) (by evm_ov)]
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
            (burnAllowanceReloadHashMem I)).readWithPadding 0 64))) =
        mapSlot (burnUsrMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (burnUsrMaskedWord I)
        (burnAllowanceReloadHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnAllowanceStoreHashMem I).readWithPadding 0 64))) =
        burnEvmAllowanceSlot I := by
    unfold burnAllowanceStoreHashMem solcNestedMappingCallerHashMem
    simpa [burnEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (burnUsrMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨3⟩
          (burnAllowanceReloadHashMem_size I))
  have rdReloadMasked := evm_run rd3628 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) (burnAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
      (burnAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (mapSlot (burnUsrMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
        (burnAllowanceReloadHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (burnAllowanceStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (burnEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [burnEvmAllowanceWord, burnEvmAllowanceSlot] using rdReloadedRaw
  have rdRoutineRaw := evm_run rdReloaded with [
    raw push2 ⟨3673⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rdRoutine := by
    simpa [burnEvmAllowanceWord, burnEvmAllowanceSlot, mapSlot, solcMappingSlot]
      using rdRoutineRaw
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := burnEvmAllowanceWord σ I) (b := burnWadWord I)
    (ret := ⟨3673⟩)
    (R := burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
    rdRoutine hsubWf hallowEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSub := by
    simpa [burnEvmAllowanceDebitWord] using rdAfterSubRaw
  have hinnerStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
            (burnAllowanceStoreHashMem I)).readWithPadding 0 64))) =
        mapSlot (burnUsrMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (burnUsrMaskedWord I)
        (burnAllowanceStoreHashMem_size I)
  have houterStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnAllowancePostStoreHashMem I).readWithPadding 0 64))) =
        burnEvmAllowanceSlot I := by
    unfold burnAllowancePostStoreHashMem solcNestedMappingCallerHashMem
    simpa [burnEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (burnUsrMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨3⟩
          (burnAllowanceStoreHashMem_size I))
  have rdStoreMasked := evm_run rdAfterSub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdStoreMasked
  have rdStoreInnerKeyPrefix := evm_run rdStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdStoreInnerKey := rdStoreInnerKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I) (burnAllowanceStoreHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdStoreInnerMemPrefix := evm_run rdStoreInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdStoreInnerMem := rdStoreInnerMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
      (burnAllowanceStoreHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdStoreInnerHashPrefix := evm_run rdStoreInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdStoreInnerHash := rdStoreInnerHashPrefix.keccak256 0
    (mapSlot (burnUsrMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerStoreSlot
    (by native_decide) (by evm_ov)
  have rdStoreCaller := evm_run rdStoreInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdStoreOuterKey := rdStoreCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨3⟩
        (burnAllowanceStoreHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdStoreOuterMemPrefix := evm_run rdStoreOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdStoreOuterMem := rdStoreOuterMemPrefix.mstore 0 (burnAllowancePostStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdStoreOuterHashPrefix := evm_run rdStoreOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdStoreOuterHash := rdStoreOuterHashPrefix.keccak256 0 (burnEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterStoreSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3710Raw⟩ := rdStoreOuterHash.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [burnEvmAfterAllowanceAccountMap, burnEvmAllowanceDebitWord,
      burnEvmAllowanceSlot, burnAllowancePostStoreHashMem, mapSlot, solcMappingSlot]
      using rd3710Raw⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_spendToTail {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hne : burnUsrMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (burnEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨3440⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnUsrHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      (burnAllowancePostStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmAfterAllowanceAccountMap σ I) k' C' := by
  exact daiBurnX_spendToTailCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hperm hne hnotMax hallowEnough
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

theorem daiBurnX_logAndJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256} {scratch rdata : ByteArray}
    (hperm : I.perm = true)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 10 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨3787⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      scratch (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret S
      (solcScratchReturnMem scratch (burnWadWord I)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  have husrMask :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ scratch.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((scratch.readWithPadding (⟨64⟩ : UInt256).toNat 32))))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hscratch]; decide) (by decide) hread64
  have rd3791 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd3793pre := evm_run rd3791 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3794 := rd3793pre.mstore 6 (solcScratchReturnMem scratch (burnWadWord I))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3809pre := evm_run rd3794 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcScratchReturnMem_mload64 (burnWadWord I) hscratch hread64)
      (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMask] at rd3809pre
  have rd3810 := evm_run rd3809pre with [raw swap2 (by native_decide) (by evm_ov)]
  have rd3843 := rd3810.pushConst transferFromTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd3851pre := evm_run rd3843 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3852 := rd3851pre.log3 0 (UInt256.ofNat 5) (by native_decide) hperm
    mem_cost (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRet := evm_run rd3852 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) hretDest (by evm_ov)]
  exact ⟨_, _, rdRet⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailSuccessJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailSupplyWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret S
      (burnTailLogMem mem I) (UInt256.ofNat 5) rdata
      (cA, burnEvmTailPostAccountMap σ I) k' C' := by
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hUsrSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I) hmem
  have rdUsrMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdUsrMasked
  have rdUsrKeyPrefix := evm_run rdUsrMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdUsrKey := rdUsrKeyPrefix.mstore 0 (wordAt0Mem (burnUsrMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrMemPrefix := evm_run rdUsrKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdUsrHashMem := rdUsrMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrHashPrefix := evm_run rdUsrHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdUsrSlot := rdUsrHashPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdUsrLoadedRaw⟩ := rdUsrSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdUsrLoaded := by
    simpa [burnEvmTailUsrBalanceWord, burnEvmUsrSlot] using rdUsrLoadedRaw
  have rdUsrSubRoutinePre := evm_run rdUsrLoaded with [
    raw push2 ⟨3745⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdUsrSubRoutine := rdUsrSubRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterUsrSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := burnEvmTailUsrBalanceWord σ I) (b := burnWadWord I)
    (ret := ⟨3745⟩)
    (R := burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
    rdUsrSubRoutine hsubWf husrEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterUsrSub := by
    simpa [burnEvmTailUsrDebitWord] using rdAfterUsrSubRaw
  have hUsrStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnTailUsrStoreMem mem I).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnTailUsrStoreMem, burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩ hmem)
  have rdUsrStoreMasked := evm_run rdAfterUsrSub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdUsrStoreMasked
  have rdUsrStoreKeyPrefix := evm_run rdUsrStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdUsrStoreKey := rdUsrStoreKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrStoreMemPrefix := evm_run rdUsrStoreKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdUsrStoreMem := rdUsrStoreMemPrefix.mstore 0 (burnTailUsrStoreMem mem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrStoreHashPrefix := evm_run rdUsrStoreMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdUsrStoreSlot := rdUsrStoreHashPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrStoreSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdAfterUsrStoreRaw⟩ := rdUsrStoreSlot.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterUsrStore := by
    simpa [burnEvmTailAfterUsrAccountMap, burnEvmTailUsrDebitWord, burnEvmUsrSlot]
      using rdAfterUsrStoreRaw
  have rdSupplyLoadedPre := evm_run rdAfterUsrStore with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdSupplyLoadedRaw⟩ := rdSupplyLoadedPre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSupplyLoaded := by
    simpa [burnEvmTailSupplyWord, burnTotalSupplySlot, solcSlotWord] using rdSupplyLoadedRaw
  have rdSupplySubRoutinePre := evm_run rdSupplyLoaded with [
    raw push2 ⟨3783⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdSupplySubRoutine := rdSupplySubRoutinePre.jump (by native_decide)
    (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rdAfterSupplySubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := burnEvmTailSupplyWord σ I) (b := burnWadWord I)
    (ret := ⟨3783⟩)
    (R := burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
    rdSupplySubRoutine hsubWf hsupplyEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSupplySub := by
    simpa [burnEvmTailSupplyDebitWord] using rdAfterSupplySubRaw
  have rdSupplyStorePre := evm_run rdAfterSupplySub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterSupplyStoreRaw⟩ := rdSupplyStorePre.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSupplyStore := by
    simpa [burnEvmTailPostAccountMap, burnEvmTailSupplyDebitWord, burnTotalSupplySlot]
      using rdAfterSupplyStoreRaw
  exact daiBurnX_logAndJump (I := I) (ret := ret) (S := S)
    (scratch := burnTailUsrStoreMem mem I)
    hperm (burnTailUsrStoreMem_size I hmem)
    (burnTailUsrStoreMem_read64 I hmem hread64)
    (by omega) hretDest rdAfterSupplyStore

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailSupplyWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, burnEvmTailPostAccountMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd686⟩ := daiBurnX_tailSuccessJump
    (I := I) (ret := ⟨686⟩) (S := [sel])
    hperm hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) husrEnough hsupplyEnough (by simpa using h)
  have rd687 := rd686.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd687 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailUsrDebitRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hSlen : S.length + 16 ≤ 1024)
    (hlt :
      (burnEvmTailUsrBalanceWord σ I).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hUsrSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I) hmem
  have rdUsrMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdUsrMasked
  have rdUsrKeyPrefix := evm_run rdUsrMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdUsrKey := rdUsrKeyPrefix.mstore 0 (wordAt0Mem (burnUsrMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdUsrMemPrefix := evm_run rdUsrKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdUsrHashMem := rdUsrMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrHashPrefix := evm_run rdUsrHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdUsrSlot := rdUsrHashPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdUsrLoadedRaw⟩ := rdUsrSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdUsrLoaded := by
    simpa [burnEvmTailUsrBalanceWord, burnEvmUsrSlot] using rdUsrLoadedRaw
  have rdUsrSubRoutinePre := evm_run rdUsrLoaded with [
    raw push2 ⟨3745⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdUsrSubRoutine := rdUsrSubRoutinePre.jump (by native_decide) (by jump_dest)
    (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  rcases hsubWf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat :
      (UInt256.sub (burnEvmTailUsrBalanceWord σ I) (burnWadWord I)).toNat =
        UInt256.size + (burnEvmTailUsrBalanceWord σ I).toNat -
          (burnWadWord I).toNat :=
    usub_toNat_underflow hlt
  have hgt :
      UInt256.gt
          (UInt256.sub (burnEvmTailUsrBalanceWord σ I) (burnWadWord I))
          (burnEvmTailUsrBalanceWord σ I) =
        ⟨1⟩ := by
    show UInt256.fromBool
        (decide
          (UInt256.sub (burnEvmTailUsrBalanceWord σ I) (burnWadWord I) >
            burnEvmTailUsrBalanceWord σ I)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub (burnEvmTailUsrBalanceWord σ I) (burnWadWord I)).toNat >
          (burnEvmTailUsrBalanceWord σ I).toNat
      rw [hsubNat]
      have hb : (burnWadWord I).toNat < UInt256.size := (burnWadWord I).val.isLt
      omega
  have rd6 := evm_run rdUsrSubRoutine with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  rw [hgt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨1399⟩ hd8 (by evm_ov)]
  have rdTail := rdPush.jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdTail
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailUsrDebitRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hlt :
      (burnEvmTailUsrBalanceWord σ I).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiBurnX_tailUsrDebitRevertCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hmem (by simp only [List.length_cons, List.length_nil]; omega) hlt (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailAfterUsrStoreCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hSlen : S.length + 16 ≤ 1024)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3771⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      (burnTailUsrStoreMem mem I) (UInt256.ofNat 3) rdata
      (cA, burnEvmTailAfterUsrAccountMap σ I) k' C' := by
  have husrMaskLiteral :
      UInt256.land (burnUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        burnUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (burnUsrMaskedWord_canonical I)
  have hUsrSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I) hmem
  have rdUsrMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdUsrMasked
  have rdUsrKeyPrefix := evm_run rdUsrMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdUsrKey := rdUsrKeyPrefix.mstore 0 (wordAt0Mem (burnUsrMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdUsrMemPrefix := evm_run rdUsrKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdUsrHashMem := rdUsrMemPrefix.mstore 0
    (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrHashPrefix := evm_run rdUsrHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdUsrSlot := rdUsrHashPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdUsrLoadedRaw⟩ := rdUsrSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdUsrLoaded := by
    simpa [burnEvmTailUsrBalanceWord, burnEvmUsrSlot] using rdUsrLoadedRaw
  have rdUsrSubRoutinePre := evm_run rdUsrLoaded with [
    raw push2 ⟨3745⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdUsrSubRoutine := rdUsrSubRoutinePre.jump (by native_decide)
    (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterUsrSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := burnEvmTailUsrBalanceWord σ I) (b := burnWadWord I)
    (ret := ⟨3745⟩)
    (R := burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
    rdUsrSubRoutine hsubWf husrEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterUsrSub := by
    simpa [burnEvmTailUsrDebitWord] using rdAfterUsrSubRaw
  have hUsrStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnTailUsrStoreMem mem I).readWithPadding 0 64))) =
        burnEvmUsrSlot I := by
    simpa [burnTailUsrStoreMem, burnEvmUsrSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (burnUsrMaskedWord I)
        (twoWordHashMem_size_96 (burnUsrMaskedWord I) ⟨2⟩ hmem)
  have rdUsrStoreMasked := evm_run rdAfterUsrSub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [husrMaskLiteral] at rdUsrStoreMasked
  have rdUsrStoreKeyPrefix := evm_run rdUsrStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdUsrStoreKey := rdUsrStoreKeyPrefix.mstore 0
    (wordAt0Mem (burnUsrMaskedWord I)
      (twoWordHashMem (burnUsrMaskedWord I) ⟨2⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrStoreMemPrefix := evm_run rdUsrStoreKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdUsrStoreMem := rdUsrStoreMemPrefix.mstore 0 (burnTailUsrStoreMem mem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdUsrStoreHashPrefix := evm_run rdUsrStoreMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdUsrStoreSlot := rdUsrStoreHashPrefix.keccak256 0 (burnEvmUsrSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hUsrStoreSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdAfterUsrStoreRaw⟩ := rdUsrStoreSlot.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [burnEvmTailAfterUsrAccountMap, burnEvmTailUsrDebitWord, burnEvmUsrSlot]
      using rdAfterUsrStoreRaw⟩

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailSupplyRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hSlen : S.length + 16 ≤ 1024)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (hltSupply :
      (burnEvmTailSupplyWord σ I).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      (burnWadWord I :: burnUsrMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rdAfterUsrStore⟩ := daiBurnX_tailAfterUsrStoreCont
    (I := I) (ret := ret) (S := S) hperm hmem hSlen husrEnough h
  have rdSupplyLoadedPre := evm_run rdAfterUsrStore with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdSupplyLoadedRaw⟩ := rdSupplyLoadedPre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSupplyLoaded := by
    simpa [burnEvmTailSupplyWord, burnTotalSupplySlot, solcSlotWord] using rdSupplyLoadedRaw
  have rdSupplySubRoutinePre := evm_run rdSupplyLoaded with [
    raw push2 ⟨3783⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdSupplySubRoutine := rdSupplySubRoutinePre.jump (by native_decide)
    (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  rcases hsubWf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat :
      (UInt256.sub (burnEvmTailSupplyWord σ I) (burnWadWord I)).toNat =
        UInt256.size + (burnEvmTailSupplyWord σ I).toNat - (burnWadWord I).toNat :=
    usub_toNat_underflow hltSupply
  have hgt :
      UInt256.gt
          (UInt256.sub (burnEvmTailSupplyWord σ I) (burnWadWord I))
          (burnEvmTailSupplyWord σ I) =
        ⟨1⟩ := by
    show UInt256.fromBool
        (decide
          (UInt256.sub (burnEvmTailSupplyWord σ I) (burnWadWord I) >
            burnEvmTailSupplyWord σ I)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub (burnEvmTailSupplyWord σ I) (burnWadWord I)).toNat >
          (burnEvmTailSupplyWord σ I).toNat
      rw [hsubNat]
      have hb : (burnWadWord I).toNat < UInt256.size := (burnWadWord I).val.isLt
      omega
  have rd6 := evm_run rdSupplySubRoutine with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  rw [hgt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨1399⟩ hd8 (by evm_ov)]
  have rdTail := rdPush.jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdTail
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiBurnX_tailSupplyRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (hltSupply :
      (burnEvmTailSupplyWord σ I).toNat < (burnWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨3710⟩
      [burnWadWord I, burnUsrMaskedWord I, ⟨686⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiBurnX_tailSupplyRevertCont (I := I) (ret := ⟨686⟩) (S := [sel])
    hperm hmem (by simp only [List.length_cons, List.length_nil]; omega)
    husrEnough hltSupply (by simpa using h)

theorem daiDecode_burn_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  simpa [burnStore, burnUsrValue, burnWadValue, burnUsrWord, burnWadWord, calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem daiDecode_burn_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

abbrev burnUsrBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnUsrBalanceWord evm I).toNat)

abbrev burnAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnAllowanceWord evm I).toNat)

abbrev burnTotalSupplyValue (evm : EVM.State) : Value :=
  .int (Int.ofNat (burnTotalSupplyWord evm).toNat)

abbrev burnAllowanceDebitValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnAllowanceDebitWord evm I).toNat)

abbrev burnUsrDebitValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnUsrDebitWord evm I).toNat)

abbrev burnSupplyDebitValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnSupplyDebitWord evm I).toNat)

theorem evalExpr_burn_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.var "wad") = .ok (burnWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnStore_get_wad]

theorem evalExpr_burn_usr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.var "usr") = .ok (burnUsrValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnStore_get_usr]

theorem evalStorageRef_burn_usr_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := burnStore I } evm
      (balanceOfRef (.var "usr")) = .ok (burnUsrBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, burnUsrBalanceRef,
    burnUsrValue, burnUsrKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?, burnStore_index_usr]

theorem evalStorageRef_burn_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := burnStore I } evm
      (allowanceRef (.var "usr") sender) = .ok (burnAllowanceRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, burnAllowanceRef,
    burnUsrValue, burnUsrKey, burnSpenderKey, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?, burnStore_index_usr]

theorem evalStorageRef_burn_totalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := burnStore I } evm
      totalSupplyRef = .ok burnTotalSupplyRef := by
  simp [evalStorageRef, totalSupplyRef, EvalResult.bind, bind, pure]

theorem evalExpr_burn_usr_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.storage (balanceOfRef (.var "usr"))) =
        .ok (burnUsrBalanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := burnStore I })
    (slot := balanceOfRef (.var "usr"))
    (er := burnUsrBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (burnUsrSlot I) (.int uint256Int))
    (value := burnUsrBalanceValue evm I)
    (hbase := by
      simpa [balanceOfRef] using burnStore_balanceOf I)
    (her := evalStorageRef_burn_usr_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, burnUsrKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, burnUsrBalanceWord] using
        storageLocLoad_uint256 evm (burnUsrSlot I))]

theorem evalExpr_burn_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.storage (allowanceRef (.var "usr") sender)) =
        .ok (burnAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := burnStore I })
    (slot := allowanceRef (.var "usr") sender)
    (er := burnAllowanceRef evm I)
    (t := .int uint256Int)
    (loc := wordLoc (burnAllowanceSlot evm I) (.int uint256Int))
    (value := burnAllowanceValue evm I)
    (hbase := by
      simpa [allowanceRef] using burnStore_allowance I)
    (her := evalStorageRef_burn_allowance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, burnUsrKey,
        burnSpenderKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, burnAllowanceWord] using
        storageLocLoad_uint256 evm (burnAllowanceSlot evm I))]

theorem evalExpr_burn_totalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.storage totalSupplyRef) = .ok (burnTotalSupplyValue evm) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := burnStore I })
    (slot := totalSupplyRef)
    (er := burnTotalSupplyRef)
    (t := .int uint256Int)
    (loc := wordLoc burnTotalSupplySlot (.int uint256Int))
    (value := burnTotalSupplyValue evm)
    (hbase := by
      simpa [totalSupplyRef] using burnStore_totalSupply I)
    (her := evalStorageRef_burn_totalSupply evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, burnTotalSupplyWord, burnTotalSupplySlot] using
        storageLocLoad_uint256 evm burnTotalSupplySlot)]

theorem evalExpr_burn_usr_balance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_balance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnUsrBalanceValue, burnWadValue, henough]

theorem evalExpr_burn_usr_balance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (burnUsrBalanceWord evm I).toNat < (burnWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_balance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnUsrBalanceValue, burnWadValue]
  omega

theorem evalExpr_burn_allowance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "usr") sender)) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, henough]

theorem evalExpr_burn_allowance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (burnAllowanceWord evm I).toNat < (burnWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "usr") sender)) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem evalExpr_burn_usr_ne_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ne (.var "usr") sender) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue, burnUsrValue, hne]

theorem evalExpr_burn_usr_ne_sender_false (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (burnUsrWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ne (.var "usr") sender) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue, burnUsrValue, heq]

theorem evalExpr_burn_allowance_ne_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "usr") sender)) (.intLit maxUint256)) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance]
  rw [show evalExpr? config { contract := contract, locals := burnStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnAllowanceValue, maxUint256]
  intro h
  apply hnotMax
  apply Int.ofNat.inj
  have hmaxInt : Int.ofNat (UInt256.size - 1) =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Int) := by
    norm_num [UInt256.size]
  rw [hmaxInt]
  exact h

theorem evalExpr_burn_allowance_ne_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hmax : (burnAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "usr") sender)) (.intLit maxUint256)) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance]
  rw [show evalExpr? config { contract := contract, locals := burnStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnAllowanceValue, maxUint256, UInt256.size,
    hmax]

theorem evalExpr_burn_allowanceNeedsSpend_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (allowanceNeedsSpend (.var "usr") sender) = .ok (.bool true) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_burn_allowance_ne_max_true evm I hnotMax]

theorem evalExpr_burn_allowanceNeedsSpend_false_sender
    (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (burnUsrWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (allowanceNeedsSpend (.var "usr") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_ne_sender_false evm I heq]
  simp only [EvalResult.bind, bind, evalExpr?, pure]

theorem evalExpr_burn_allowanceNeedsSpend_false_max (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (burnAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (allowanceNeedsSpend (.var "usr") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_burn_allowance_ne_max_false evm I hmax]

theorem evalExpr_burn_allowance_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .sub (.storage (allowanceRef (.var "usr") sender)) (.var "wad")) =
        .ok (.int (Int.ofNat (burnAllowanceWord evm I).toNat -
          Int.ofNat (burnWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_burn_usr_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .sub (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (.int (Int.ofNat (burnUsrBalanceWord evm I).toNat -
          Int.ofNat (burnWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_balance, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem evalExpr_burn_supply_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .sub (.storage totalSupplyRef) (.var "wad")) =
        .ok (.int (Int.ofNat (burnTotalSupplyWord evm).toNat -
          Int.ofNat (burnWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_totalSupply, evalExpr_burn_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (sub256 (.storage (allowanceRef (.var "usr") sender)) (.var "wad")) =
        .ok (burnAllowanceDebitValue evm I) := by
  have hsub :
      Int.ofNat (burnAllowanceWord evm I).toNat - Int.ofNat (burnWadWord I).toNat =
        Int.ofNat ((burnAllowanceWord evm I).toNat - (burnWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (burnAllowanceDebitWord evm I).toNat =
      (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat := by
    unfold burnAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (burnAllowanceWord evm I).val.isLt)
  have hltNat :
      (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (burnAllowanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((burnAllowanceWord evm I).toNat - (burnWadWord I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg :
      ¬ (Int.ofNat ((burnAllowanceWord evm I).toNat - (burnWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound :
      ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_burn_allowance_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((burnAllowanceWord evm I).toNat - (burnWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    simp [burnAllowanceDebitValue, htoNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_usr_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (sub256 (.storage (balanceOfRef (.var "usr"))) (.var "wad")) =
        .ok (burnUsrDebitValue evm I) := by
  have hsub :
      Int.ofNat (burnUsrBalanceWord evm I).toNat - Int.ofNat (burnWadWord I).toNat =
        Int.ofNat ((burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (burnUsrDebitWord evm I).toNat =
      (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat := by
    unfold burnUsrDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (burnUsrBalanceWord evm I).val.isLt)
  have hltNat :
      (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (burnUsrBalanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg :
      ¬ (Int.ofNat ((burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound :
      ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_burn_usr_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    simp [burnUsrDebitValue, htoNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_supply_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnTotalSupplyWord evm).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (sub256 (.storage totalSupplyRef) (.var "wad")) =
        .ok (burnSupplyDebitValue evm I) := by
  have hsub :
      Int.ofNat (burnTotalSupplyWord evm).toNat - Int.ofNat (burnWadWord I).toNat =
        Int.ofNat ((burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (burnSupplyDebitWord evm I).toNat =
      (burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat := by
    unfold burnSupplyDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (burnTotalSupplyWord evm).val.isLt)
  have hltNat :
      (burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (burnTotalSupplyWord evm).val.isLt)
  have hlt : ¬ Int.ofNat
        ((burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg :
      ¬ (Int.ofNat ((burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound :
      ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_burn_supply_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    simp [burnSupplyDebitValue, htoNat]

theorem evalExpr_burn_supply_debit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (burnTotalSupplyWord evm).toNat < (burnWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (sub256 (.storage totalSupplyRef) (.var "wad")) = .revert := by
  have hneg :
      Int.ofNat (burnTotalSupplyWord evm).toNat - Int.ofNat (burnWadWord I).toNat < 0 := by
    have hltInt :
        Int.ofNat (burnTotalSupplyWord evm).toNat < Int.ofNat (burnWadWord I).toNat :=
      Int.ofNat_lt.mpr hlt
    omega
  have hnotEnough : ¬ (burnWadWord I).toNat ≤ (burnTotalSupplyWord evm).toNat :=
    Nat.not_le_of_lt hlt
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_burn_supply_sub_raw]
  simp [EvalResult.bind, bind, pure, uint256Int, hneg, hnotEnough]

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_allowance_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .le (sub256 (.storage (allowanceRef (.var "usr") sender)) (.var "wad"))
        (.storage (allowanceRef (.var "usr") sender))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_allowance_debit evm I henough, evalExpr_burn_allowance]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnAllowanceValue, burnAllowanceDebitValue]
  have hdebit : (burnAllowanceDebitWord evm I).toNat =
      (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat := by
    unfold burnAllowanceDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
        lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (burnAllowanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_usr_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .le (sub256 (.storage (balanceOfRef (.var "usr"))) (.var "wad"))
        (.storage (balanceOfRef (.var "usr")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_usr_debit evm I henough, evalExpr_burn_usr_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnUsrBalanceValue, burnUsrDebitValue]
  have hdebit : (burnUsrDebitWord evm I).toNat =
      (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat := by
    unfold burnUsrDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
        lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (burnUsrBalanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_burn_supply_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (burnWadWord I).toNat ≤ (burnTotalSupplyWord evm).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .le (sub256 (.storage totalSupplyRef) (.var "wad"))
        (.storage totalSupplyRef)) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_supply_debit evm I henough, evalExpr_burn_totalSupply]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnTotalSupplyValue, burnSupplyDebitValue]
  have hdebit : (burnSupplyDebitWord evm I).toNat =
      (burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat := by
    unfold burnSupplyDebitWord
    exact ulit_toNat' _ (by
      have hlt : (burnTotalSupplyWord evm).toNat - (burnWadWord I).toNat < 2 ^ 256 :=
        lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (burnTotalSupplyWord evm).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

theorem evalExpr_burn_supply_checkedSub_revert (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (burnTotalSupplyWord evm).toNat < (burnWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.binary .le (sub256 (.storage totalSupplyRef) (.var "wad"))
        (.storage totalSupplyRef)) = .revert := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_burn_supply_debit_revert evm I hlt]
  simp [EvalResult.bind, bind]

theorem burnAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := burnStore I } evm
      .storage (allowanceRef (.var "usr") sender) (burnAllowanceDebitValue evm I) =
        .ok ({ contract := contract, locals := burnStore I }, burnAfterAllowanceState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := allowanceRef (.var "usr") sender)
      (er := burnAllowanceRef evm I)
      (ty := uint256St)
      (loc := wordLoc (burnAllowanceSlot evm I) (.int uint256Int))
      (hbase := by
        simpa [allowanceRef] using burnStore_allowance I)
      (her := evalStorageRef_burn_allowance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, burnUsrKey,
          burnSpenderKey, uint256St])
      (hloc := by rfl)
  rw [show wordLoc (burnAllowanceSlot evm I) (ElemType.int uint256Int) =
    uint256Loc (burnAllowanceSlot evm I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem burnAssignUsr (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := burnStore I } evm
      .storage (balanceOfRef (.var "usr")) (burnUsrDebitValue evm I) =
        .ok ({ contract := contract, locals := burnStore I }, burnAfterUsrDebitState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "usr"))
      (er := burnUsrBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (burnUsrSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using burnStore_balanceOf I)
      (her := evalStorageRef_burn_usr_balance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, burnUsrKey, uint256St])
      (hloc := by rfl)
  rw [show wordLoc (burnUsrSlot I) (ElemType.int uint256Int) =
    uint256Loc (burnUsrSlot I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem burnAssignSupply (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := burnStore I } evm
      .storage totalSupplyRef (burnSupplyDebitValue evm I) =
        .ok ({ contract := contract, locals := burnStore I },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner burnTotalSupplySlot
            (burnSupplyDebitWord evm I)) := by
  apply assignStorageRef_storage_scalar
      (slot := totalSupplyRef)
      (er := burnTotalSupplyRef)
      (ty := uint256St)
      (loc := wordLoc burnTotalSupplySlot (.int uint256Int))
      (hbase := by
        simpa [totalSupplyRef] using burnStore_totalSupply I)
      (her := evalStorageRef_burn_totalSupply evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  rw [show wordLoc burnTotalSupplySlot (ElemType.int uint256Int) =
    uint256Loc burnTotalSupplySlot by rfl]
  rw [storageLocStore_uint256]

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReturns_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat)
    (husrDebitEnough :
      (burnWadWord I).toNat ≤
        (burnUsrBalanceWord (burnAfterAllowanceState evm I) I).toNat)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤
        (burnTotalSupplyWord (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I)).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body
      (.returned { contract := contract, locals := burnStore I }
        (burnPostState (burnAfterAllowanceState evm I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := burnStore I }
        (burnAfterAllowanceState evm I))
      (evalExpr_burn_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_burn_allowance_debit evm I hallowEnough)
        (burnAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_burn_usr_balance_ge_true (burnAfterAllowanceState evm I) I
          husrDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_burn_usr_checkedSub_true (burnAfterAllowanceState evm I) I
          husrDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_burn_usr_debit (burnAfterAllowanceState evm I) I husrDebitEnough)
        (burnAssignUsr (burnAfterAllowanceState evm I) I)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_burn_supply_checkedSub_true
          (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I) I hsupplyEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_burn_supply_debit
          (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I) I hsupplyEnough)
        (by
          simpa [burnPostState] using
            burnAssignSupply (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I) I)) ?_
    exact ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReturns_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (burnUsrWord I).toNat = evm.executionEnv.source)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤
        (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body
      (.returned { contract := contract, locals := burnStore I } (burnPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := burnStore I } evm)
      (evalExpr_burn_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_checkedSub_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_burn_usr_debit evm I husrEnough) (burnAssignUsr evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burn_supply_checkedSub_true (burnAfterUsrDebitState evm I) I
        hsupplyEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_burn_supply_debit (burnAfterUsrDebitState evm I) I hsupplyEnough)
      (by simpa [burnPostState] using burnAssignSupply (burnAfterUsrDebitState evm I) I)) ?_
  exact ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReturns_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (burnAllowanceWord evm I).toNat = UInt256.size - 1)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤
        (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body
      (.returned { contract := contract, locals := burnStore I } (burnPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := burnStore I } evm)
      (evalExpr_burn_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_checkedSub_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_burn_usr_debit evm I husrEnough) (burnAssignUsr evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burn_supply_checkedSub_true (burnAfterUsrDebitState evm I) I
        hsupplyEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_burn_supply_debit (burnAfterUsrDebitState evm I) I hsupplyEnough)
      (by simpa [burnPostState] using burnAssignSupply (burnAfterUsrDebitState evm I) I)) ?_
  exact ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_initialBalance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (burnUsrBalanceWord evm I).toNat < (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_burn_usr_balance_ge_false evm I hlt))

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hlt : (burnAllowanceWord evm I).toNat < (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (result := .reverted)
      (evalExpr_burn_allowanceNeedsSpend_true evm I hne hnotMax)
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_burn_allowance_ge_false evm I hlt))))

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_usrDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat)
    (hltDebit :
      (burnUsrBalanceWord (burnAfterAllowanceState evm I) I).toNat < (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := burnStore I }
        (burnAfterAllowanceState evm I))
      (evalExpr_burn_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_burn_allowance_debit evm I hallowEnough)
        (burnAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_burn_usr_balance_ge_false (burnAfterAllowanceState evm I) I hltDebit))

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_supply_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (burnAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat)
    (husrDebitEnough :
      (burnWadWord I).toNat ≤
        (burnUsrBalanceWord (burnAfterAllowanceState evm I) I).toNat)
    (hltSupply :
      (burnTotalSupplyWord (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I)).toNat <
        (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := burnStore I }
        (burnAfterAllowanceState evm I))
      (evalExpr_burn_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_burn_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_burn_allowance_debit evm I hallowEnough)
        (burnAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burn_usr_balance_ge_true (burnAfterAllowanceState evm I) I
        husrDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burn_usr_checkedSub_true (burnAfterAllowanceState evm I) I
        husrDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_burn_usr_debit (burnAfterAllowanceState evm I) I husrDebitEnough)
      (burnAssignUsr (burnAfterAllowanceState evm I) I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_burn_supply_checkedSub_revert
        (burnAfterUsrDebitState (burnAfterAllowanceState evm I) I) I hltSupply))

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_supply_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (burnUsrWord I).toNat = evm.executionEnv.source)
    (hltSupply : (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat <
      (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := burnStore I } evm)
      (evalExpr_burn_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_checkedSub_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_burn_usr_debit evm I husrEnough) (burnAssignUsr evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_burn_supply_checkedSub_revert (burnAfterUsrDebitState evm I) I hltSupply))

set_option maxHeartbeats 1000000 in
theorem daiBurnBodyReverts_supply_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (husrEnough : (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (burnUsrWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (burnAllowanceWord evm I).toNat = UInt256.size - 1)
    (hltSupply : (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat <
      (burnWadWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [burnTransition, nonpayable, spendAllowance, debitBalance, checkedSub,
    List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := burnStore I } evm)
      (evalExpr_burn_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_balance_ge_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_burn_usr_checkedSub_true evm I husrEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_burn_usr_debit evm I husrEnough) (burnAssignUsr evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_burn_supply_checkedSub_revert (burnAfterUsrDebitState evm I) I hltSupply))

theorem burnUsrBalanceWord_accountMapEquiv {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    burnEvmTailUsrBalanceWord σ I = burnUsrBalanceWord evm I := by
  have hread :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (burnEvmUsrSlot I)
      (⟨0⟩ : UInt256)
  simpa [burnEvmTailUsrBalanceWord, burnUsrBalanceWord, burnEvmUsrSlot,
    burnUsrSlot_eq_mapSlot_masked, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, solcSlotWord, howner] using hread

theorem burnAllowanceWord_accountMapEquiv {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evm.executionEnv.source = I.source)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    burnEvmAllowanceWord σ I = burnAllowanceWord evm I := by
  have hread :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (burnEvmAllowanceSlot I)
      (⟨0⟩ : UInt256)
  unfold burnAllowanceWord
  rw [show burnAllowanceSlot evm I = burnEvmAllowanceSlot I by
    simpa [burnEvmAllowanceSlot] using
      burnAllowanceSlot_eq_mapSlot_masked evm I hsource]
  simpa [burnEvmAllowanceWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, solcSlotWord, howner] using hread

theorem burnAfterAllowance_accountMapEquiv {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evm.executionEnv.source = I.source)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hallowEnough : (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ I).toNat) :
    accountMapEquiv (burnEvmAfterAllowanceAccountMap σ I)
      (burnAfterAllowanceState evm I).accountMap := by
  have hallowWord :=
    burnAllowanceWord_accountMapEquiv (σ := σ) (evm := evm) (I := I)
      howner hsource hAccounts
  have hallowDebitEq :
      burnEvmAllowanceDebitWord σ I = burnAllowanceDebitWord evm I := by
    apply u256_inj
    unfold burnEvmAllowanceDebitWord burnAllowanceDebitWord
    rw [usub_toNat hallowEnough]
    have hallowEnoughSolm :
        (burnWadWord I).toNat ≤ (burnAllowanceWord evm I).toNat := by
      rw [← hallowWord]
      exact hallowEnough
    have hlt :
        (burnAllowanceWord evm I).toNat - (burnWadWord I).toNat < UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (burnAllowanceWord evm I).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [← hallowWord]
  have hslot :
      burnAllowanceSlot evm I = burnEvmAllowanceSlot I := by
    simpa [burnEvmAllowanceSlot] using
      burnAllowanceSlot_eq_mapSlot_masked evm I hsource
  simpa [burnEvmAfterAllowanceAccountMap, burnAfterAllowanceState, storageStore_accountMap,
    howner, hslot, hallowDebitEq] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (burnEvmAllowanceSlot I)
      (burnEvmAllowanceDebitWord σ I) hAccounts

set_option maxHeartbeats 1000000 in
theorem burnTailSolmPrefixBridge {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat) :
    (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat ∧
    (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat =
      (burnEvmTailSupplyWord σ I).toNat ∧
    accountMapEquiv (burnEvmTailAfterUsrAccountMap σ I)
      (burnAfterUsrDebitState evm I).accountMap := by
  have husrWord :=
    burnUsrBalanceWord_accountMapEquiv (σ := σ) (evm := evm) (I := I)
      howner hAccounts
  have husrEnoughSolm :
      (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat := by
    rw [← husrWord]
    exact husrEnough
  have husrDebitEq :
      burnEvmTailUsrDebitWord σ I = burnUsrDebitWord evm I := by
    apply u256_inj
    unfold burnEvmTailUsrDebitWord burnUsrDebitWord
    rw [usub_toNat husrEnough]
    have hlt :
        (burnUsrBalanceWord evm I).toNat - (burnWadWord I).toNat < UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (burnUsrBalanceWord evm I).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [← husrWord]
  have husrMap :
      accountMapEquiv (burnEvmTailAfterUsrAccountMap σ I)
        (burnAfterUsrDebitState evm I).accountMap := by
    simpa [burnEvmTailAfterUsrAccountMap, burnAfterUsrDebitState, storageStore_accountMap,
      burnEvmUsrSlot, burnUsrSlot_eq_mapSlot_masked, howner, husrDebitEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (burnEvmUsrSlot I)
        (burnEvmTailUsrDebitWord σ I) hAccounts
  have hsupplyWord :
      burnEvmTailSupplyWord σ I = burnTotalSupplyWord (burnAfterUsrDebitState evm I) := by
    have hread :=
      accountMapEquiv_storage_findD husrMap I.codeOwner burnTotalSupplySlot
        (⟨0⟩ : UInt256)
    have hownerAfter :
        (burnAfterUsrDebitState evm I).executionEnv.codeOwner = I.codeOwner := by
      simpa [burnAfterUsrDebit_codeOwner evm I] using howner
    simpa [burnEvmTailSupplyWord, burnTotalSupplyWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, hownerAfter] using hread
  exact ⟨husrEnoughSolm, by rw [← hsupplyWord], husrMap⟩

set_option maxHeartbeats 1000000 in
theorem burnTailSolmBridge {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (husrEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ I).toNat)
    (hsupplyEnough :
      (burnWadWord I).toNat ≤ (burnEvmTailSupplyWord σ I).toNat) :
    (burnWadWord I).toNat ≤ (burnUsrBalanceWord evm I).toNat ∧
    (burnWadWord I).toNat ≤
      (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat ∧
    accountMapEquiv (burnEvmTailPostAccountMap σ I) (burnPostState evm I).accountMap := by
  rcases burnTailSolmPrefixBridge howner hAccounts husrEnough with
    ⟨husrEnoughSolm, hsupplyWordNat, husrMap⟩
  have hsupplyEnoughSolm :
      (burnWadWord I).toNat ≤
        (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat := by
    rw [hsupplyWordNat]
    exact hsupplyEnough
  have hsupplyDebitEq :
      burnEvmTailSupplyDebitWord σ I =
        burnSupplyDebitWord (burnAfterUsrDebitState evm I) I := by
    apply u256_inj
    unfold burnEvmTailSupplyDebitWord burnSupplyDebitWord
    rw [usub_toNat hsupplyEnough]
    have hlt :
        (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).toNat -
            (burnWadWord I).toNat < UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _)
        (burnTotalSupplyWord (burnAfterUsrDebitState evm I)).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [hsupplyWordNat]
  have hownerAfter :
      (burnAfterUsrDebitState evm I).executionEnv.codeOwner = I.codeOwner := by
    simpa [burnAfterUsrDebit_codeOwner evm I] using howner
  have hfinal :
      accountMapEquiv (burnEvmTailPostAccountMap σ I) (burnPostState evm I).accountMap := by
    simpa [burnEvmTailPostAccountMap, burnPostState, storageStore_accountMap,
      hownerAfter, hsupplyDebitEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner burnTotalSupplySlot
        (burnEvmTailSupplyDebitWord σ I) husrMap
  exact ⟨husrEnoughSolm, hsupplyEnoughSolm, hfinal⟩

/-- `burn(address,uint256)` body refines its Solm transition. -/
theorem daiBurnBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 3) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some burnTransition :=
    daiDispatchBurn hsel
  have hreach := daiReachBurnBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiDecode_burn_ok (I := I) hsz68
    obtain ⟨_, _, rd3336⟩ :=
      daiBurnX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerSolm : evmSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm, initState]
    have hsourceSolm : evmSolm.executionEnv.source = I.source := by
      simp [evmSolm, initState]
    have husrWord :
        burnEvmTailUsrBalanceWord σ_evm I = burnUsrBalanceWord evmSolm I :=
      burnUsrBalanceWord_accountMapEquiv (σ := σ_evm) (evm := evmSolm) (I := I)
        hownerSolm hAccounts
    by_cases husrEnough :
        (burnWadWord I).toNat ≤ (burnEvmTailUsrBalanceWord σ_evm I).toNat
    · obtain ⟨_, _, rd3440⟩ := daiBurnX_initialBalanceOk husrEnough rd3336
      have husrEnoughSolm :
          (burnWadWord I).toNat ≤ (burnUsrBalanceWord evmSolm I).toNat := by
        rw [← husrWord]
        exact husrEnough
      by_cases husrIsSender :
          AccountAddress.ofNat (burnUsrWord I).toNat = I.source
      · have heqWord := burnUsrMaskedWord_eq_solcSourceWord_of_address_eq I husrIsSender
        obtain ⟨_, _, rd3710⟩ := daiBurnX_allowanceSkipSender heqWord rd3440
        by_cases hsupplyEnough :
            (burnWadWord I).toNat ≤ (burnEvmTailSupplyWord σ_evm I).toNat
        · rcases burnTailSolmBridge hownerSolm hAccounts husrEnough hsupplyEnough with
            ⟨husrEnoughBody, hsupplyEnoughBody, hfinal⟩
          have hbody :
              ExecTransitionBody config contract evmSolm (burnStore I)
                burnTransition.body
                (.returned { contract := contract, locals := burnStore I }
                  (burnPostState evmSolm I) none) := by
            simpa [evmSolm] using
              daiBurnBodyReturns_skipSender evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                husrEnoughBody
                (by simpa [evmSolm, initState] using husrIsSender)
                hsupplyEnoughBody
          exact (daiBurnX_tailSuccess hperm (burnUsrHashMem_size I)
              (burnUsrHashMem_read64 I) husrEnough hsupplyEnough rd3710)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by
                simp [burnPostState, burnAfterUsrDebitState, evmSolm, initState,
                  storageStore_createdAccounts])
              hfinal
              (by
                simpa [burnTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
        · have hltSupply :
              (burnEvmTailSupplyWord σ_evm I).toNat < (burnWadWord I).toNat := by
            omega
          rcases burnTailSolmPrefixBridge hownerSolm hAccounts husrEnough with
            ⟨husrEnoughBody, hsupplyNat, _⟩
          have hltSupplyBody :
              (burnTotalSupplyWord (burnAfterUsrDebitState evmSolm I)).toNat <
                (burnWadWord I).toNat := by
            rw [hsupplyNat]
            exact hltSupply
          have hbody :
              ExecTransitionBody config contract evmSolm (burnStore I)
                burnTransition.body .reverted := by
            simpa [evmSolm] using
              daiBurnBodyReverts_supply_skipSender evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                husrEnoughBody
                (by simpa [evmSolm, initState] using husrIsSender)
                hltSupplyBody
          exact (daiBurnX_tailSupplyRevert hperm (burnUsrHashMem_size I)
              husrEnough hltSupply rd3710)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hneWord : burnUsrMaskedWord I ≠ solcSourceWord I := by
          intro hbad
          exact husrIsSender (burn_address_eq_of_usrMaskedWord_eq I hbad)
        have hallowWord :=
          burnAllowanceWord_accountMapEquiv (σ := σ_evm) (evm := evmSolm) (I := I)
            hownerSolm hsourceSolm hAccounts
        by_cases hmax :
            (burnEvmAllowanceWord σ_evm I).toNat = UInt256.size - 1
        · have hmaxBody : (burnAllowanceWord evmSolm I).toNat = UInt256.size - 1 := by
            rw [← hallowWord]
            exact hmax
          obtain ⟨_, _, rd3710⟩ := daiBurnX_allowanceSkipMax hneWord hmax rd3440
          by_cases hsupplyEnough :
              (burnWadWord I).toNat ≤ (burnEvmTailSupplyWord σ_evm I).toNat
          · rcases burnTailSolmBridge hownerSolm hAccounts husrEnough hsupplyEnough with
              ⟨husrEnoughBody, hsupplyEnoughBody, hfinal⟩
            have hbody :
                ExecTransitionBody config contract evmSolm (burnStore I)
                  burnTransition.body
                  (.returned { contract := contract, locals := burnStore I }
                    (burnPostState evmSolm I) none) := by
              simpa [evmSolm] using
                daiBurnBodyReturns_skipMax evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  husrEnoughBody
                  (by simpa [evmSolm, initState] using husrIsSender)
                  hmaxBody
                  hsupplyEnoughBody
            exact (daiBurnX_tailSuccess hperm (burnAllowanceHashMem_size I)
                (burnAllowanceHashMem_read64 I) husrEnough hsupplyEnough rd3710)
              |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                (by
                  simp [burnPostState, burnAfterUsrDebitState, evmSolm, initState,
                    storageStore_createdAccounts])
                hfinal
                (by
                  simpa [burnTransition] using
                    (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                      (dvs := []) rfl (by native_decide) (by native_decide)))
          · have hltSupply :
                (burnEvmTailSupplyWord σ_evm I).toNat < (burnWadWord I).toNat := by
              omega
            rcases burnTailSolmPrefixBridge hownerSolm hAccounts husrEnough with
              ⟨husrEnoughBody, hsupplyNat, _⟩
            have hltSupplyBody :
                (burnTotalSupplyWord (burnAfterUsrDebitState evmSolm I)).toNat <
                  (burnWadWord I).toNat := by
              rw [hsupplyNat]
              exact hltSupply
            have hbody :
                ExecTransitionBody config contract evmSolm (burnStore I)
                  burnTransition.body .reverted := by
              simpa [evmSolm] using
                daiBurnBodyReverts_supply_skipMax evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  husrEnoughBody
                  (by simpa [evmSolm, initState] using husrIsSender)
                  hmaxBody
                  hltSupplyBody
            exact (daiBurnX_tailSupplyRevert hperm (burnAllowanceHashMem_size I)
                husrEnough hltSupply rd3710)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · by_cases hallowEnough :
              (burnWadWord I).toNat ≤ (burnEvmAllowanceWord σ_evm I).toNat
          · have hnotMaxBody :
                (burnAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
              rw [← hallowWord]
              exact hmax
            have hallowEnoughBody :
                (burnWadWord I).toNat ≤ (burnAllowanceWord evmSolm I).toNat := by
              rw [← hallowWord]
              exact hallowEnough
            have hallowAcc :=
              burnAfterAllowance_accountMapEquiv
                (σ := σ_evm) (evm := evmSolm) (I := I)
                hownerSolm hsourceSolm hAccounts hallowEnough
            let evmAfterAllowance := burnAfterAllowanceState evmSolm I
            have hownerAfterAllowance :
                evmAfterAllowance.executionEnv.codeOwner = I.codeOwner := by
              simpa [evmAfterAllowance, burnAfterAllowance_codeOwner evmSolm I]
                using hownerSolm
            obtain ⟨_, _, rd3710⟩ :=
              daiBurnX_spendToTail hperm hneWord hmax hallowEnough rd3440
            by_cases husrDebitEnough :
                (burnWadWord I).toNat ≤
                  (burnEvmTailUsrBalanceWord
                    (burnEvmAfterAllowanceAccountMap σ_evm I) I).toNat
            · by_cases hsupplyEnough :
                  (burnWadWord I).toNat ≤
                    (burnEvmTailSupplyWord (burnEvmAfterAllowanceAccountMap σ_evm I)
                      I).toNat
              · rcases burnTailSolmBridge hownerAfterAllowance hallowAcc
                    husrDebitEnough hsupplyEnough with
                  ⟨husrDebitEnoughBody, hsupplyEnoughBody, hfinal⟩
                have hbody :
                    ExecTransitionBody config contract evmSolm (burnStore I)
                      burnTransition.body
                      (.returned { contract := contract, locals := burnStore I }
                        (burnPostState evmAfterAllowance I) none) := by
                  simpa [evmAfterAllowance, evmSolm] using
                    daiBurnBodyReturns_spend evmSolm I
                      (by simp only [evmSolm, initState]; exact hwv)
                      husrEnoughSolm
                      (by simpa [evmSolm, initState] using husrIsSender)
                      hnotMaxBody
                      hallowEnoughBody
                      husrDebitEnoughBody
                      hsupplyEnoughBody
                exact (daiBurnX_tailSuccess hperm (burnAllowancePostStoreHashMem_size I)
                    (burnAllowancePostStoreHashMem_read64 I) husrDebitEnough
                    hsupplyEnough rd3710)
                  |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                    (by
                      simp [burnPostState, burnAfterUsrDebitState, evmAfterAllowance,
                        burnAfterAllowanceState, evmSolm, initState,
                        storageStore_createdAccounts])
                    hfinal
                    (by
                      simpa [burnTransition] using
                        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                          (dvs := []) rfl (by native_decide) (by native_decide)))
              · have hltSupply :
                    (burnEvmTailSupplyWord
                        (burnEvmAfterAllowanceAccountMap σ_evm I) I).toNat <
                      (burnWadWord I).toNat := by
                  omega
                rcases burnTailSolmPrefixBridge hownerAfterAllowance hallowAcc
                    husrDebitEnough with
                  ⟨husrDebitEnoughBody, hsupplyNat, _⟩
                have hltSupplyBody :
                    (burnTotalSupplyWord
                        (burnAfterUsrDebitState evmAfterAllowance I)).toNat <
                      (burnWadWord I).toNat := by
                  rw [hsupplyNat]
                  exact hltSupply
                have hbody :
                    ExecTransitionBody config contract evmSolm (burnStore I)
                      burnTransition.body .reverted := by
                  simpa [evmAfterAllowance, evmSolm] using
                    daiBurnBodyReverts_supply_spend evmSolm I
                      (by simp only [evmSolm, initState]; exact hwv)
                      husrEnoughSolm
                      (by simpa [evmSolm, initState] using husrIsSender)
                      hnotMaxBody
                      hallowEnoughBody
                      husrDebitEnoughBody
                      hltSupplyBody
                exact (daiBurnX_tailSupplyRevert hperm
                    (burnAllowancePostStoreHashMem_size I) husrDebitEnough
                    hltSupply rd3710)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hltDebit :
                (burnEvmTailUsrBalanceWord
                    (burnEvmAfterAllowanceAccountMap σ_evm I) I).toNat <
                  (burnWadWord I).toNat := by
                omega
              have husrAfterWord :
                  burnEvmTailUsrBalanceWord
                      (burnEvmAfterAllowanceAccountMap σ_evm I) I =
                    burnUsrBalanceWord evmAfterAllowance I :=
                burnUsrBalanceWord_accountMapEquiv
                  (σ := burnEvmAfterAllowanceAccountMap σ_evm I)
                  (evm := evmAfterAllowance) (I := I)
                  hownerAfterAllowance hallowAcc
              have hltDebitBody :
                  (burnUsrBalanceWord evmAfterAllowance I).toNat <
                    (burnWadWord I).toNat := by
                rw [← husrAfterWord]
                exact hltDebit
              have hbody :
                  ExecTransitionBody config contract evmSolm (burnStore I)
                    burnTransition.body .reverted := by
                simpa [evmAfterAllowance, evmSolm] using
                  daiBurnBodyReverts_usrDebit evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    husrEnoughSolm
                    (by simpa [evmSolm, initState] using husrIsSender)
                    hnotMaxBody
                    hallowEnoughBody
                    hltDebitBody
              exact (daiBurnX_tailUsrDebitRevert
                  (mem := burnAllowancePostStoreHashMem I)
                  (σ := burnEvmAfterAllowanceAccountMap σ_evm I)
                  (burnAllowancePostStoreHashMem_size I) hltDebit rd3710)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hltAllow :
                (burnEvmAllowanceWord σ_evm I).toNat < (burnWadWord I).toNat := by
              omega
            have hnotMaxBody :
                (burnAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
              rw [← hallowWord]
              exact hmax
            have hltAllowBody :
                (burnAllowanceWord evmSolm I).toNat < (burnWadWord I).toNat := by
              rw [← hallowWord]
              exact hltAllow
            have hbody :
                ExecTransitionBody config contract evmSolm (burnStore I)
                  burnTransition.body .reverted := by
              simpa [evmSolm] using
                daiBurnBodyReverts_allowance evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  husrEnoughSolm
                  (by simpa [evmSolm, initState] using husrIsSender)
                  hnotMaxBody
                  hltAllowBody
            exact (daiBurnX_allowanceRevert hneWord hmax hltAllow rd3440)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hlt :
          (burnEvmTailUsrBalanceWord σ_evm I).toNat < (burnWadWord I).toNat := by
        omega
      have hltBody :
          (burnUsrBalanceWord evmSolm I).toNat < (burnWadWord I).toNat := by
        rw [← husrWord]
        exact hlt
      have hbody :
          ExecTransitionBody config contract evmSolm (burnStore I)
            burnTransition.body .reverted := by
        simpa [evmSolm] using
          daiBurnBodyReverts_initialBalance evmSolm I
            (by simp only [evmSolm, initState]; exact hwv)
            hltBody
      exact (daiBurnX_initialBalanceRevert hlt rd3336)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdec := daiDecode_burn_none_short (I := I) hsz4 (by omega)
    exact (daiBurnX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdec

end Benchmarks.Dss.Dai
