import Examples.BlindAuction.Storage
import Examples.SimpleAuction.Withdraw
import Reasoning.ExternalCall
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `withdraw()` outer body facts -/

abbrev withdrawSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def withdrawSenderKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def withdrawAmountSlot (I : ExecutionEnv) : UInt256 :=
  pendingReturnsSlot (withdrawSenderKey I)

def withdrawAmountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (withdrawAmountSlot I) ⟨0⟩)

def withdrawZeroMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (withdrawAmountSlot I) ⟨0⟩

def withdrawClearedState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (withdrawAmountSlot I) ⟨0⟩

def withdrawZeroState (evm : EVM.State) : EVM.State :=
  withdrawClearedState evm evm.executionEnv

def withdrawAmountStore (amount : UInt256) : Store :=
  (∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))

def withdrawCallStore (amount : UInt256) (success : Bool) (out : ByteArray) : Store :=
  ((withdrawAmountStore amount).insert "success" (.bool success)).insert "_data" (.bytes out)

noncomputable def withdrawBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def withdrawHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (withdrawSourceWord I)).write 0 withdrawBaseSlotMem 0 32

noncomputable def withdrawKeyMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (withdrawSourceWord I)).write 0 solcFreePtrMem 0 32

noncomputable def withdrawLoadHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0 (withdrawKeyMem I) 32 32

noncomputable def withdrawRehashKeyMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (withdrawSourceWord I)).write 0 (withdrawLoadHashMem I) 0 32

noncomputable def withdrawRehashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0 (withdrawRehashKeyMem I) 32 32

theorem withdrawKeyValueToWord_address_source (I : ExecutionEnv) :
    keyValueToWord (withdrawSenderKey I) = withdrawSourceWord I := by
  apply u256_inj
  unfold withdrawSenderKey withdrawSourceWord keyValueToWord UInt256.ofNat
  change I.source.val = (Fin.ofNat UInt256.size I.source.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le I.source.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

theorem withdrawAmountSlot_spec (I : ExecutionEnv) :
    withdrawAmountSlot I = blindAuctionMappingSlot (withdrawSourceWord I) ⟨7⟩ := by
  unfold withdrawAmountSlot pendingReturnsSlot blindAuctionMappingSlot
  rw [withdrawKeyValueToWord_address_source]

theorem withdrawBaseSlotMem_size : withdrawBaseSlotMem.size = 96 := by
  unfold withdrawBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem withdrawHashMem_size (I : ExecutionEnv) : (withdrawHashMem I).size = 96 := by
  unfold withdrawHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawBaseSlotMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, withdrawBaseSlotMem_size, toByteArray_size]
  norm_num

theorem withdrawKeyMem_size (I : ExecutionEnv) : (withdrawKeyMem I).size = 96 := by
  unfold withdrawKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem withdrawLoadHashMem_size (I : ExecutionEnv) : (withdrawLoadHashMem I).size = 96 := by
  unfold withdrawLoadHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, withdrawKeyMem_size, toByteArray_size]
  norm_num

theorem withdrawRehashKeyMem_size (I : ExecutionEnv) : (withdrawRehashKeyMem I).size = 96 := by
  unfold withdrawRehashKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawLoadHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, withdrawLoadHashMem_size, toByteArray_size]
  norm_num

theorem withdrawRehashMem_size (I : ExecutionEnv) : (withdrawRehashMem I).size = 96 := by
  unfold withdrawRehashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawRehashKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, withdrawRehashKeyMem_size, toByteArray_size]
  norm_num

theorem withdrawBaseSlotMem_read32 :
    withdrawBaseSlotMem.readWithPadding 32 32 = UInt256.toByteArray (⟨7⟩ : UInt256) := by
  unfold withdrawBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)]
  rw [show (UInt256.toByteArray (⟨7⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨7⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (⟨7⟩ : UInt256)).data.size ≤ 32
        rw [show (UInt256.toByteArray (⟨7⟩ : UInt256)).data.size =
          (UInt256.toByteArray (⟨7⟩ : UInt256)).size from rfl, toByteArray_size]]

theorem withdrawBaseSlotMem_read64 :
    withdrawBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawBaseSlotMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)
    (by omega)
    (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem withdrawKeyMem_read0 (I : ExecutionEnv) :
    (withdrawKeyMem I).readWithPadding 0 32 =
      UInt256.toByteArray (withdrawSourceWord I) := by
  unfold withdrawKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega)]
  rw [show (UInt256.toByteArray (withdrawSourceWord I)).extract 0 32 =
      UInt256.toByteArray (withdrawSourceWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (withdrawSourceWord I)).data.size ≤ 32
        rw [show (UInt256.toByteArray (withdrawSourceWord I)).data.size =
          (UInt256.toByteArray (withdrawSourceWord I)).size from rfl, toByteArray_size]]

theorem withdrawRehashKeyMem_read0 (I : ExecutionEnv) :
    (withdrawRehashKeyMem I).readWithPadding 0 32 =
      UInt256.toByteArray (withdrawSourceWord I) := by
  unfold withdrawRehashKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [withdrawLoadHashMem_size]; omega)]
  rw [show (UInt256.toByteArray (withdrawSourceWord I)).extract 0 32 =
      UInt256.toByteArray (withdrawSourceWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (withdrawSourceWord I)).data.size ≤ 32
        rw [show (UInt256.toByteArray (withdrawSourceWord I)).data.size =
          (UInt256.toByteArray (withdrawSourceWord I)).size from rfl, toByteArray_size]]

set_option maxHeartbeats 1000000 in
theorem withdrawLoadHashMem_read0_64 (I : ExecutionEnv) :
    (withdrawLoadHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSourceWord I) ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [withdrawLoadHashMem_size]; norm_num)]
  unfold withdrawLoadHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [withdrawKeyMem_size]; omega)]
  let M := withdrawKeyMem I
  let S := UInt256.toByteArray (⟨7⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray (withdrawSourceWord I) ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [SimpleAuction.withdraw_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray (withdrawSourceWord I) := by
      dsimp [M]
      rw [← readWithPadding_eq_extract (withdrawKeyMem I) 0
        (by rw [withdrawKeyMem_size]; omega)]
      exact withdrawKeyMem_read0 I
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨7⟩ : UInt256)).size by rw [toByteArray_size]]
      exact SimpleAuction.withdrawByteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [withdrawKeyMem_size]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

set_option maxHeartbeats 1000000 in
theorem withdrawRehashMem_read0_64 (I : ExecutionEnv) :
    (withdrawRehashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSourceWord I) ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [withdrawRehashMem_size]; norm_num)]
  unfold withdrawRehashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
    (by rw [withdrawRehashKeyMem_size]; omega)]
  let M := withdrawRehashKeyMem I
  let S := UInt256.toByteArray (⟨7⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray (withdrawSourceWord I) ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [SimpleAuction.withdraw_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray (withdrawSourceWord I) := by
      dsimp [M]
      rw [← readWithPadding_eq_extract (withdrawRehashKeyMem I) 0
        (by rw [withdrawRehashKeyMem_size]; omega)]
      exact withdrawRehashKeyMem_read0 I
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨7⟩ : UInt256)).size by rw [toByteArray_size]]
      exact SimpleAuction.withdrawByteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [withdrawRehashKeyMem_size]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

theorem withdrawLoadHashMem_read64 (I : ExecutionEnv) :
    (withdrawLoadHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawLoadHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [withdrawKeyMem_size]; omega)
    (by omega)
    (by rw [withdrawKeyMem_size])]
  unfold withdrawKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)
    (by omega)
    (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem withdrawRehashMem_read64 (I : ExecutionEnv) :
    (withdrawRehashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawRehashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [withdrawRehashKeyMem_size]; omega)
    (by omega)
    (by rw [withdrawRehashKeyMem_size])]
  unfold withdrawRehashKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [withdrawLoadHashMem_size]; omega)
    (by omega)
    (by rw [withdrawLoadHashMem_size])]
  exact withdrawLoadHashMem_read64 I

theorem withdrawLoadHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawLoadHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawLoadHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawLoadHashMem_size]; decide) (by decide)
    (withdrawLoadHashMem_read64 I)

theorem withdrawRehashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawRehashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawRehashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawRehashMem_size]; decide) (by decide)
    (withdrawRehashMem_read64 I)

set_option maxHeartbeats 2000000 in
theorem withdrawHashMem_read0_64 (I : ExecutionEnv) :
    (withdrawHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSourceWord I) ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' (withdrawHashMem I) 0 64
    (by norm_num) (by norm_num) (by rw [withdrawHashMem_size]; omega)]
  unfold withdrawHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawBaseSlotMem_size]; omega)]
  have hempty : withdrawBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    simp
  rw [hempty, empty_append]
  have hfirst :
      ((UInt256.toByteArray (withdrawSourceWord I) ++ withdrawBaseSlotMem.extract 32
          withdrawBaseSlotMem.size).extract 0 64) =
        UInt256.toByteArray (withdrawSourceWord I) ++
          (withdrawBaseSlotMem.extract 32 withdrawBaseSlotMem.size).extract 0 32 := by
    rw [extract_append_span (UInt256.toByteArray (withdrawSourceWord I))
      (withdrawBaseSlotMem.extract 32 withdrawBaseSlotMem.size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
    rw [show (UInt256.toByteArray (withdrawSourceWord I)).extract 0
        (UInt256.toByteArray (withdrawSourceWord I)).size =
        UInt256.toByteArray (withdrawSourceWord I) from by
          apply ByteArray.ext
          rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
          rfl]
    rw [toByteArray_size]
  rw [show (UInt256.toByteArray (withdrawSourceWord I)).extract 0 32 =
      UInt256.toByteArray (withdrawSourceWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (withdrawSourceWord I)).data.size ≤ 32
        rw [show (UInt256.toByteArray (withdrawSourceWord I)).data.size =
          (UInt256.toByteArray (withdrawSourceWord I)).size from rfl, toByteArray_size]]
  simp only [Nat.zero_add]
  rw [hfirst]
  have htail :
      (withdrawBaseSlotMem.extract 32 withdrawBaseSlotMem.size).extract 0 32 =
        UInt256.toByteArray (⟨7⟩ : UInt256) := by
    rw [extract_extract_BA]
    rw [show 32 + 0 = 32 by norm_num]
    rw [show min (32 + 32) withdrawBaseSlotMem.size = 64 by
      rw [withdrawBaseSlotMem_size]; norm_num]
    rw [← readWithPadding_eq_extract withdrawBaseSlotMem 32
      (by rw [withdrawBaseSlotMem_size]; omega)]
    exact withdrawBaseSlotMem_read32
  rw [htail]

theorem withdrawMappingKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((withdrawHashMem I).readWithPadding 0 64)))
      = withdrawAmountSlot I := by
  rw [withdrawHashMem_read0_64, withdrawAmountSlot_spec]
  exact mappingSlot_single (withdrawSourceWord I) ⟨7⟩

theorem withdrawLoadMappingKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((withdrawLoadHashMem I).readWithPadding 0 64)))
      = withdrawAmountSlot I := by
  rw [withdrawLoadHashMem_read0_64, withdrawAmountSlot_spec]
  exact mappingSlot_single (withdrawSourceWord I) ⟨7⟩

theorem withdrawRehashMappingKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((withdrawRehashMem I).readWithPadding 0 64)))
      = withdrawAmountSlot I := by
  rw [withdrawRehashMem_read0_64, withdrawAmountSlot_spec]
  exact mappingSlot_single (withdrawSourceWord I) ⟨7⟩

theorem withdrawStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionUint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0
          (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad blindAuctionUint256Loc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem withdrawPendingReturns_evalStorageRef
    (evm : EVM.State) (locals : Store) :
    evalStorageRef blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (pendingReturnsRef sender) =
    .ok { base := "pendingReturns", steps := [.mindex (withdrawSenderKey evm.executionEnv)] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, pendingReturnsRef, sender,
    evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    withdrawSenderKey]

theorem withdrawPendingReturns_storageType {I : ExecutionEnv} :
    storageTypeAt? blindAuctionContract.storage
      ({ base := "pendingReturns", steps := [.mindex (withdrawSenderKey I)] } : EvaledStorageRef) =
    some uint256St := by
  rfl

theorem withdrawPendingReturns_load (evm : EVM.State) (locals : Store)
    (hbase : locals[(pendingReturnsRef sender).base]? = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage (pendingReturnsRef sender)) =
    .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (withdrawAmountSlot evm.executionEnv)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := withdrawPendingReturns_evalStorageRef evm locals)
    (hty := withdrawPendingReturns_storageType)
    (hloc := blindAuctionConfig_storage_pendingReturns (withdrawSenderKey evm.executionEnv))]
  simpa [withdrawAmountSlot] using
    withdrawStorageLocLoad_uint256 evm (withdrawAmountSlot evm.executionEnv)

theorem withdrawPendingReturns_clear (evm : EVM.State) (locals : Store)
    (hbase : locals[(pendingReturnsRef sender).base]? = none) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      .storage (pendingReturnsRef sender) (.int 0) =
    .ok ({ contract := blindAuctionContract, locals := locals },
      withdrawClearedState evm evm.executionEnv) := by
  rw [assignStorageRef_storage_scalar (hbase := hbase)
    (her := withdrawPendingReturns_evalStorageRef evm locals)
    (hty := withdrawPendingReturns_storageType)
    (hloc := blindAuctionConfig_storage_pendingReturns (withdrawSenderKey evm.executionEnv))
    (hstore := by
      change storageLocStore evm
          (blindAuctionUint256Loc (withdrawAmountSlot evm.executionEnv))
          (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) =
        some (withdrawClearedState evm evm.executionEnv)
      rw [blindAuctionStorageLocStore_uint256]
      rfl)]

theorem withdrawZeroState_originalMap (evm : EVM.State) :
    (withdrawZeroState evm).σ₀ = evm.σ₀ := by
  unfold withdrawZeroState withdrawClearedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_genesisBlockHeader (evm : EVM.State) :
    (withdrawZeroState evm).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold withdrawZeroState withdrawClearedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_blocks (evm : EVM.State) :
    (withdrawZeroState evm).blocks = evm.blocks := by
  unfold withdrawZeroState withdrawClearedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_substate (evm : EVM.State) :
    (withdrawZeroState evm).substate = evm.substate := by
  unfold withdrawZeroState withdrawClearedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawCallStore_success_get (amount : UInt256) (success : Bool) (out : ByteArray) :
    (withdrawCallStore amount success out)["success"]? = some (.bool success) := by
  change (withdrawCallStore amount success out).get? "success" = some (.bool success)
  unfold withdrawCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem withdrawCallStore_amount_get (amount : UInt256) (success : Bool) (out : ByteArray) :
    (withdrawCallStore amount success out)["amount"]? =
      some (.int (Int.ofNat amount.toNat)) := by
  change (withdrawCallStore amount success out).get? "amount" =
    some (.int (Int.ofNat amount.toNat))
  unfold withdrawCallStore withdrawAmountStore
  rw [store_get_ne]
  · rw [store_get_ne]
    · exact store_get_self _ _ _
    · decide
  · decide

theorem withdrawAccountMapEquiv_balance {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) :
    (σ.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ, accountEquiv] at hστ ⊢
  exact hστ.2.1

theorem evalExpr_withdraw_sender (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_withdraw_amount_gt_false (evm : EVM.State) (amount : UInt256)
    (hzero : amount = ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
      (.binary .gt (.var "amount") (.intLit 0)) = .ok (.bool false) := by
  subst hzero
  simp [withdrawAmountStore, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalBinaryOp?]

theorem evalExpr_withdraw_amount_gt_true (evm : EVM.State) (amount : UInt256)
    (hpos : amount ≠ ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
      (.binary .gt (.var "amount") (.intLit 0)) = .ok (.bool true) := by
  simp [withdrawAmountStore, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalBinaryOp?]
  have hnat : 0 < amount.toNat := by
    cases amount with
    | mk val =>
        cases val with
        | mk n hlt =>
            simp [UInt256.toNat] at hpos ⊢
            omega
  omega

theorem evalExpr_withdraw_success (evm : EVM.State) (amount : UInt256) (success : Bool)
    (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawCallStore amount success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawCallStore_success_get]

theorem evalExpr_withdraw_amount (evm : EVM.State) (amount : UInt256) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
      (.var "amount") = .ok (.int (Int.ofNat amount.toNat)) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawAmountStore]

theorem evalExpr_withdraw_emptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem withdrawAssignZero (evm : EVM.State) (amount : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
      .storage (pendingReturnsRef sender) (.int 0) =
        .ok ({ contract := blindAuctionContract, locals := withdrawAmountStore amount },
          withdrawZeroState evm) := by
  have hbase : (withdrawAmountStore amount).get? "pendingReturns" = none := by
    unfold withdrawAmountStore
    rw [store_get_ne]
    · simp
    · decide
  simpa [withdrawZeroState] using withdrawPendingReturns_clear evm (withdrawAmountStore amount) hbase

theorem blindAuctionWithdrawBodyReturns_zero (evm : EVM.State) (amount : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hamount :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (withdrawAmountSlot evm.executionEnv) =
        amount)
    (hzero : amount = ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅ withdrawTransition.body
      (.returned { contract := blindAuctionContract, locals := withdrawAmountStore amount }
        evm none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hamountEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
        (.storage (pendingReturnsRef sender)) =
          .ok (.int (Int.ofNat amount.toNat)) := by
    simpa [hamount] using withdrawPendingReturns_load evm ∅ (by simp)
  refine ExecBlock.consNormal (ExecStmt.letDecl hamountEval) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_withdraw_amount_gt_false evm amount hzero)
      ExecBlock.nil) ?_
  exact ExecBlock.nil

theorem blindAuctionWithdrawBodyReturns_callSuccess
    (evm evm' : EVM.State) (amount : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hamount :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (withdrawAmountSlot evm.executionEnv) =
        amount)
    (hpos : amount ≠ ⟨0⟩)
    (hcall :
      callViaEVM (withdrawZeroState evm) (EVM.address (withdrawZeroState evm).executionEnv.source)
        (Int.ofNat amount.toNat) ByteArray.empty (true, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅ withdrawTransition.body
      (.returned { contract := blindAuctionContract, locals := withdrawCallStore amount true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hamountEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
        (.storage (pendingReturnsRef sender)) =
          .ok (.int (Int.ofNat amount.toNat)) := by
    simpa [hamount] using withdrawPendingReturns_load evm ∅ (by simp)
  refine ExecBlock.consNormal (ExecStmt.letDecl hamountEval) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok
        { contract := blindAuctionContract, locals := withdrawCallStore amount true out } evm')
      (evalExpr_withdraw_amount_gt_true evm amount hpos) ?_) ?_
  · show ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
      [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
        .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ]
      (.ok { contract := blindAuctionContract, locals := withdrawCallStore amount true out } evm')
    refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (withdrawAssignZero evm amount)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallSuccess
        (evalExpr_withdraw_sender (withdrawZeroState evm) (withdrawAmountStore amount))
        (evalExpr_withdraw_amount (withdrawZeroState evm) amount)
        (evalExpr_withdraw_emptyBytes (withdrawZeroState evm) (withdrawAmountStore amount))
        hcall) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_withdraw_success evm' amount true out)) ?_
    exact ExecBlock.nil
  · exact ExecBlock.nil

theorem blindAuctionWithdrawBodyReverts_callFailure
    (evm evm' : EVM.State) (amount : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hamount :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (withdrawAmountSlot evm.executionEnv) =
        amount)
    (hpos : amount ≠ ⟨0⟩)
    (hcall :
      callViaEVM (withdrawZeroState evm) (EVM.address (withdrawZeroState evm).executionEnv.source)
        (Int.ofNat amount.toNat) ByteArray.empty (false, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅
      withdrawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hamountEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
        (.storage (pendingReturnsRef sender)) =
          .ok (.int (Int.ofNat amount.toNat)) := by
    simpa [hamount] using withdrawPendingReturns_load evm ∅ (by simp)
  refine ExecBlock.consNormal (ExecStmt.letDecl hamountEval) ?_
  refine ExecBlock.consRevert
    (ExecStmt.iteTrue (result := .reverted)
      (evalExpr_withdraw_amount_gt_true evm amount hpos) ?_)
  show ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := withdrawAmountStore amount } evm
    [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
      .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (withdrawAssignZero evm amount)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_withdraw_sender (withdrawZeroState evm) (withdrawAmountStore amount))
      (evalExpr_withdraw_amount (withdrawZeroState evm) amount)
      (evalExpr_withdraw_emptyBytes (withdrawZeroState evm) (withdrawAmountStore amount))
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_withdraw_success evm' amount false out))

theorem blindAuctionWithdrawSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_withdraw {cd : ByteArray}
    (hsel : ((⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some withdrawTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray) :=
    (blindAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition])
    (post := [auctionEndTransition, beneficiaryGetter, biddingEndGetter, revealEndGetter,
      endedGetter, highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionWithdrawSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide

theorem blindAuctionDecode_withdraw {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem blindAuctionX_withdraw_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd332⟩ := hreach
  have rd340 := evm_run rd332 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨343⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd340.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_withdraw_entry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨834⟩ [⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd332⟩ := hreach
  have rd834 := evm_run rd332 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨343⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨276⟩, push2 ⟨834⟩, jump (by jump_dest)]
  exact ⟨_, _, rd834⟩

theorem blindAuctionX_withdraw_loadAmount {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨850⟩
      [withdrawAmountWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (withdrawLoadHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd834⟩ := blindAuctionX_withdraw_entry (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd849₀ := evm_run rd834 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (withdrawKeyMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        change (UInt256.toByteArray (withdrawSourceWord I)).write 0 solcFreePtrMem 0 32 =
          withdrawKeyMem I
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore 0 (withdrawLoadHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (withdrawAmountSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawLoadMappingKeccak I) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd850₀⟩ := rd849₀.sload (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [withdrawAmountWord, initState] using rd850₀⟩

theorem blindAuctionX_withdraw_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : withdrawAmountWord σ I = ⟨0⟩) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      ByteArray.empty := by
  obtain ⟨_, _, rd850⟩ := blindAuctionX_withdraw_loadAmount (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd852₀ := evm_run rd850 with [dup1, iszero]
  have rd852 := rd852₀
  rw [hzero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd852
  have rd884 := evm_run rd852 with [push2 ⟨884⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd884 with [jumpdest, pop, jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem blindAuctionX_withdraw_toCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩) :
    ∃ gasArg k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨766⟩
      [gasArg, withdrawSourceWord I, withdrawAmountWord σ I,
        ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        withdrawAmountWord σ I, withdrawSourceWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨_, _, rd850⟩ := blindAuctionX_withdraw_loadAmount (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have hnez : UInt256.isZero (withdrawAmountWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hpos
  have rd852₀ := evm_run rd850 with [dup1, iszero]
  have rd852 := rd852₀
  rw [hnez] at rd852
  have rd873₀ := evm_run rd852 with [
    push2 ⟨884⟩, jumpiNT (by decide),
    caller, push0, dup2, dup2,
    raw mstore 0 (withdrawRehashKeyMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore 0 (withdrawRehashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup3,
    raw keccak256 0 (withdrawAmountSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMappingKeccak I) (by decide) (by evm_ov),
    dup3, swap1]
  obtain ⟨_, _, rd874₀⟩ := rd873₀.sstore hperm (by decide) (by evm_ov)
  have rd765₀ := evm_run rd874₀ with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMem_mload64 I) (by decide) (by evm_ov),
    swap1, swap2, swap1, dup4, swap1, push2 ⟨754⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMem_mload64 I) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup8]
  obtain ⟨gasArg, rd766⟩ := rd765₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [withdrawZeroMap] using rd766⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionX_withdraw_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          (withdrawZeroMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (withdrawSourceWord I))
          (toExecute (withdrawZeroMap σ I) (AccountAddress.ofUInt256 (withdrawSourceWord I)))
          callGas (UInt256.ofNat I.gasPrice)
          (withdrawAmountWord σ I) (withdrawAmountWord σ I)
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩,
            withdrawAmountWord σ I, withdrawSourceWord I, ⟨0⟩,
            withdrawAmountWord σ I, ⟨276⟩, blindAuctionSelWord I]
          (withdrawRehashMem I) (UInt256.ofNat 3) o (cA', σ') k C := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd767₀, hosz⟩ :=
    rd766.callValueMade (by decide) hperm hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (withdrawRehashMem I).readWithPadding (⟨128⟩ : UInt256).toNat
      (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact SimpleAuction.withdraw_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        (withdrawZeroMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (withdrawSourceWord I))
        (toExecute (withdrawZeroMap σ I) (AccountAddress.ofUInt256 (withdrawSourceWord I)))
        callGas (UInt256.ofNat I.gasPrice)
        (withdrawAmountWord σ I) (withdrawAmountWord σ I)
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, SimpleAuction.withdraw_write_len_zero, haw] at rd767₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', hosz,
    by simpa [initState] using rd767₀⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionX_withdraw_callDepth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨0⟩, ⟨128⟩, withdrawAmountWord σ I, withdrawSourceWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨k', C', rd767₀⟩ := rd766.callValueDepthLimit hperm (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, SimpleAuction.withdraw_write_len_zero, haw] at rd767₀
  exact ⟨k', C', by simpa [withdrawZeroMap, initState] using rd767₀⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionX_withdraw_callInsufficient {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : ¬ withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨0⟩, ⟨128⟩, withdrawAmountWord σ I, withdrawSourceWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨k', C', rd767₀⟩ :=
    SimpleAuction.withdrawRDCallValueInsufficientBalance rd766 hperm
      (by decide) hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, SimpleAuction.withdraw_write_len_zero, haw] at rd767₀
  exact ⟨k', C', by simpa [withdrawZeroMap, initState] using rd767₀⟩

theorem blindAuctionX_withdraw_postCallEmpty_toBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ} {z amount sender : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [z, ⟨128⟩, amount, sender, ⟨0⟩, amount, ⟨276⟩, blindAuctionSelWord I]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [z, amount, ⟨276⟩, blindAuctionSelWord I] mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop,
    returndatasize, dup1, push0, dup2, eq, push2 ⟨812⟩,
    jumpiT (by decide) (by jump_dest),
    jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionX_withdraw_postCallNonempty_toBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {k C : ℕ} {z amount sender : UInt256} {o : ByteArray}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [z, ⟨128⟩, amount, sender, ⟨0⟩, amount, ⟨276⟩, blindAuctionSelWord I]
      mem (UInt256.ofNat 3) o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [z, amount, ⟨276⟩, blindAuctionSelWord I] mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd776₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd776 := rd776₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd776
  have rd780 := evm_run rd776 with [push2 ⟨812⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0 mem 64 32
  have rd798 := evm_run rd780 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost hfp (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd801 := evm_run rd798 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd807 := evm_run rd801 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        SimpleAuction.withdrawReturnDataActiveWords o := by
    simp [SimpleAuction.withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd808 := SimpleAuction.withdrawRDReturndatacopy
    (Cₘ (SimpleAuction.withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (SimpleAuction.withdrawReturnDataActiveWords o)
    rd807 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        SimpleAuction.withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd817 := evm_run rd808 with [push2 ⟨817⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd817 with [pop, pop, swap1, pop]⟩

theorem blindAuctionX_withdraw_requireSuccess_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {amount : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [⟨1⟩, amount, ⟨276⟩, blindAuctionSelWord I]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have rd276 := evm_run rd with [
    dup1, push2 ⟨830⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem blindAuctionX_withdraw_requireSuccess_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {amount : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [⟨0⟩, amount, ⟨276⟩, blindAuctionSelWord I]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd827 := evm_run rd with [dup1, push2 ⟨830⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd827 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionX_withdraw_afterCall_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    {amount : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨0⟩, ⟨128⟩, amount, withdrawSourceWord I, ⟨0⟩, amount, ⟨276⟩,
        blindAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) o acc k C)
    (hosz : o.size < UInt256.size) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := SimpleAuction.withdrawByteArray_eq_empty_of_size_eq_zero o ho
    subst o
    obtain ⟨_, _, rd822⟩ :=
      blindAuctionX_withdraw_postCallEmpty_toBranch (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact blindAuctionX_withdraw_requireSuccess_revert rd822
  · obtain ⟨_, _, _, _, rd822⟩ :=
      blindAuctionX_withdraw_postCallNonempty_toBranch (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (withdrawRehashMem_mload64 I) ho hosz
    exact blindAuctionX_withdraw_requireSuccess_revert rd822

theorem blindAuctionX_withdraw_afterCall_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    {amount : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨1⟩, ⟨128⟩, amount, withdrawSourceWord I, ⟨0⟩, amount, ⟨276⟩,
        blindAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) o acc k C)
    (hosz : o.size < UInt256.size) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := SimpleAuction.withdrawByteArray_eq_empty_of_size_eq_zero o ho
    subst o
    obtain ⟨_, _, rd822⟩ :=
      blindAuctionX_withdraw_postCallEmpty_toBranch (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact blindAuctionX_withdraw_requireSuccess_return rd822
  · obtain ⟨_, _, _, _, rd822⟩ :=
      blindAuctionX_withdraw_postCallNonempty_toBranch (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (withdrawRehashMem_mload64 I) ho hosz
    exact blindAuctionX_withdraw_requireSuccess_return rd822

theorem blindAuctionX_withdraw_callDepth_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd767⟩ :=
    blindAuctionX_withdraw_callDepth (g := g) hperm hwv hreach hpos hdepth
  obtain ⟨_, _, rd822⟩ :=
    blindAuctionX_withdraw_postCallEmpty_toBranch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd767
  exact blindAuctionX_withdraw_requireSuccess_revert rd822

theorem blindAuctionX_withdraw_callInsufficient_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨332⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : ¬ withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd767⟩ :=
    blindAuctionX_withdraw_callInsufficient (g := g) hperm hwv hreach hpos hbalance hdepth
  obtain ⟨_, _, rd822⟩ :=
    blindAuctionX_withdraw_postCallEmpty_toBranch (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd767
  exact blindAuctionX_withdraw_requireSuccess_revert rd822

theorem blindAuctionWithdrawBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      withdrawTransition.body .reverted := by
  dsimp [withdrawTransition]
  exact bodyReverts_nonPayable h

/-- `withdraw()` body (pc 332) refines its transition. -/
theorem blindAuctionWithdrawBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨332⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionWithdrawSelector_size hsel
  have hd := blindAuctionDispatch_withdraw (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_withdraw (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hzero : withdrawAmountWord σ_evm I = ⟨0⟩
    · have hword : withdrawAmountWord σ_evm I = withdrawAmountWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (withdrawAmountSlot I) ⟨0⟩
      have hzeroS : withdrawAmountWord σ_solm I = ⟨0⟩ := by
        rw [← hword, hzero]
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hamountS :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
              (withdrawAmountSlot evmS.executionEnv) =
            withdrawAmountWord σ_solm I := by
        simp [evmS, initState, withdrawAmountWord, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage]
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
            withdrawTransition.body
            (.returned
              { contract := blindAuctionContract
                locals := withdrawAmountStore (withdrawAmountWord σ_solm I) }
              evmS none) :=
        blindAuctionWithdrawBodyReturns_zero evmS (withdrawAmountWord σ_solm I)
          (by simpa [evmS, initState] using hwv) hamountS hzeroS
      exact (blindAuctionX_withdraw_zero (g := Sat256.ofUInt256 g) hwv hreach hzero)
        |>.reEquivExecution hcode hd hdec hbody hAccounts (returnEquiv.void rfl rfl rfl)
    · have hword : withdrawAmountWord σ_evm I = withdrawAmountWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (withdrawAmountSlot I) ⟨0⟩
      have hnonzero : withdrawAmountWord σ_evm I ≠ ⟨0⟩ := hzero
      have hposS : withdrawAmountWord σ_solm I ≠ ⟨0⟩ := by
        intro hz
        exact hnonzero (by rw [hword]; exact hz)
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmSZero := withdrawZeroState evmS
      have hamountS :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
              (withdrawAmountSlot evmS.executionEnv) =
            withdrawAmountWord σ_solm I := by
        simp [evmS, initState, withdrawAmountWord, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage]
      have hZeroMap :
          accountMapEquiv (withdrawZeroMap σ_evm I) (withdrawZeroMap σ_solm I) := by
        unfold withdrawZeroMap
        exact accountMapEquiv_sstoreAccountMap I.codeOwner (withdrawAmountSlot I) ⟨0⟩
          hAccounts
      by_cases hdepthEq : I.depth = 1024
      · let evmSFail : EVM.State :=
          { evmSZero with
            substate := (evmSZero.addAccessedAccount
              (EVM.address evmSZero.executionEnv.source)).substate }
        have hcall :
            callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
              (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
              (false, evmSFail, ByteArray.empty) := by
          apply callViaEVM.callNotMade
          · rfl
          · rfl
          · rintro ⟨_, hdepthNe⟩
            exact hdepthNe (by
              simpa [evmSZero, withdrawZeroState, withdrawClearedState, evmS, initState,
                storageStore_executionEnv] using hdepthEq)
        have hbody :
            ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
              withdrawTransition.body .reverted :=
          blindAuctionWithdrawBodyReverts_callFailure evmS evmSFail
            (withdrawAmountWord σ_solm I) ByteArray.empty
            (by simpa [evmS, initState] using hwv) hamountS hposS
            (by simpa [evmSZero] using hcall)
        exact (blindAuctionX_withdraw_callDepth_revert (g := Sat256.ofUInt256 g)
            hperm hwv hreach hnonzero hdepthEq)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdepthLt : I.depth.val < 1024 := by
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          have hneVal : I.depth.val ≠ 1024 := by
            intro hv
            apply hdepthEq
            exact Fin.ext hv
          omega
        by_cases hbalance : withdrawAmountWord σ_evm I ≤
            (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
        · obtain ⟨cA', σ', z, out, A_in, callGas, kCall, CCall, hTheta, houtsz, rd767⟩ :=
            blindAuctionX_withdraw_callMade (g := Sat256.ofUInt256 g) hperm hwv hreach
              hzero hbalance hdepthLt
          obtain ⟨g'', A', hThetaEq⟩ := hTheta
          let evmEZero : EVM.State :=
            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := withdrawZeroMap σ_evm I }
          let evmECall : EVM.State :=
            { evmEZero with accountMap := σ', substate := A', createdAccounts := cA' }
          let targetE : EVM.Address := AccountAddress.ofUInt256 (withdrawSourceWord I)
          let valueE : ℤ := Int.ofNat (withdrawAmountWord σ_evm I).toNat
          have hcallE :
              callViaEVM evmEZero targetE valueE ByteArray.empty (z, evmECall, out) := by
            refine callViaEVM.callMade
              (valueWord := withdrawAmountWord σ_evm I)
              (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
              ?_ ?_ ?_ ?_ ?_
            · exact (blindAuctionWordOfInt_ofNat_toNat (withdrawAmountWord σ_evm I)).symm
            · refine ⟨callGas, A_in, ?_⟩
              simpa [evmEZero, targetE, valueE, initState, hperm, accountAddress_roundtrip,
                withdrawSourceWord] using hThetaEq
            · simp [evmECall]
            · simpa [evmEZero, initState] using hbalance
            · intro hd'
              exact hdepthEq (by simpa [evmEZero, initState] using hd')
          obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
            callViaEVM_accountMapEquiv (storage := blindAuctionConfig.storage)
              (evm_solm := evmSZero) hcallE
              (by
                simpa [evmEZero, evmSZero, withdrawZeroState, withdrawClearedState, evmS,
                  initState, blindAuctionStorageStore_accountMap, storageStore_executionEnv]
                  using hZeroMap)
              (by
                simpa [evmEZero, evmSZero, evmS, initState,
                  withdrawZeroState_originalMap])
              (by
                simp [evmEZero, evmSZero, withdrawZeroState, withdrawClearedState, evmS,
                  initState, blindAuctionStorageStore_createdAccounts])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_genesisBlockHeader])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_blocks])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_substate])
              (by
                simp [evmEZero, evmSZero, withdrawZeroState, withdrawClearedState, evmS,
                  initState, storageStore_executionEnv])
          let evmSCall : EVM.State :=
            { evmSZero with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evmECall.createdAccounts }
          have hAddressId (a : AccountAddress) : EVM.address a = a := by
            apply Fin.ext
            simp [EVM.address, EVM.uintN]
            exact Nat.mod_eq_of_lt a.isLt
          have hTargetEq : targetE = EVM.address evmSZero.executionEnv.source := by
            calc
              targetE = I.source := by
                simpa [targetE, withdrawSourceWord] using accountAddress_roundtrip I.source
              _ = EVM.address evmSZero.executionEnv.source := by
                simp [evmSZero, withdrawZeroState, withdrawClearedState, evmS, initState,
                  storageStore_executionEnv, hAddressId]
          have hValueEq : valueE = Int.ofNat (withdrawAmountWord σ_solm I).toNat := by
            simp [valueE, hword]
          have hcallS :
              callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
                (z, evmSCall, out) := by
            simpa [evmSCall, hTargetEq, hValueEq] using hcallSRaw
          cases z
          · have hbody :
                ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                  withdrawTransition.body .reverted :=
              blindAuctionWithdrawBodyReverts_callFailure evmS evmSCall
                (withdrawAmountWord σ_solm I) out
                (by simpa [evmS, initState] using hwv) hamountS hposS
                (by simpa [evmSZero] using hcallS)
            exact (blindAuctionX_withdraw_afterCall_revert
                (g := Sat256.ofUInt256 g) (by simpa using rd767) houtsz)
              |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hbody :
                ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                  withdrawTransition.body
                  (.returned
                    { contract := blindAuctionContract
                      locals := withdrawCallStore (withdrawAmountWord σ_solm I) true out }
                    evmSCall none) :=
              blindAuctionWithdrawBodyReturns_callSuccess evmS evmSCall
                (withdrawAmountWord σ_solm I) out
                (by simpa [evmS, initState] using hwv) hamountS hposS
                (by simpa [evmSZero] using hcallS)
            have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (cA', σ') ByteArray.empty :=
              blindAuctionX_withdraw_afterCall_return (g := Sat256.ofUInt256 g)
                (by simpa using rd767) houtsz
            exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
              (by simp [evmSCall, evmECall])
              (by simpa [evmSCall, evmECall] using hPostAccounts)
              (returnEquiv.void rfl rfl rfl)
        · let evmSFail : EVM.State :=
            { evmSZero with
              substate := (evmSZero.addAccessedAccount
                (EVM.address evmSZero.executionEnv.source)).substate }
          have hBalEq :
              (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) =
                (withdrawZeroMap σ_solm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
            withdrawAccountMapEquiv_balance hZeroMap I.codeOwner
          have hcall :
              callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
                (false, evmSFail, ByteArray.empty) := by
            apply callViaEVM.callNotMade
            · rfl
            · rfl
            · rintro ⟨hvalueBal, _⟩
              rw [blindAuctionWordOfInt_ofNat_toNat] at hvalueBal
              have hvalueBalS :
                    withdrawAmountWord σ_solm I ≤
                      (withdrawZeroMap σ_solm I |>.find? I.codeOwner |>.elim ⟨0⟩
                        (·.balance)) := by
                simpa [evmSZero, withdrawZeroState, withdrawClearedState, evmS, initState,
                  withdrawZeroMap, blindAuctionStorageStore_accountMap,
                  storageStore_executionEnv] using hvalueBal
              have hvalueBalE :
                  withdrawAmountWord σ_evm I ≤
                    (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩
                      (·.balance)) := by
                simpa [hword, hBalEq] using hvalueBalS
              exact hbalance hvalueBalE
          have hbody :
              ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                withdrawTransition.body .reverted :=
            blindAuctionWithdrawBodyReverts_callFailure evmS evmSFail
              (withdrawAmountWord σ_solm I) ByteArray.empty
              (by simpa [evmS, initState] using hwv) hamountS hposS
              (by simpa [evmSZero] using hcall)
          exact (blindAuctionX_withdraw_callInsufficient_revert (g := Sat256.ofUInt256 g)
              hperm hwv hreach hzero hbalance hdepthLt)
            |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hrev := blindAuctionX_withdraw_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          withdrawTransition.body .reverted := by
      exact blindAuctionWithdrawBodyReverts_nonpayable
        (by simp only [initState]; exact hwv)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
