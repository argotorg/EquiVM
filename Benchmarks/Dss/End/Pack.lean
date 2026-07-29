import Benchmarks.Dss.End.Dispatch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

attribute [local simp]
  endWardsSelectorBytes
  endVatSelectorBytes
  endCatSelectorBytes
  endDogSelectorBytes
  endVowSelectorBytes
  endPotSelectorBytes
  endSpotSelectorBytes
  endCureSelectorBytes
  endLiveSelectorBytes
  endWhenSelectorBytes
  endWaitSelectorBytes
  endDebtSelectorBytes
  endTagSelectorBytes
  endGapSelectorBytes
  endArtSelectorBytes
  endFixSelectorBytes
  endBagSelectorBytes
  endOutSelectorBytes
  endRelySelectorBytes
  endDenySelectorBytes
  endFileAddressSelectorBytes
  endFileUintSelectorBytes
  endCageSelectorBytes
  endCageIlkSelectorBytes
  endSnipSelectorBytes
  endSkipSelectorBytes
  endSkimSelectorBytes
  endFreeSelectorBytes
  endThawSelectorBytes
  endFlowSelectorBytes
  endPackSelectorBytes
  endCashSelectorBytes

/-! ## `pack(uint256)` -/

abbrev endPackConcreteSelector : ByteArray := selectorBytes 0x6e 0xa4 0x25 0x55

abbrev endPackWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev endPackWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (endPackWadWord I).toNat)

abbrev endPackStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "wad" (endPackWadValue I)

abbrev endPackEntryPc : UInt256 := ⟨806⟩
abbrev endPackReturnPc : UInt256 := ⟨562⟩
abbrev endPackDecodedPc : UInt256 := ⟨828⟩
abbrev endPackBodyPc : UInt256 := ⟨6345⟩

abbrev endPackRayWord : UInt256 := ⟨1000000000000000000000000000⟩

abbrev endPackMoveSelectorWord : UInt256 := ⟨0xbb35783b⟩

abbrev endPackMoveSelectorShifted : UInt256 := ⟨0xbb35783b00000000000000000000000000000000000000000000000000000000⟩

abbrev endPackMoveOutPtr : UInt256 := ⟨128⟩

abbrev endPackMoveInSize : UInt256 := ⟨100⟩

abbrev endPackMoveEndPtr : UInt256 := ⟨228⟩

abbrev endPackAmtWord (I : ExecutionEnv) : UInt256 :=
  endPackWadWord I * endPackRayWord

abbrev endPackStoreAmt (I : ExecutionEnv) : Store :=
  (endPackStore I).insert "amt" (.int (Int.ofNat (endPackAmtWord I).toNat))

abbrev endPackStoreMove (I : ExecutionEnv) : Store :=
  (endPackStoreAmt I).insert "_move" (collapseReturns [])

abbrev endPackStoreBagNew (I : ExecutionEnv) (bagNew : UInt256) : Store :=
  (endPackStoreMove I).insert "bagNew" (.int (Int.ofNat bagNew.toNat))

abbrev endPackDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

abbrev endPackVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨1⟩ σ I) solcAddrMask

abbrev endPackVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨4⟩ σ I) solcAddrMask

abbrev endPackVatAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endPackVatWord σ I).toNat

abbrev endPackVowAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endPackVowWord σ I).toNat

abbrev endPackBagKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def endPackBagSlot (I : ExecutionEnv) : UInt256 :=
  bagSlot (endPackBagKey I)

abbrev endPackBagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endPackBagSlot I) σ I

abbrev endPackEvaledBagRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bag", steps := [.mindex (endPackBagKey I)] }

def endPackPostState (evm : EVM.State) (I : ExecutionEnv) (bagNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endPackBagSlot I) bagNew

noncomputable def endPackMoveSelectorMem (mem : ByteArray) : ByteArray :=
  endPackMoveSelectorShifted.toByteArray.write 0 mem endPackMoveOutPtr.toNat 32

noncomputable def endPackMoveArg0Mem (_σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (endPackMoveSelectorMem mem)
    (endPackMoveOutPtr + ⟨4⟩).toNat 32

noncomputable def endPackMoveArg1Mem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (endPackVowWord σ I).toByteArray.write 0 (endPackMoveArg0Mem σ I mem)
    (endPackMoveOutPtr + ⟨36⟩).toNat 32

noncomputable def endPackMoveCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (mem : ByteArray) : ByteArray :=
  amt.toByteArray.write 0 (endPackMoveArg1Mem σ I mem)
    (endPackMoveOutPtr + ⟨68⟩).toNat 32

noncomputable def endPackMovePostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (endPackMoveCalldataMem σ I amt solcFreePtrMem) endPackMoveOutPtr.toNat
    (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat

theorem endPackBagSlot_eq (I : ExecutionEnv) :
    endPackBagSlot I = solcMappingSlot ⟨16⟩ (solcSourceWord I) := by
  unfold endPackBagSlot bagSlot endPackBagKey mapSlot solcMappingSlot
  rw [keyValueToWord_address]

theorem endPackMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endPackMoveSelectorMem mem).size = 160 := by
  unfold endPackMoveSelectorMem
  exact toByteArray_write32_size_of_ge mem endPackMoveSelectorShifted
    endPackMoveOutPtr.toNat 96 160 hmem (by native_decide) (by native_decide)
    (by native_decide)

theorem endPackMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endPackMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endPackMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap endPackMoveSelectorShifted mem
    endPackMoveOutPtr.toNat 64 (by rw [hmem]) (by native_decide)
    (by rw [hmem]; native_decide), hread64]

theorem endPackMoveArg0Mem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveArg0Mem σ I mem).size = 164 := by
  unfold endPackMoveArg0Mem
  exact toByteArray_write32_size_of_le (endPackMoveSelectorMem mem) (solcSourceWord I)
    132 160 164 (endPackMoveSelectorMem_size hmem)
    (by rw [endPackMoveSelectorMem_size hmem]; omega) (by omega)

theorem endPackMoveArg0Mem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endPackMoveArg0Mem σ I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackMoveArg0Mem
  change ((solcSourceWord I).toByteArray.write 0 (endPackMoveSelectorMem mem) 132
      32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endPackMoveSelectorMem_size hmem]; omega) (by omega),
    endPackMoveSelectorMem_read64 hmem hread64]

theorem endPackMoveArg1Mem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveArg1Mem σ I mem).size = 196 := by
  unfold endPackMoveArg1Mem
  exact toByteArray_write32_size_of_ge (endPackMoveArg0Mem σ I mem) (endPackVowWord σ I)
    164 164 196 (endPackMoveArg0Mem_size σ I hmem)
    (by omega) (by native_decide) (by omega)

theorem endPackMoveArg1Mem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endPackMoveArg1Mem σ I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackMoveArg1Mem
  change ((endPackVowWord σ I).toByteArray.write 0 (endPackMoveArg0Mem σ I mem)
      164 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap (endPackVowWord σ I)
    (endPackMoveArg0Mem σ I mem) 164 64
    (by rw [endPackMoveArg0Mem_size σ I hmem]; native_decide)
    (by native_decide) (by rw [endPackMoveArg0Mem_size σ I hmem]; native_decide),
    endPackMoveArg0Mem_read64 σ I hmem hread64]

theorem endPackMoveCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).size = 228 := by
  unfold endPackMoveCalldataMem
  exact toByteArray_write32_size_of_ge (endPackMoveArg1Mem σ I mem) amt
    196 196 228 (endPackMoveArg1Mem_size σ I hmem)
    (by omega) (by native_decide) (by omega)

theorem endPackMoveCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackMoveCalldataMem
  change (amt.toByteArray.write 0 (endPackMoveArg1Mem σ I mem) 196 32).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap amt (endPackMoveArg1Mem σ I mem) 196 64
    (by rw [endPackMoveArg1Mem_size σ I hmem]; native_decide)
    (by native_decide) (by rw [endPackMoveArg1Mem_size σ I hmem]; native_decide),
    endPackMoveArg1Mem_read64 σ I hmem hread64]

theorem endPackMovePostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    endPackMovePostCallMem σ I amt out = endPackMoveCalldataMem σ I amt solcFreePtrMem := by
  unfold endPackMovePostCallMem
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
      exact Nat.zero_le _
    simp [min, hle]
  rw [hmin]
  exact byteArray_write_len_zero out (endPackMoveCalldataMem σ I amt solcFreePtrMem)
    0 endPackMoveOutPtr.toNat

noncomputable def endPackBagHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨16⟩ (endPackMovePostCallMem σ I amt out)

noncomputable def endPackBagStoreKeyMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  wordAt0Mem (solcSourceWord I) (endPackBagHashMem σ I amt out)

noncomputable def endPackBagStoreSlotMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨16⟩ (endPackBagHashMem σ I amt out)

theorem endPackBagHashMem_write_key (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (solcSourceWord I).toByteArray.write 0 (endPackBagHashMem σ I amt out) 0 32 =
      endPackBagStoreKeyMem σ I amt out := by
  rfl

theorem endPackBagHashMem_write_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (UInt256.toByteArray ⟨16⟩).write 0
        (endPackBagStoreKeyMem σ I amt out) 32 32 =
      endPackBagStoreSlotMem σ I amt out := by
  rfl

theorem endPackMovePostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackMovePostCallMem σ I amt out).size = 228 := by
  rw [endPackMovePostCallMem_eq]
  exact endPackMoveCalldataMem_size σ I amt solcFreePtrMem_size

theorem endPackMovePostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackMovePostCallMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endPackMovePostCallMem_eq]
  exact endPackMoveCalldataMem_read64 σ I amt solcFreePtrMem_size solcFreePtrMem_read64

theorem endWordAt0Mem_size_228 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (wordAt0Mem word mem).size = 228 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 228 228 hmem (by omega) (by omega)

theorem endTwoWordHashMem_size_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).size = 228 := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32 228 228
    (endWordAt0Mem_size_228 key hmem)
    (by rw [endWordAt0Mem_size_228 key hmem]; omega) (by omega)

theorem endTwoWordHashMem_read64_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_228 key hmem]; omega) (by omega)
      (by rw [endWordAt0Mem_size_228 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem endTwoWordHashMem_read0_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_228 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem endTwoWordHashMem_read32_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_228 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem endTwoWordHashMem_read0_64_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [endTwoWordHashMem_size_228 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [endTwoWordHashMem_size_228 key slot hmem]; omega),
      endTwoWordHashMem_read0_228 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [endTwoWordHashMem_size_228 key slot hmem]; omega),
      endTwoWordHashMem_read32_228 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem endPackBagHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endPackBagHashMem σ I amt out).readWithPadding 0 64))) =
      endPackBagSlot I := by
  rw [endPackBagSlot_eq]
  unfold endPackBagHashMem
  rw [endTwoWordHashMem_read0_64_228 (solcSourceWord I) ⟨16⟩
    (endPackMovePostCallMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨16⟩

theorem endPackBagHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackBagHashMem σ I amt out).size = 228 := by
  unfold endPackBagHashMem
  exact endTwoWordHashMem_size_228 (solcSourceWord I) ⟨16⟩
    (endPackMovePostCallMem_size σ I amt out)

theorem endPackBagHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackBagHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackBagHashMem
  exact endTwoWordHashMem_read64_228 (solcSourceWord I) ⟨16⟩
    (endPackMovePostCallMem_size σ I amt out)
    (endPackMovePostCallMem_read64 σ I amt out)

theorem endPackBagStoreSlotMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackBagStoreSlotMem σ I amt out).size = 228 := by
  unfold endPackBagStoreSlotMem
  exact endTwoWordHashMem_size_228 (solcSourceWord I) ⟨16⟩
    (endPackBagHashMem_size σ I amt out)

theorem endPackBagStoreSlotMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackBagStoreSlotMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackBagStoreSlotMem
  exact endTwoWordHashMem_read64_228 (solcSourceWord I) ⟨16⟩
    (endPackBagHashMem_size σ I amt out)
    (endPackBagHashMem_read64 σ I amt out)

theorem endPackBagStoreSlotMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endPackBagStoreSlotMem σ I amt out).readWithPadding 0 64))) =
      endPackBagSlot I := by
  rw [endPackBagSlot_eq]
  unfold endPackBagStoreSlotMem
  rw [endTwoWordHashMem_read0_64_228 (solcSourceWord I) ⟨16⟩
    (endPackBagHashMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨16⟩

noncomputable def endPackLogDataMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (endPackWadWord I)).write 0
    (endPackBagStoreSlotMem σ I amt out) 128 32

theorem endPackLogDataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackLogDataMem σ I amt out).size = 228 := by
  unfold endPackLogDataMem
  exact toByteArray_write32_size_of_le (endPackBagStoreSlotMem σ I amt out)
    (endPackWadWord I) 128 228 228
    (endPackBagStoreSlotMem_size σ I amt out)
    (by rw [endPackBagStoreSlotMem_size σ I amt out]; omega) (by omega)

theorem endPackLogDataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endPackLogDataMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endPackLogDataMem
  rw [toByteArray_write_read_below_of_gap (endPackWadWord I)
    (endPackBagStoreSlotMem σ I amt out) 128 64
    (by rw [endPackBagStoreSlotMem_size σ I amt out]; omega) (by omega)
    (by rw [endPackBagStoreSlotMem_size σ I amt out]; native_decide)]
  exact endPackBagStoreSlotMem_read64 σ I amt out

theorem endPackDecode6612Mstore :
    decode endBytecode ⟨6612⟩ = some (.MSTORE, .none) := by
  native_decide

theorem endPackMoveCalldataMem_read128_4
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 128 4 =
      moveSelector := by
  have h132 : (endPackMoveOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  have h164 : (endPackMoveOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  have h196 : (endPackMoveOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold endPackMoveCalldataMem
  rw [h196]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [endPackMoveArg1Mem_size σ I hmem]) (by omega)
    (by rw [endPackMoveArg1Mem_size σ I hmem]; omega) (by omega) (by norm_num)]
  unfold endPackMoveArg1Mem
  rw [h164]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [endPackMoveArg0Mem_size σ I hmem]) (by omega)
    (by rw [endPackMoveArg0Mem_size σ I hmem]; omega) (by omega) (by norm_num)]
  unfold endPackMoveArg0Mem
  rw [h132]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endPackMoveSelectorMem_size hmem]; omega) (by omega)
    (by rw [endPackMoveSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
  unfold endPackMoveSelectorMem endPackMoveOutPtr
  change
    (endPackMoveSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
      moveSelector
  rw [toByteArray_write_read_window_of_gap endPackMoveSelectorShifted mem 128 0 4
    (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  unfold endPackMoveSelectorShifted moveSelector selectorBytes
  native_decide

theorem endPackMoveCalldataMem_read132_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 132 32 =
      (solcSourceWord I).toByteArray := by
  have h132 : (endPackMoveOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  have h164 : (endPackMoveOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  have h196 : (endPackMoveOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold endPackMoveCalldataMem
  rw [h196]
  rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
    (by rw [endPackMoveArg1Mem_size σ I hmem]) (by omega)
    (by rw [endPackMoveArg1Mem_size σ I hmem]; omega) (by omega) (by norm_num)]
  unfold endPackMoveArg1Mem
  rw [h164]
  rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
    (by rw [endPackMoveArg0Mem_size σ I hmem]) (by omega)
    (by rw [endPackMoveArg0Mem_size σ I hmem]) (by omega) (by norm_num)]
  unfold endPackMoveArg0Mem
  rw [h132]
  rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
    (by rw [endPackMoveSelectorMem_size hmem]; omega) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endPackMoveCalldataMem_read164_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 164 32 =
      (endPackVowWord σ I).toByteArray := by
  have h164 : (endPackMoveOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  have h196 : (endPackMoveOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold endPackMoveCalldataMem
  rw [h196]
  rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
    (by rw [endPackMoveArg1Mem_size σ I hmem]) (by omega)
    (by rw [endPackMoveArg1Mem_size σ I hmem]) (by omega) (by norm_num)]
  unfold endPackMoveArg1Mem
  rw [h164]
  rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
    (by rw [endPackMoveArg0Mem_size σ I hmem]) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endPackMoveCalldataMem_read196_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 196 32 = amt.toByteArray := by
  have h196 : (endPackMoveOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold endPackMoveCalldataMem
  rw [h196]
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
    (by rw [endPackMoveArg1Mem_size σ I hmem])]
  rw [toByteArray_extract_all]

theorem endPackMoveCalldataMem_read128_100
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endPackMoveCalldataMem σ I amt mem).readWithPadding 128 100 =
      moveSelector ++ (solcSourceWord I).toByteArray ++ (endPackVowWord σ I).toByteArray ++
        amt.toByteArray := by
  have hsize : (endPackMoveCalldataMem σ I amt mem).size = 228 :=
    endPackMoveCalldataMem_size σ I amt hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (endPackMoveCalldataMem σ I amt mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endPackMoveCalldataMem σ I amt mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endPackMoveCalldataMem σ I amt mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endPackMoveCalldataMem_read128_4 σ I amt hmem,
    endPackMoveCalldataMem_read132_32 σ I amt hmem,
    endPackMoveCalldataMem_read164_32 σ I amt hmem,
    endPackMoveCalldataMem_read196_32 σ I amt hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endPackMoveEncode_eq (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    config.externalABI.encode? "move"
        [.address I.source, .address (endPackVowAddr σ I), .int (Int.ofNat amt.toNat)] =
      some ((endPackMoveCalldataMem σ I amt mem).readWithPadding
        endPackMoveOutPtr.toNat endPackMoveInSize.toNat) := by
  change config.externalABI.encode? "move"
      [.address I.source, .address (endPackVowAddr σ I), .int (Int.ofNat amt.toNat)] =
    some ((endPackMoveCalldataMem σ I amt mem).readWithPadding 128 100)
  rw [endPackMoveCalldataMem_read128_100 σ I amt hmem]
  have hsourceWord : EVM.word ↑I.source = solcSourceWord I := by
    change UInt256.ofNat I.source.val = solcSourceWord I
    rfl
  have hvowCanon : (endPackVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I)
  have hvowVal :
      (endPackVowAddr σ I).val = (endPackVowWord σ I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  have hvowWord : EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I := by
    change UInt256.ofNat (endPackVowAddr σ I).val = endPackVowWord σ I
    rw [hvowVal]
    exact u256_ofNat_toNat _
  have hamtLt : amt.toNat < EVM.twoPow 256 := amt.val.isLt
  have hamtWord : EVM.word amt.toNat = amt := by
    show UInt256.ofNat amt.toNat = amt
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int, moveSelector,
    selectorBytes, hsourceWord, hvowWord, hamtLt, hamtWord]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.data_append, Array.append_assoc]

theorem endPackX_debtZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hdebt : endPackDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endPackBodyPc
      [endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd6348 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6349raw⟩ := rd6348.sload (by native_decide) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endPackDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd6349zero := rd6349raw
  rw [hdebtRaw] at rd6349zero
  obtain ⟨_, _, rd6349⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6349⟩
        (⟨0⟩ :: endPackWadWord I :: endPackReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endPackBodyPc] using rd6349zero⟩
  have rd6352 := rd6349.push2 ⟨6413⟩ (by native_decide) (by evm_ov)
  have rd6353 := rd6352.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6353⟩
        [endPackWadWord I, endPackReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd6353⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨6353⟩) (len := ⟨13⟩)
    (rawWord := ⟨5500907680949753345960233497199⟩) (shift := ⟨152⟩)
    (word := UInt256.shiftLeft ⟨5500907680949753345960233497199⟩ ⟨152⟩)
    (op := .PUSH13) (width := 13)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endPackX_mulEntry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endPackBodyPc
      [endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endPackRayWord, endPackWadWord I, ⟨6462⟩, endPackVowWord σ I,
        solcSourceWord I, endPackMoveSelectorWord, endPackVatWord σ I,
        endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6348 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6349raw⟩ := rd6348.sload (by native_decide) (by evm_ov)
  have rd6349 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6349⟩
        (endPackDebtWord σ I :: endPackWadWord I :: endPackReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [endPackDebtWord, endSlotWord, solcSlotWord] using rd6349raw⟩
  obtain ⟨_, _, rd6349⟩ := rd6349
  have rd6352 := rd6349.push2 ⟨6413⟩ (by native_decide) (by evm_ov)
  have rd6413 := rd6352.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)
  have rd6416 := evm_run rd6413 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6417raw⟩ := rd6416.sload (by native_decide) (by evm_ov)
  have rd6417 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6417⟩
        (endSlotWord ⟨1⟩ σ I :: endPackWadWord I :: endPackReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd6417raw⟩
  obtain ⟨_, _, rd6417⟩ := rd6417
  have rd6419 := rd6417.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6420raw⟩ := rd6419.sload (by native_decide) (by evm_ov)
  have rd6420 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6420⟩
        (endSlotWord ⟨4⟩ σ I :: endSlotWord ⟨1⟩ σ I :: endPackWadWord I ::
          endPackReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd6420raw⟩
  obtain ⟨_, _, rd6420⟩ := rd6420
  have rd6445 := evm_run rd6420 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xbb35783b⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨6462⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have rd6458 := rd6445.pushConst endPackRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd6461 := rd6458.push2 ⟨10170⟩ (by native_decide) (by evm_ov)
  have rd10170 := rd6461.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [endPackRayWord, endPackVatWord, endPackVowWord, endPackMoveSelectorWord,
      endSlotWord, solcSlotWord, solcAddrMask, u256_land_comm] using rd10170⟩

theorem endPackX_mulOverflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hover : UInt256.size ≤ (endPackWadWord I).toNat * endPackRayWord.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endPackRayWord, endPackWadWord I, ⟨6462⟩, endPackVowWord σ I,
        solcSourceWord I, endPackMoveSelectorWord, endPackVatWord σ I,
        endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdivNe :
      UInt256.div (endPackWadWord I * endPackRayWord) endPackRayWord ≠
        endPackWadWord I := by
    have hcomm :
        UInt256.div (endPackRayWord * endPackWadWord I) endPackRayWord ≠
          endPackWadWord I := by
      simpa [endPackRayWord] using
        endU256_mul_div_overflow_ne (endPackWadWord I) endPackRayWord hover
    intro hbad
    have hmul : endPackRayWord * endPackWadWord I = endPackWadWord I * endPackRayWord := by
      simpa using u256_mul_comm endPackRayWord (endPackWadWord I)
    exact hcomm (by rwa [hmul])
  have rd10179 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : UInt256.isZero endPackRayWord = ⟨0⟩ := by
    native_decide
  have rd10180 := rd10179.jumpiNT (by native_decide) hrayNonzero (by evm_ov)
  have rd10192 := evm_run rd10180 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have hrayCond : endPackRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10194 := rd10192.jumpiT (by native_decide) hrayCond (by jump_dest) (by evm_ov)
  have rd10201 := evm_run rd10194 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqCond :
      UInt256.eq (UInt256.div (endPackWadWord I * endPackRayWord) endPackRayWord)
        (endPackWadWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne hdivNe
  have rdFallthrough := rd10201.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endPackX_mulReturns {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endPackRayWord, endPackWadWord I, ⟨6462⟩, endPackVowWord σ I,
        solcSourceWord I, endPackMoveSelectorWord, endPackVatWord σ I,
        endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6462⟩
      [endPackAmtWord I, endPackVowWord σ I, solcSourceWord I,
        endPackMoveSelectorWord, endPackVatWord σ I, endPackWadWord I,
        endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hdiv :
      UInt256.div (endPackWadWord I * endPackRayWord) endPackRayWord =
        endPackWadWord I := by
    apply u256_inj
    rw [udiv_toNat]
    have hprod :
        (endPackWadWord I * endPackRayWord).toNat =
          (endPackWadWord I).toNat * endPackRayWord.toNat := by
      rw [umul_toNat (endPackWadWord I) endPackRayWord hfit]
    have hrayPos : 0 < endPackRayWord.toNat := by
      native_decide
    rw [hprod]
    simpa [Nat.mul_comm] using
      Nat.mul_div_right (endPackWadWord I).toNat hrayPos
  have rd10179 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hrayNonzero : UInt256.isZero endPackRayWord = ⟨0⟩ := by
    native_decide
  have rd10180 := rd10179.jumpiNT (by native_decide) hrayNonzero (by evm_ov)
  have rd10192 := evm_run rd10180 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10194⟩ (by native_decide) (by evm_ov)]
  have hrayCond : endPackRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10194 := rd10192.jumpiT (by native_decide) hrayCond (by jump_dest) (by evm_ov)
  have rd10201 := evm_run rd10194 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqCond :
      UInt256.eq (UInt256.div (endPackWadWord I * endPackRayWord) endPackRayWord)
        (endPackWadWord I) ≠ ⟨0⟩ := by
    rw [hdiv, u256_eq_refl]
    exact one_ne_zero_uint
  have rd10108 := rd10201.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
  have rd6462 := evm_run rd10108 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [endPackAmtWord] using rd6462⟩

theorem endPackX_moveExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {amt : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6462⟩
      [amt, endPackVowWord σ I, solcSourceWord I, endPackMoveSelectorWord,
        endPackVatWord σ I, endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6536⟩
      (endPackVatWord σ I :: endPackVatWord σ I :: ⟨0⟩ :: endPackMoveOutPtr ::
        endPackMoveInSize :: endPackMoveOutPtr :: ⟨0⟩ :: endPackMoveEndPtr ::
        endPackMoveSelectorWord :: endPackVatWord σ I :: endPackWadWord I ::
        endPackReturnPc :: sel :: [])
      (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
              else UInt256.ofNat
                (fromByteArrayBigEndian
          (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hcallMem :
      (endPackMoveCalldataMem σ I amt solcFreePtrMem).size = 228 :=
    endPackMoveCalldataMem_size σ I amt solcFreePtrMem_size
  have hcallRead64 :
      (endPackMoveCalldataMem σ I amt solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endPackMoveCalldataMem_read64 σ I amt solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endPackMoveCalldataMem σ I amt solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
              else UInt256.ofNat
                (fromByteArrayBigEndian
          ((endPackMoveCalldataMem σ I amt solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorMask :
      UInt256.land endPackMoveSelectorWord (⟨0xffffffff⟩ : UInt256) =
        endPackMoveSelectorWord := by
    native_decide
  have hsourceMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (solcSourceWord I) = solcSourceWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (solcSourceWord_canonical I)
  have hvowMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endPackVowWord σ I) = endPackVowWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I))
  have rd6536 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endPackMoveSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endPackMoveArg0Mem σ I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        rw [hsourceMask]
        simp only [endPackMoveArg0Mem, endPackMoveOutPtr]
        rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat =
          ((⟨128⟩ : UInt256) + ⟨4⟩).toNat from by native_decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endPackMoveArg1Mem σ I solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        rw [hvowMask]
        simp only [endPackMoveArg1Mem, endPackMoveOutPtr]
        rw [show ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨128⟩)).toNat =
          ((⟨128⟩ : UInt256) + ⟨36⟩).toNat from by native_decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endPackMoveSelectorMem, endPackMoveArg0Mem, endPackMoveArg1Mem,
      endPackMoveCalldataMem, endPackMoveOutPtr, endPackMoveInSize, endPackMoveEndPtr,
      endPackMoveSelectorShifted, endPackMoveSelectorWord, endPackVatWord, endPackVowWord,
      endSlotWord, solcSlotWord, solcAddrMask, hselectorMask, hsourceMask, hvowMask,
      u256_land_comm] using rd6536⟩

theorem endPackX_moveNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel amt : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6462⟩
      [amt, endPackVowWord σ I, solcSourceWord I, endPackMoveSelectorWord,
        endPackVatWord σ I, endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6536⟩ := endPackX_moveExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6536⟩) (okPc := ⟨6548⟩) rd6536
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem endPackX_moveCallReady {cA gh bl σ σ₀ A I} {g : Sat256} {sel amt : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6462⟩
      [amt, endPackVowWord σ I, solcSourceWord I, endPackMoveSelectorWord,
        endPackVatWord σ I, endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6551⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endPackMoveOutPtr ::
        endPackMoveInSize :: endPackMoveOutPtr :: ⟨0⟩ :: endPackMoveEndPtr ::
        endPackMoveSelectorWord :: endPackVatWord σ I :: endPackWadWord I ::
        endPackReturnPc :: sel :: [])
      (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd6536⟩ := endPackX_moveExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd6551⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6536⟩) (okPc := ⟨6548⟩) rd6536
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd6551⟩

theorem endPackX_movePostCall {cA gh bl σ σ₀ A I} {g : UInt256} {sel amt gasWord : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6551⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endPackMoveOutPtr ::
        endPackMoveInSize :: endPackMoveOutPtr :: ⟨0⟩ :: endPackMoveEndPtr ::
        endPackMoveSelectorWord :: endPackVatWord σ I :: endPackWadWord I ::
        endPackReturnPc :: sel :: [])
      (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endPackVatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endPackMoveCalldataMem σ I amt solcFreePtrMem).readWithPadding
            endPackMoveOutPtr.toNat endPackMoveInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endPackMoveEndPtr :: endPackMoveSelectorWord ::
            endPackVatWord σ I :: endPackWadWord I :: endPackReturnPc :: sel :: [])
          (endPackMovePostCallMem σ I amt out) (UInt256.ofNat 8) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd6552raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          endPackMoveOutPtr.toNat endPackMoveInSize.toNat)
          endPackMoveOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      unfold endPackMoveOutPtr endPackMoveInSize
      native_decide
    simpa [endPackMovePostCallMem, endPackMoveOutPtr, endPackMoveInSize,
      endPackMoveEndPtr, haw] using rd6552raw

theorem endPackX_moveCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel amt gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6551⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endPackMoveOutPtr ::
        endPackMoveInSize :: endPackMoveOutPtr :: ⟨0⟩ :: endPackMoveEndPtr ::
        endPackMoveSelectorWord :: endPackVatWord σ I :: endPackWadWord I ::
        endPackReturnPc :: sel :: [])
      (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
      (⟨0⟩ :: endPackMoveEndPtr :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      (endPackMoveCalldataMem σ I amt solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd6552raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        endPackMoveOutPtr.toNat endPackMoveInSize.toNat)
        endPackMoveOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    unfold endPackMoveOutPtr endPackMoveInSize
    native_decide
  simpa [endPackMoveOutPtr, endPackMoveInSize, endPackMoveEndPtr, hmin,
    byteArray_write_len_zero, haw] using rd6552raw

theorem endPackX_moveCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
      (⟨0⟩ :: endPackMoveEndPtr :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6552⟩) (okPc := ⟨6568⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem endPackX_moveCallSucceeded {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
      (⟨1⟩ :: endPackMoveEndPtr :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6570⟩
      (endPackMoveEndPtr :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨6552⟩) (okPc := ⟨6568⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endPackX_bagAddEntry {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
      (⟨1⟩ :: endPackMoveEndPtr :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      (endPackMovePostCallMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endPackWadWord I, endPackBagWord σ' I, ⟨6599⟩, endPackWadWord I,
        endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k' C' := by
  obtain ⟨_, _, rd6570⟩ := endPackX_moveCallSucceeded (g := g) h
  have rd6576 := evm_run rd6570 with [
    raw pop (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdKeyMem := rd6576.mstore 0
    (wordAt0Mem (solcSourceWord I) (endPackMovePostCallMem σ I (endPackAmtWord I) out))
    (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdHashPrefix := evm_run rdKeyMem with [
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdHashPrefix.mstore 0
    (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (endPackBagSlot I) (UInt256.ofNat 8)
    (by native_decide) mem_cost (endPackBagHashMem_slot σ I (endPackAmtWord I) out)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide) (by evm_ov)
  have rdLoaded : ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6587⟩
      (endPackBagWord σ' I :: endPackMoveSelectorWord :: endPackVatWord σ I ::
        endPackWadWord I :: endPackReturnPc :: sel :: [])
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endPackBagWord, endSlotWord, solcSlotWord] using rdLoadedRaw⟩
  obtain ⟨_, _, rdLoaded⟩ := rdLoaded
  have rdJumpTarget := evm_run rdLoaded with [
    raw push2 ⟨6599⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdJumpTarget.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endPackX_bagAddOverflow {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤ (endPackBagWord σ' I).toNat + (endPackWadWord I).toNat)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endPackWadWord I, endPackBagWord σ' I, ⟨6599⟩, endPackWadWord I,
        endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let bag := endPackBagWord σ' I
  let wad := endPackWadWord I
  have hover' : UInt256.size ≤ wad.toNat + bag.toNat := by
    dsimp [bag, wad]
    simpa [Nat.add_comm] using hover
  have hsum_lt2 : wad.toNat + bag.toNat < 2 * UInt256.size := by
    have hbag : bag.toNat < UInt256.size := bag.val.isLt
    have hwad : wad.toNat < UInt256.size := wad.val.isLt
    omega
  have hmod : (wad.toNat + bag.toNat) % UInt256.size =
      wad.toNat + bag.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (wad + bag).toNat = wad.toNat + bag.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (wad + bag) bag = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hwadLt : wad.toNat < UInt256.size := wad.val.isLt
    omega
  have rd10099pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by native_decide) (by evm_ov)]
  have rd10099' := by
    simpa [bag, wad] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10100
  have rd10104pre := evm_run rd10100 with [raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10104 := rd10104pre.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd10104 (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endPackX_bagAddSuccess {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hfit : (endPackBagWord σ' I).toNat + (endPackWadWord I).toNat < UInt256.size)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endPackWadWord I, endPackBagWord σ' I, ⟨6599⟩, endPackWadWord I,
        endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6599⟩
      [endPackBagWord σ' I + endPackWadWord I, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k' C' := by
  let bag := endPackBagWord σ' I
  let wad := endPackWadWord I
  have hfit' : wad.toNat + bag.toNat < UInt256.size := by
    dsimp [bag, wad]
    simpa [Nat.add_comm] using hfit
  have haddNat : (wad + bag).toNat = wad.toNat + bag.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit']
  have hlt : UInt256.lt (wad + bag) bag = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd10099pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by native_decide) (by evm_ov)]
  have rd10099' := by
    simpa [bag, wad] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10100
  have rd10108pre := evm_run rd10100 with [
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd6599 := evm_run rd10108pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hcomm :
      endPackWadWord I + endPackBagWord σ' I =
        endPackBagWord σ' I + endPackWadWord I :=
    u256_add_comm (endPackWadWord I) (endPackBagWord σ' I)
  exact ⟨_, _, by simpa [bag, wad, hcomm] using rd6599⟩

theorem endPackX_bagStoreHash {cA gh bl σ σ' σ₀ A I} {g sel bagNew : UInt256}
    {out : ByteArray} {k C : ℕ}
    {cA' : Batteries.RBSet AccountAddress compare}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6599⟩
      [bagNew, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6618⟩
      [⟨0⟩, ⟨64⟩, ⟨32⟩, ⟨64⟩, solcSourceWord I, bagNew, endPackWadWord I,
        endPackReturnPc, sel]
      (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k' C' := by
  have rd6600 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6601 := rd6600.caller (by native_decide) (by evm_ov)
  have rd6603 := rd6601.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd6604 := rd6603.dup2 (by native_decide) (by evm_ov)
  have rd6605pre := rd6604.dup2 (by native_decide) (by evm_ov)
  have rdKeyMem := RD.mstore
    (a := ⟨0⟩) (b := solcSourceWord I)
    (t := [⟨0⟩, solcSourceWord I, bagNew, endPackWadWord I, endPackReturnPc, sel])
    0 (endPackBagStoreKeyMem σ I (endPackAmtWord I) out)
    (UInt256.ofNat 8) rd6605pre (by native_decide) mem_cost
    (endPackBagHashMem_write_key σ I (endPackAmtWord I) out)
    (by native_decide)
    (by evm_ov)
  have rd6608 := rdKeyMem.push1 ⟨16⟩ (by native_decide) (by evm_ov)
  have rd6610 := rd6608.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd6611 := rd6610.swap1 (by native_decide) (by evm_ov)
  have rd6612pre := rd6611.dup2 (by native_decide) (by evm_ov)
  have rdHashMem := rd6612pre.mstore 0
    (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8)
    endPackDecode6612Mstore mem_cost
    (endPackBagHashMem_write_slot σ I (endPackAmtWord I) out)
    (by native_decide) (by evm_ov)
  have rd6615 := rdHashMem.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd6616 := rd6615.swap2 (by native_decide) (by evm_ov)
  have rd6617 := rd6616.dup3 (by native_decide) (by evm_ov)
  have rd6618pre := rd6617.swap1 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd6618pre⟩

theorem endPackX_bagStoreAtHash {cA gh bl σ σ' σ₀ A I} {g sel bagNew : UInt256}
    {out : ByteArray} {k C : ℕ}
    {cA' : Batteries.RBSet AccountAddress compare}
    (hperm : I.perm = true)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6618⟩
      [⟨0⟩, ⟨64⟩, ⟨32⟩, ⟨64⟩, solcSourceWord I, bagNew, endPackWadWord I,
        endPackReturnPc, sel]
      (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6623⟩
      [⟨64⟩, solcSourceWord I, ⟨32⟩, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', sstoreAccountMap I.codeOwner σ' (endPackBagSlot I) bagNew) k' C' := by
  have rdSlot := h.keccak256 0 (endPackBagSlot I) (UInt256.ofNat 8)
    (by native_decide) mem_cost (endPackBagStoreSlotMem_slot σ I (endPackAmtWord I) out)
    (by native_decide) (by evm_ov)
  have rd6620 := rdSlot.swap4 (by native_decide) (by evm_ov)
  have rd6621 := rd6620.swap1 (by native_decide) (by evm_ov)
  have rdSstorePrefix := rd6621.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdStoredRaw⟩ := rdSstorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rdStoredRaw⟩

theorem endPackX_bagStore {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6599⟩
      [endPackBagWord σ' I + endPackWadWord I, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6623⟩
      [⟨64⟩, solcSourceWord I, ⟨32⟩, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', sstoreAccountMap I.codeOwner σ' (endPackBagSlot I)
        (endPackBagWord σ' I + endPackWadWord I)) k' C' := by
  obtain ⟨_, _, rdHash⟩ :=
    endPackX_bagStoreHash (bagNew := endPackBagWord σ' I + endPackWadWord I) h
  obtain ⟨_, _, rdStored⟩ :=
    endPackX_bagStoreAtHash (bagNew := endPackBagWord σ' I + endPackWadWord I)
      hperm rdHash
  exact ⟨_, _, rdStored⟩

theorem endPackX_bagLogReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σ : AccountMap} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨6623⟩
      [⟨64⟩, solcSourceWord I, ⟨32⟩, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagStoreSlotMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have rd6627pre := evm_run h with [
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (mloadFreePtrValue
        (by rw [endPackBagStoreSlotMem_size σ I (endPackAmtWord I) out]; decide)
        (by decide) (endPackBagStoreSlotMem_read64 σ I (endPackAmtWord I) out))
      (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdLogMem := rd6627pre.mstore 0
    (endPackLogDataMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6632pre := evm_run rdLogMem with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (mloadFreePtrValue
        (by rw [endPackLogDataMem_size σ I (endPackAmtWord I) out]; decide)
        (by decide) (endPackLogDataMem_read64 σ I (endPackAmtWord I) out))
      (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd6665 := rd6632pre.pushConst
    (⟨0x47a981d8cbc0f6df64c9be4ce0a423071a088bd46c549bbd11a4d566e031fe0c⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd6672pre := evm_run rd6665 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLog := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0x47a981d8cbc0f6df64c9be4ce0a423071a088bd46c549bbd11a4d566e031fe0c⟩)
    (d := solcSourceWord I)
    (t := [endPackWadWord I, endPackReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd6672pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop := RD.pop (a := endPackWadWord I) (t := [endPackReturnPc, sel])
    rdLog (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endPackReturnPc) (t := [sel]) rdPop
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endPackReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem endPackX_bagStoreReturn {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6599⟩
      [endPackBagWord σ' I + endPackWadWord I, endPackWadWord I, endPackReturnPc, sel]
      (endPackBagHashMem σ I (endPackAmtWord I) out) (UInt256.ofNat 8) out
      (cA', σ') k C) :
    RDret endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cA', sstoreAccountMap I.codeOwner σ' (endPackBagSlot I)
        (endPackBagWord σ' I + endPackWadWord I))
      ByteArray.empty := by
  obtain ⟨_, _, rdStored⟩ := endPackX_bagStore hperm h
  exact endPackX_bagLogReturn (σ := σ) (out := out) hperm rdStored

theorem evalStorageRef_endPack_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endPackStore I } evm
      debtRef = .ok ({ base := "debt", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]

theorem evalExpr_endPack_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
      (.storage debtRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endPackStore I })
    (slot := debtRef)
    (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := by simp [endPackStore, debtRef])
    (her := evalStorageRef_endPack_debt evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨11⟩)

theorem evalExpr_endPack_debt_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endPackStore I } evm
        (.storage debtRef) = .ok (.int 0) := by
    simpa [hdebt] using evalExpr_endPack_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endPackStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endPack_debt_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endPackStore I } evm
        (.storage debtRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) :=
    evalExpr_endPack_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endPackStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  apply hdebt
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem evalStorageRef_endPack_vat {locals : Store} (_hbase : locals.get? "vat" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vatRef = .ok ({ base := "vat", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]

theorem evalExpr_endPack_vat {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨1⟩)
    (hbase := hbase)
    (her := evalStorageRef_endPack_vat hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨1⟩)

theorem evalStorageRef_endPack_vow {locals : Store} (_hbase : locals.get? "vow" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vowRef = .ok ({ base := "vow", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]

theorem evalExpr_endPack_vow {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := vowRef)
    (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨4⟩)
    (hbase := hbase)
    (her := evalStorageRef_endPack_vow hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨4⟩)

theorem evalStorageRef_endPack_bag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (_hbase : locals.get? "bag" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (bagRef sender) = .ok (endPackEvaledBagRef I) := by
  simp [evalStorageRef, evalStorageRefStep, bagRef, sender, envValue, endPackEvaledBagRef,
    endPackBagKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_endPack_bag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hbase : locals.get? "bag" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := bagRef sender)
    (er := endPackEvaledBagRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endPackBagSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endPack_bag evm I hbase hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endPackBagSlot I))

theorem endPackAssignBag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (bagNew : UInt256)
    (hbase : locals.get? "bag" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bagRef sender) (.int (Int.ofNat bagNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endPackPostState evm I bagNew) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endPackBagSlot I))
      (hbase := hbase)
      (her := evalStorageRef_endPack_bag evm I hbase hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endPackPostState] using
    endStorageLocStore_uint256 evm (endPackBagSlot I) bagNew

theorem endPackTailReverts_bagAddOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)).toNat +
          (endPackWadWord I).toNat) :
    ExecBlock config { contract := contract, locals := endPackStoreMove I } evm
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ]
      .reverted := by
  let bagWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)
  have hbase : (endPackStoreMove I).get? "bag" = none := by
    simp [endPackStoreMove, endPackStoreAmt, endPackStore]
  have hbag :
      evalExpr? config { contract := contract, locals := endPackStoreMove I } evm
        (.storage (bagRef sender)) = .ok (.int (Int.ofNat bagWord.toNat)) := by
    simpa [bagWord] using evalExpr_endPack_bag evm I hbase hsrc
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStoreMove I } evm
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStoreMove, endPackStoreAmt, endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endPackStoreMove I)
        (name := "wad") (value := endPackWadWord I)
        (by
          rw [endPackStoreMove, endPackStoreAmt, endPackStore,
            store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
            store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endPackStoreMove I } evm
        [.storage (bagRef sender), .var "wad"] =
          .ok [.int (Int.ofNat bagWord.toNat),
            .int (Int.ofNat (endPackWadWord I).toNat)] := by
    simp [evalExprs?, hbag, hwad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat bagWord.toNat),
            .int (Int.ofNat (endPackWadWord I).toNat)] =
        some (endUintBinaryLocals bagWord (endPackWadWord I)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endPackStoreMove I } evm
        (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew")
        .reverted := by
    have hbody :=
      endExecAddFunctionRevert (evm := evm) (x := bagWord) (y := endPackWadWord I) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := endPackStoreMove I })
      (evm := evm) (name := "add") (retVar := "bagNew")
      (args := [.storage (bagRef sender), .var "wad"])
      (argVals :=
        [.int (Int.ofNat bagWord.toNat),
          .int (Int.ofNat (endPackWadWord I).toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals bagWord (endPackWadWord I))
      hargs (by rfl) hbind hbody
  exact ExecBlock.consRevert haddStmt

theorem endPackTailReturns (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hfit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)).toNat +
          (endPackWadWord I).toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := endPackStoreMove I } evm
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ]
      (.ok
        { contract := contract,
          locals :=
            endPackStoreBagNew I
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I) +
                endPackWadWord I) }
        (endPackPostState evm I
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I) +
            endPackWadWord I))) := by
  let bagWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)
  let bagNew := bagWord + endPackWadWord I
  have hbaseMove : (endPackStoreMove I).get? "bag" = none := by
    simp [endPackStoreMove, endPackStoreAmt, endPackStore]
  have hbag :
      evalExpr? config { contract := contract, locals := endPackStoreMove I } evm
        (.storage (bagRef sender)) = .ok (.int (Int.ofNat bagWord.toNat)) := by
    simpa [bagWord] using evalExpr_endPack_bag evm I hbaseMove hsrc
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStoreMove I } evm
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStoreMove, endPackStoreAmt, endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endPackStoreMove I)
        (name := "wad") (value := endPackWadWord I)
        (by
          rw [endPackStoreMove, endPackStoreAmt, endPackStore,
            store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
            store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endPackStoreMove I } evm
        [.storage (bagRef sender), .var "wad"] =
          .ok [.int (Int.ofNat bagWord.toNat),
            .int (Int.ofNat (endPackWadWord I).toNat)] := by
    simp [evalExprs?, hbag, hwad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat bagWord.toNat),
            .int (Int.ofNat (endPackWadWord I).toNat)] =
        some (endUintBinaryLocals bagWord (endPackWadWord I)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endPackStoreMove I } evm
        (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew")
        (.ok { contract := contract, locals := endPackStoreBagNew I bagNew } evm) := by
    have hbody :=
      endExecAddFunctionReturn (evm := evm) (x := bagWord) (y := endPackWadWord I)
        (sum := bagNew) rfl hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endPackStoreMove I })
      (evm := evm) (name := "add") (retVar := "bagNew")
      (args := [.storage (bagRef sender), .var "wad"])
      (argVals :=
        [.int (Int.ofNat bagWord.toNat),
          .int (Int.ofNat (endPackWadWord I).toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals bagWord (endPackWadWord I))
      hargs (by rfl) hbind hbody
    simpa [endPackStoreBagNew, resumeAfterInternalCall, collapseReturns, bagNew] using hstmt
  have hbagNew :
      evalExpr? config { contract := contract, locals := endPackStoreBagNew I bagNew } evm
        (.var "bagNew") = .ok (.int (Int.ofNat bagNew.toNat)) := by
    simpa [endPackStoreBagNew] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endPackStoreBagNew I bagNew)
        (name := "bagNew") (value := bagNew) (by simp [endPackStoreBagNew])
  have hassign :
      assignStorageRef? config { contract := contract, locals := endPackStoreBagNew I bagNew }
        evm .storage (bagRef sender) (.int (Int.ofNat bagNew.toNat)) =
          .ok ({ contract := contract, locals := endPackStoreBagNew I bagNew },
            endPackPostState evm I bagNew) := by
    exact endPackAssignBag evm I bagNew
      (by simp [endPackStoreBagNew, endPackStoreMove, endPackStoreAmt, endPackStore])
      hsrc
  refine ExecBlock.consNormal haddStmt ?_
  exact ExecBlock.consNormal (ExecStmt.assign hbagNew hassign) ExecBlock.nil

theorem endPackVatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endPackVatWord σ I = endPackVatWord τ I := by
  simp [endPackVatWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩]

theorem endPackVatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endPackVatWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endPackVatWord σ I)
  have htarget : endPackVatWord σ I = endPackVatWord τ I :=
    endPackVatWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem endPackVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endPackVatWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endPackVatWord σ I)
  have htarget : endPackVatWord σ I = endPackVatWord τ I :=
    endPackVatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endPackVatAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endPackVatAddr σ I = AccountAddress.ofUInt256 (endPackVatWord σ I) := by
  simpa [endPackVatAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endPackVatWord σ I)).symm

theorem endPackVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hzero

theorem endPackVatCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hne

theorem endPackBodyReverts_debtZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguard :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endPack_debt_ne_false evm0 I hdebtLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endPackStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage debtRef) (.intLit 0))
      (rest :=
        [ .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move" ++
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endPackBodyReverts_mulOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (endPackWadWord I).toNat * endPackRayWord.toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endPack_debt_ne_true evm0 I hdebtLoad
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStore I)
        (name := "wad") (value := endPackWadWord I) (by simp [endPackStore])
  have hray :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.intLit RAY) = .ok (.int (Int.ofNat endPackRayWord.toNat)) := by
    have hRay : RAY = Int.ofNat endPackRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRay]
  have hargs :
      evalExprs? config { contract := contract, locals := endPackStore I } evm0
        [.var "wad", .intLit RAY] =
          .ok [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] := by
    simp [evalExprs?, hwad, hray, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] =
        some (endUintBinaryLocals (endPackWadWord I) endPackRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := endPackStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt") .reverted := by
    have hbody :=
      endExecMulFunctionRevert (evm := evm0)
        (x := endPackWadWord I) (y := endPackRayWord) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := endPackStore I })
      (evm := evm0) (name := "mul") (retVar := "amt")
      (args := [.var "wad", .intLit RAY])
      (argVals :=
        [.int (Int.ofNat (endPackWadWord I).toNat),
          .int (Int.ofNat endPackRayWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals (endPackWadWord I) endPackRayWord)
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        packTransition.body .reverted := by
    simp only [packTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hmulStmt
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endPackBodyReverts_moveNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endPack_debt_ne_true evm0 I hdebtLoad
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStore I)
        (name := "wad") (value := endPackWadWord I) (by simp [endPackStore])
  have hray :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.intLit RAY) = .ok (.int (Int.ofNat endPackRayWord.toNat)) := by
    have hRay : RAY = Int.ofNat endPackRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRay]
  have hargs :
      evalExprs? config { contract := contract, locals := endPackStore I } evm0
        [.var "wad", .intLit RAY] =
          .ok [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] := by
    simp [evalExprs?, hwad, hray, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] =
        some (endUintBinaryLocals (endPackWadWord I) endPackRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := endPackStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := endPackStoreAmt I } evm0) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm0)
        (x := endPackWadWord I) (y := endPackRayWord) (prod := endPackAmtWord I)
        rfl hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endPackStore I })
      (evm := evm0) (name := "mul") (retVar := "amt")
      (args := [.var "wad", .intLit RAY])
      (argVals :=
        [.int (Int.ofNat (endPackWadWord I).toNat),
          .int (Int.ofNat endPackRayWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals (endPackWadWord I) endPackRayWord)
      hargs (by rfl) hbind hbody
    simpa [endPackStoreAmt, resumeAfterInternalCall, collapseReturns] using hstmt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endPackStoreAmt I).get? "vat" = none := by
      simp [endPackStoreAmt, endPackStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endPackStoreAmt I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endPackVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardMove :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := endPackStoreAmt I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm0)
        (locals := endPackStoreAmt I) (receiver := .storage vatRef)
        (retVar := "_move") (name := "move") (sendVal := 0)
        (args := [sender, vowAddr, .var "amt"]) (perm := true)
        hguardMove
  have hmoveWithTail :
      ExecBlock config { contract := contract, locals := endPackStoreAmt I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move" ++
          [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
            .assign .storage (bagRef sender) (.var "bagNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      hmoveBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        packTransition.body .reverted := by
    simp only [packTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    simpa using hmoveWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endPackBodyReverts_moveCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "move" 0
        [.address I.source, .address (endPackVowAddr σ I),
          .int (Int.ofNat (endPackAmtWord I).toNat)]
        (false, evmMove, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endPack_debt_ne_true evm0 I hdebtLoad
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStore I)
        (name := "wad") (value := endPackWadWord I) (by simp [endPackStore])
  have hray :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.intLit RAY) = .ok (.int (Int.ofNat endPackRayWord.toNat)) := by
    have hRay : RAY = Int.ofNat endPackRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRay]
  have hmulArgs :
      evalExprs? config { contract := contract, locals := endPackStore I } evm0
        [.var "wad", .intLit RAY] =
          .ok [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] := by
    simp [evalExprs?, hwad, hray, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] =
        some (endUintBinaryLocals (endPackWadWord I) endPackRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := endPackStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := endPackStoreAmt I } evm0) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm0)
        (x := endPackWadWord I) (y := endPackRayWord) (prod := endPackAmtWord I)
        rfl hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endPackStore I })
      (evm := evm0) (name := "mul") (retVar := "amt")
      (args := [.var "wad", .intLit RAY])
      (argVals :=
        [.int (Int.ofNat (endPackWadWord I).toNat),
          .int (Int.ofNat endPackRayWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals (endPackWadWord I) endPackRayWord)
      hmulArgs (by rfl) hbind hbody
    simpa [endPackStoreAmt, resumeAfterInternalCall, collapseReturns] using hstmt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endPackStoreAmt I).get? "vat" = none := by
      simp [endPackStoreAmt, endPackStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endPackStoreAmt I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardMove :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hsender :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evm0, initState, pure]
  have hvow :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        vowAddr = .ok (.address (endPackVowAddr σ I)) := by
    have hbase : (endPackStoreAmt I).get? "vow" = none := by
      simp [endPackStoreAmt, endPackStore]
    simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow (locals := endPackStoreAmt I) evm0 hbase
  have hamt :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.var "amt") = .ok (.int (Int.ofNat (endPackAmtWord I).toNat)) := by
    simpa [endPackStoreAmt] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStoreAmt I)
        (name := "amt") (value := endPackAmtWord I) (by simp [endPackStoreAmt])
  have hmoveArgs :
      evalExprs? config { contract := contract, locals := endPackStoreAmt I } evm0
        [sender, vowAddr, .var "amt"] =
          .ok [.address I.source, .address (endPackVowAddr σ I),
            .int (Int.ofNat (endPackAmtWord I).toNat)] := by
    simp [evalExprs?, hsender, hvow, hamt, EvalResult.bind, bind, pure]
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := endPackStoreAmt I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmMove)
        (locals := endPackStoreAmt I) (receiver := .storage vatRef)
        (retVar := "_move") (name := "move") (target := endPackVatAddr σ I)
        (sendVal := 0) (args := [sender, vowAddr, .var "amt"])
        (argVals :=
          [.address I.source, .address (endPackVowAddr σ I),
            .int (Int.ofNat (endPackAmtWord I).toNat)])
        (out := out) (perm := true)
        hguardMove hreceiver hmoveArgs hcall
  have hmoveWithTail :
      ExecBlock config { contract := contract, locals := endPackStoreAmt I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move" ++
          [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
            .assign .storage (bagRef sender) (.var "bagNew") ])
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      hmoveBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        packTransition.body .reverted := by
    simp only [packTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    simpa using hmoveWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endPackPrefixMoveSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "move" 0
        [.address I.source, .address (endPackVowAddr σ I),
          .int (Int.ofNat (endPackAmtWord I).toNat)]
        (true, evmMove, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endPackStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
          .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
        checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move")
      (.ok { contract := contract, locals := endPackStoreMove I } evmMove) := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endPack_debt_ne_true evm0 I hdebtLoad
  have hwad :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endPackWadWord I).toNat)) := by
    simpa [endPackStore, endPackWadValue] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStore I)
        (name := "wad") (value := endPackWadWord I) (by simp [endPackStore])
  have hray :
      evalExpr? config { contract := contract, locals := endPackStore I } evm0
        (.intLit RAY) = .ok (.int (Int.ofNat endPackRayWord.toNat)) := by
    have hRay : RAY = Int.ofNat endPackRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRay]
  have hmulArgs :
      evalExprs? config { contract := contract, locals := endPackStore I } evm0
        [.var "wad", .intLit RAY] =
          .ok [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] := by
    simp [evalExprs?, hwad, hray, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endPackWadWord I).toNat),
            .int (Int.ofNat endPackRayWord.toNat)] =
        some (endUintBinaryLocals (endPackWadWord I) endPackRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := endPackStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := endPackStoreAmt I } evm0) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm0)
        (x := endPackWadWord I) (y := endPackRayWord) (prod := endPackAmtWord I)
        rfl hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endPackStore I })
      (evm := evm0) (name := "mul") (retVar := "amt")
      (args := [.var "wad", .intLit RAY])
      (argVals :=
        [.int (Int.ofNat (endPackWadWord I).toNat),
          .int (Int.ofNat endPackRayWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals (endPackWadWord I) endPackRayWord)
      hmulArgs (by rfl) hbind hbody
    simpa [endPackStoreAmt, resumeAfterInternalCall, collapseReturns] using hstmt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endPackStoreAmt I).get? "vat" = none := by
      simp [endPackStoreAmt, endPackStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endPackStoreAmt I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardMove :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hsender :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evm0, initState, pure]
  have hvow :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        vowAddr = .ok (.address (endPackVowAddr σ I)) := by
    have hbase : (endPackStoreAmt I).get? "vow" = none := by
      simp [endPackStoreAmt, endPackStore]
    simpa [vowAddr, evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow (locals := endPackStoreAmt I) evm0 hbase
  have hamt :
      evalExpr? config { contract := contract, locals := endPackStoreAmt I } evm0
        (.var "amt") = .ok (.int (Int.ofNat (endPackAmtWord I).toNat)) := by
    simpa [endPackStoreAmt] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endPackStoreAmt I)
        (name := "amt") (value := endPackAmtWord I) (by simp [endPackStoreAmt])
  have hmoveArgs :
      evalExprs? config { contract := contract, locals := endPackStoreAmt I } evm0
        [sender, vowAddr, .var "amt"] =
          .ok [.address I.source, .address (endPackVowAddr σ I),
            .int (Int.ofNat (endPackAmtWord I).toNat)] := by
    simp [evalExprs?, hsender, hvow, hamt, EvalResult.bind, bind, pure]
  have hmoveBlock :
      ExecBlock config { contract := contract, locals := endPackStoreAmt I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move")
        (.ok { contract := contract, locals := endPackStoreMove I } evmMove) := by
    have hdec : config.externalABI.decode? "move" out = some [] := by
      simp [config, externalABI, decodeVoid?]
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmMove)
      (locals := endPackStoreAmt I) (receiver := .storage vatRef)
      (retVar := "_move") (name := "move") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [sender, vowAddr, .var "amt"])
      (argVals :=
        [.address I.source, .address (endPackVowAddr σ I),
          .int (Int.ofNat (endPackAmtWord I).toNat)])
      (out := out) (perm := true) (value := [])
      hguardMove hreceiver hmoveArgs hcall hdec
    simpa [checkedExternalCallStmts, endPackStoreMove, collapseReturns] using hblock
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, vowAddr, .var "amt"] "_move")
        (.ok { contract := contract, locals := endPackStoreMove I } evmMove) := by
    simp only [nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    simpa using hmoveBlock
  simpa using hblock

theorem endPackBodyReverts_bagAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "move" 0
        [.address I.source, .address (endPackVowAddr σ I),
          .int (Int.ofNat (endPackAmtWord I).toNat)]
        (true, evmMove, out) true)
    (hsrcMove : evmMove.executionEnv.source = I.source)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner (endPackBagSlot I)).toNat +
          (endPackWadWord I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, vowAddr, .var "amt"] "_move")
        (.ok { contract := contract, locals := endPackStoreMove I } evmMove) := by
    simpa [evm0] using
      endPackPrefixMoveSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmMove := evmMove) (out := out)
        hwv hdebt hfit hcodeSize hcall
  have htail :=
    endPackTailReverts_bagAddOverflow evmMove I hsrcMove hover
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        packTransition.body .reverted := by
    have happ := execBlock_append
      (s2 :=
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      hprefix htail
    simpa [packTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endPackBodyReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endPackDebtWord σ I ≠ ⟨0⟩)
    (hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "move" 0
        [.address I.source, .address (endPackVowAddr σ I),
          .int (Int.ofNat (endPackAmtWord I).toNat)]
        (true, evmMove, out) true)
    (hsrcMove : evmMove.executionEnv.source = I.source)
    (hfitAdd :
      (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner (endPackBagSlot I)).toNat +
          (endPackWadWord I).toNat <
        UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endPackStore I) packTransition.body
      (.returned
        { contract := contract,
          locals :=
            endPackStoreBagNew I
              (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner (endPackBagSlot I) +
                endPackWadWord I) }
        (endPackPostState evmMove I
          (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner (endPackBagSlot I) +
            endPackWadWord I))
        none) := by
  intro evm0
  let bagWord := Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner (endPackBagSlot I)
  let bagNew := bagWord + endPackWadWord I
  have hprefix :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, vowAddr, .var "amt"] "_move")
        (.ok { contract := contract, locals := endPackStoreMove I } evmMove) := by
    simpa [evm0] using
      endPackPrefixMoveSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmMove := evmMove) (out := out)
        hwv hdebt hfit hcodeSize hcall
  have htail :=
    endPackTailReturns evmMove I hsrcMove hfitAdd
  have hblock :
      ExecBlock config { contract := contract, locals := endPackStore I } evm0
        packTransition.body
        (.ok { contract := contract, locals := endPackStoreBagNew I bagNew }
          (endPackPostState evmMove I bagNew)) := by
    have happ := execBlock_append
      (s2 :=
        [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
          .assign .storage (bagRef sender) (.var "bagNew") ])
      hprefix htail
    simpa [packTransition, List.append_assoc, bagWord, bagNew] using happ
  simpa [ExecTransitionBody, evm0, bagWord, bagNew] using ExecFuncBody.execBlockOK hblock

theorem endDecode_pack_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (packTransition.params.map Param.name)
      (transitionSignature packTransition).paramTypes I.calldata = some (endPackStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["wad"] [uint256] I.calldata = _
  simpa [config, endPackStore, endPackWadValue, endPackWadWord, uint256, uint256Int]
    using endDecode_legacyUint256_ok (cd := I.calldata) (x := "wad") hsz36

theorem endDecode_pack_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (packTransition.params.map Param.name)
      (transitionSignature packTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["wad"] [uint256] I.calldata = none
  simpa [config, uint256, uint256Int] using
    endDecode_legacyUint256_none_short (cd := I.calldata) (x := "wad") hsz4 hshort

theorem endDispatchPack {I : ExecutionEnv}
    (hsel : selIs I (selectorOf packTransition)) :
    dispatchMsg contract I.calldata = some packTransition := by
  have hsel' : selIs I endPackConcreteSelector := by
    simpa [endPackSelectorBytes, endPackConcreteSelector] using hsel
  have hcd : I.calldata.extract 0 4 = endPackConcreteSelector :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some packTransition
  unfold transitions
  simp [dispatchList, hcd, endPackConcreteSelector, selectorBytes]
  native_decide

theorem endReachPackBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endPackConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endPackEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x6ea42555⟩ :=
    endSelWord_eq_of_beq I hsz 0x6e 0xa4 0x25 0x55 ⟨0x6ea42555⟩
      (by native_decide) (by simpa [selIs, endPackConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup294FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup294FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup294FirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endPackEntryPc 1 hfirst
    (fun j hj => endGroup294ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endPackX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endPackEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endPackBodyPc
      [endPackWadWord I, endPackReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endPackEntryPc) (ret := endPackReturnPc)
    (decoded := endPackDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endPackDecodedPc) (ret := endPackReturnPc)
    (routine := endPackBodyPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endPackWadWord, calldataWord] using hroutine⟩

theorem endPackX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endPackEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endPackEntryPc) (ret := endPackReturnPc)
    (decoded := endPackDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endPackBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some packTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endPackEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endPackX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_pack_none_short hsz4 hshort)

theorem endPackBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf packTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endPackConcreteSelector := by
    simpa [endPackSelectorBytes, endPackConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endPackConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some packTransition :=
    endDispatchPack hsel
  have hreach := endReachPackBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_pack_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endPackX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hdebtCouple : endPackDebtWord σ_evm I = endPackDebtWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebt : endPackDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : endPackDebtWord σ_solm I = ⟨0⟩ := by
        rw [← hdebtCouple]
        exact hdebt
      have hbody :
          ExecTransitionBody config contract evmSolm (endPackStore I)
            packTransition.body .reverted := by
        simpa [evmSolm] using
          endPackBodyReverts_debtZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hdebtSolm
      exact (endPackX_debtZero (g := Sat256.ofUInt256 g) hdebt hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdebtSolm : endPackDebtWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebt (by rw [hdebtCouple, hbad])
      obtain ⟨_, _, hmulEntry⟩ :=
        endPackX_mulEntry (g := Sat256.ofUInt256 g) hdebt hbodyReach
      by_cases hover : UInt256.size ≤ (endPackWadWord I).toNat * endPackRayWord.toNat
      · have hbody :
            ExecTransitionBody config contract evmSolm (endPackStore I)
              packTransition.body .reverted := by
          simpa [evmSolm] using
            endPackBodyReverts_mulOverflow
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hdebtSolm hover
        exact (endPackX_mulOverflow (g := Sat256.ofUInt256 g) hover hmulEntry)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hfit : (endPackWadWord I).toNat * endPackRayWord.toNat < UInt256.size :=
          Nat.lt_of_not_ge hover
        obtain ⟨_, _, hmoveStart⟩ :=
          endPackX_mulReturns (g := Sat256.ofUInt256 g) hfit hmulEntry
        by_cases hvatCode :
            Reasoning.Theory.extCodeSizeWord σ_evm (endPackVatWord σ_evm I) =
              ⟨0⟩
        · have hvatCodeSolm :
              Reasoning.Theory.extCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) = ⟨0⟩ :=
            endPackVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract evmSolm (endPackStore I)
                packTransition.body .reverted := by
            simpa [evmSolm] using
              endPackBodyReverts_moveNoCode
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hwv hdebtSolm hfit hvatCodeSolm
          exact (endPackX_moveNoCode (g := Sat256.ofUInt256 g) hmoveStart hvatCode)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hvatCodeNE :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (endPackVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
          have hvatCodeSolmNE :
              Reasoning.Theory.extCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) ≠ ⟨0⟩ :=
            endPackVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
          obtain ⟨gasWord, _, _, hcallReady⟩ :=
            endPackX_moveCallReady (g := Sat256.ofUInt256 g) hmoveStart hvatCodeNE
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd6552, hout⟩ :=
              endPackX_movePostCall hcallReady hdepthLt
            rcases hΘ with ⟨g'', A', hΘeq⟩
            have hdepthNe :
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
                  1024 := by
              intro hbad
              have hbadI : I.depth = 1024 := by
                simpa [initState] using hbad
              have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
              omega
            have htgt :
                EVM.address (endPackVatAddr σ_evm I) =
                  AccountAddress.ofUInt256 (endPackVatWord σ_evm I) := by
              have hAddressId (a : AccountAddress) : EVM.address a = a := by
                apply Fin.ext
                show ↑a % EVM.twoPow 160 = ↑a
                rw [Nat.mod_eq_of_lt]
                exact a.isLt
              calc
                EVM.address (endPackVatAddr σ_evm I)
                    = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ_evm I)) := by
                      rw [endPackVatAddr_eq_ofUInt256]
                _ = AccountAddress.ofUInt256 (endPackVatWord σ_evm I) :=
                      hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_evm I))
            have hcallEvm :
                typedCallViaEVM config
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (endPackVatAddr σ_evm I)) "move" 0
                  [.address I.source, .address (endPackVowAddr σ_evm I),
                    .int (Int.ofNat (endPackAmtWord I).toNat)]
                  (z,
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'
                      substate := A'
                      createdAccounts := cA' },
                    out) true := by
              exact callCoincides
                (cfg := config)
                (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (name := "move")
                (args :=
                  [.address I.source, .address (endPackVowAddr σ_evm I),
                    .int (Int.ofNat (endPackAmtWord I).toNat)])
                (tgt := EVM.address (endPackVatAddr σ_evm I))
                (targetWord := endPackVatWord σ_evm I)
                (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
                (z := z) (o := out) (g'' := g'') (callGas := callGas)
                (mem := endPackMoveCalldataMem σ_evm I (endPackAmtWord I) solcFreePtrMem)
                (inOff := endPackMoveOutPtr) (inSize := endPackMoveInSize)
                (callPerm := true)
                hdepthNe htgt
                (endPackMoveEncode_eq σ_evm I (endPackAmtWord I) solcFreePtrMem_size)
                (by simpa [initState, hperm] using hΘeq)
            obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hStateCall⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm)
                (by simp [initState]) hAccounts
            have hVatAddr : endPackVatAddr σ_evm I = endPackVatAddr σ_solm I := by
              simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccounts]
            have hVowWord : endPackVowWord σ_evm I = endPackVowWord σ_solm I := by
              simp [endPackVowWord, endSlotWord, solcSlotWord,
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩]
            have hVowAddr : endPackVowAddr σ_evm I = endPackVowAddr σ_solm I := by
              simp [endPackVowAddr, hVowWord]
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endPackVatAddr σ_solm I)) "move" 0
                  [.address I.source, .address (endPackVowAddr σ_solm I),
                    .int (Int.ofNat (endPackAmtWord I).toNat)]
                  (z,
                    { evmSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' },
                    out) true := by
              simpa [evmSolm, hVatAddr, hVowAddr] using hcallSolmRaw
            cases z
            · have hbody :
                  ExecTransitionBody config contract evmSolm (endPackStore I)
                    packTransition.body .reverted := by
                simpa [evmSolm] using
                  endPackBodyReverts_moveCallFailed
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmMove :=
                      { evmSolm with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' })
                    (out := out)
                    hwv hdebtSolm hfit hvatCodeSolmNE (by simpa [evmSolm] using hcallSolm)
              exact (endPackX_moveCallFailed (g := g) rd6552 hout)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · let evmMoveEvm :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ'
                  substate := A'
                  createdAccounts := cA' }
              let evmMoveSolm :=
                { evmSolm with
                  accountMap := σ'_solm
                  substate := A'_solm
                  createdAccounts := cA' }
              have hsrcMove : evmMoveSolm.executionEnv.source = I.source := by
                simp [evmMoveSolm, evmSolm, initState]
              have hbagCouple :
                  endPackBagWord σ' I =
                    Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                      (endPackBagSlot I) := by
                have hload := hStateCall.storageLoad_codeOwner (endPackBagSlot I)
                simpa [evmMoveEvm, evmMoveSolm, initState, Solm.EVM.storageLoad,
                  State.lookupAccount, endPackBagWord, endSlotWord, solcSlotWord] using hload
              obtain ⟨_, _, rdAddEntry⟩ := endPackX_bagAddEntry (g := g) rd6552
              by_cases hoverAdd :
                  UInt256.size ≤
                    (endPackBagWord σ' I).toNat + (endPackWadWord I).toNat
              · have hoverSolm :
                    UInt256.size ≤
                      (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                            (endPackBagSlot I)).toNat +
                        (endPackWadWord I).toNat := by
                  rw [← hbagCouple]
                  exact hoverAdd
                have hbody :
                    ExecTransitionBody config contract evmSolm (endPackStore I)
                      packTransition.body .reverted := by
                  simpa [evmMoveSolm, evmSolm] using
                    endPackBodyReverts_bagAddOverflow
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g)
                      (evmMove := evmMoveSolm) (out := out)
                      hwv hdebtSolm hfit hvatCodeSolmNE
                      (by simpa [evmMoveSolm, evmSolm] using hcallSolm)
                      hsrcMove hoverSolm
                exact (endPackX_bagAddOverflow hoverAdd rdAddEntry)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hfitAdd :
                    (endPackBagWord σ' I).toNat + (endPackWadWord I).toNat <
                      UInt256.size :=
                  Nat.lt_of_not_ge hoverAdd
                have hfitAddSolm :
                    (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                          (endPackBagSlot I)).toNat +
                        (endPackWadWord I).toNat <
                      UInt256.size := by
                  rw [← hbagCouple]
                  exact hfitAdd
                obtain ⟨_, _, rdBagStore⟩ := endPackX_bagAddSuccess hfitAdd rdAddEntry
                have hret := endPackX_bagStoreReturn hperm rdBagStore
                have hbagNewCouple :
                    endPackBagWord σ' I + endPackWadWord I =
                      Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                          (endPackBagSlot I) +
                        endPackWadWord I := by
                  rw [hbagCouple]
                have hbody :
                    ExecTransitionBody config contract evmSolm (endPackStore I)
                      packTransition.body
                      (.returned
                        { contract := contract,
                          locals :=
                            endPackStoreBagNew I
                              (Solm.EVM.storageLoad evmMoveSolm
                                  evmMoveSolm.executionEnv.codeOwner (endPackBagSlot I) +
                                endPackWadWord I) }
                        (endPackPostState evmMoveSolm I
                          (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                              (endPackBagSlot I) +
                            endPackWadWord I))
                        none) := by
                  simpa [evmMoveSolm, evmSolm] using
                    endPackBodyReturns
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g)
                      (evmMove := evmMoveSolm) (out := out)
                      hwv hdebtSolm hfit hvatCodeSolmNE
                      (by simpa [evmMoveSolm, evmSolm] using hcallSolm)
                      hsrcMove hfitAddSolm
                exact hret.reEquivExecutionGenEVMStateEquiv
                  (evm'_evm :=
                    endPackPostState evmMoveEvm I (endPackBagWord σ' I + endPackWadWord I))
                  (evm'_solm :=
                    endPackPostState evmMoveSolm I
                      (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                          (endPackBagSlot I) +
                        endPackWadWord I))
                  hcode hdispatch hdecode hbody
                  (by
                    simp [evmMoveEvm, endPackPostState, initState, storageStore_createdAccounts])
                  (by
                    simpa [evmMoveEvm, endPackPostState, initState, storageStore_accountMap] using
                      accountMapEquiv.refl
                        (sstoreAccountMap I.codeOwner σ' (endPackBagSlot I)
                          (endPackBagWord σ' I + endPackWadWord I)))
                  (by
                    simpa [evmMoveEvm, evmMoveSolm, endPackPostState, hbagNewCouple] using
                      hStateCall.storageStore_codeOwner (endPackBagSlot I) hbagNewCouple)
                  (by
                    simpa [packTransition] using
                      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                        (dvs := []) rfl (by native_decide) (by native_decide)))
          · rw [not_lt] at hdepthLt
            have hdepthEq : I.depth = 1024 :=
              Fin.ext (by have := I.depth.isLt; omega)
            obtain ⟨_, _, rd6552⟩ :=
              endPackX_moveCallDepthLimit (g := g) hcallReady hdepthEq
            let A_move :=
              (evmSolm.addAccessedAccount (EVM.address (endPackVatAddr σ_solm I))).substate
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endPackVatAddr σ_solm I)) "move" 0
                  [.address I.source, .address (endPackVowAddr σ_solm I),
                    .int (Int.ofNat (endPackAmtWord I).toNat)]
                  (false, { evmSolm with substate := A_move }, ByteArray.empty) true := by
              simpa [evmSolm, A_move] using
                (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                  (tgt := EVM.address (endPackVatAddr σ_solm I)) (name := "move")
                  (args :=
                    [.address I.source, .address (endPackVowAddr σ_solm I),
                      .int (Int.ofNat (endPackAmtWord I).toNat)])
                  (callPerm := true)
                  (endPackMoveEncode_eq σ_solm I (endPackAmtWord I) solcFreePtrMem_size)
                  (by simpa [evmSolm, initState] using hdepthEq))
            have hbody :
                ExecTransitionBody config contract evmSolm (endPackStore I)
                  packTransition.body .reverted := by
              simpa [evmSolm] using
                endPackBodyReverts_moveCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmMove := { evmSolm with substate := A_move })
                  (out := ByteArray.empty)
                  hwv hdebtSolm hfit hvatCodeSolmNE (by simpa [evmSolm] using hcallSolm)
            exact (endPackX_moveCallFailed (g := g) rd6552 (by native_decide))
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endPackBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
