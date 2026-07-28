import Benchmarks.Dss.End.Dispatch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `cash(bytes32,uint256)` transition -/

abbrev endCashConcreteSelector : ByteArray := selectorBytes 0xfe 0x85 0x07 0xc6

abbrev endCashIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endCashIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endCashWadWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

abbrev endCashStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endCashIlkBytes I))).insert
    "wad" (.int (Int.ofNat (endCashWadWord I).toNat))

theorem endCashStore_get_ilk (I : ExecutionEnv) :
    (endCashStore I).get? "ilk" = some (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
  rw [endCashStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endCashIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endCashFixEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "fix", steps := [.mindex (endCashIlkKey I)] }

abbrev endCashFixSlot (I : ExecutionEnv) : UInt256 := fixSlot (endCashIlkKey I)

abbrev endCashFixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endCashFixSlot I) σ I

abbrev endCashVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨1⟩ σ I) solcAddrMask

abbrev endCashThisWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev endCashFluxSelectorWord : UInt256 := ⟨0x6111be2e⟩

abbrev endCashFluxSelectorShifted : UInt256 :=
  ⟨0x6111be2e00000000000000000000000000000000000000000000000000000000⟩

abbrev endCashFluxOutPtr : UInt256 := ⟨128⟩

abbrev endCashFluxInSize : UInt256 := ⟨132⟩

abbrev endCashFluxOutSize : UInt256 := ⟨0⟩

abbrev endCashFluxEndPtr : UInt256 := ⟨260⟩

abbrev endCashAmtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (endCashWadWord I * endCashFixWord σ I) endRayWord

abbrev endCashStoreAmt (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (endCashStore I).insert "amt" (.int (Int.ofNat (endCashAmtWord σ I).toNat))

abbrev endCashStoreFlux (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (endCashStoreAmt σ I).insert "_flux" (collapseReturns [])

abbrev endCashStoreOutNew (σ : AccountMap) (I : ExecutionEnv) (outNew : UInt256) : Store :=
  (endCashStoreFlux σ I).insert "outNew" (.int (Int.ofNat outNew.toNat))

abbrev endCashVatAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endCashVatWord σ I).toNat

abbrev endCashOutKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def endCashOutSlot (I : ExecutionEnv) : UInt256 :=
  outSlot (endCashIlkKey I) (endCashOutKey I)

abbrev endCashOutWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endCashOutSlot I) σ I

abbrev endCashBagKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def endCashBagSlot (I : ExecutionEnv) : UInt256 :=
  bagSlot (endCashBagKey I)

abbrev endCashBagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endCashBagSlot I) σ I

abbrev endCashEvaledOutRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "out", steps := [.mindex (endCashIlkKey I), .mindex (endCashOutKey I)] }

abbrev endCashEvaledBagRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bag", steps := [.mindex (endCashBagKey I)] }

def endCashPostState (evm : EVM.State) (I : ExecutionEnv) (outNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endCashOutSlot I) outNew

def endCashPostAccountMap (σ : AccountMap) (I : ExecutionEnv) (outNew : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (endCashOutSlot I) outNew

abbrev endCashPostBagWord (σ : AccountMap) (I : ExecutionEnv) (outNew : UInt256) :
    UInt256 :=
  endSlotWord (endCashBagSlot I) (endCashPostAccountMap σ I outNew) I

noncomputable def endCashFixHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endCashIlkWord I) ⟨15⟩ solcFreePtrMem

noncomputable def endCashFixHashMem2 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endCashIlkWord I) ⟨15⟩ (endCashFixHashMem I)

noncomputable def endCashFluxSelectorMem (mem : ByteArray) : ByteArray :=
  endCashFluxSelectorShifted.toByteArray.write 0 mem endCashFluxOutPtr.toNat 32

noncomputable def endCashFluxArg0Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (endCashIlkWord I).toByteArray.write 0 (endCashFluxSelectorMem mem)
    (endCashFluxOutPtr + ⟨4⟩).toNat 32

noncomputable def endCashFluxArg1Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (endCashThisWord I).toByteArray.write 0 (endCashFluxArg0Mem I mem)
    (endCashFluxOutPtr + ⟨36⟩).toNat 32

noncomputable def endCashFluxArg2Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (endCashFluxArg1Mem I mem)
    (endCashFluxOutPtr + ⟨68⟩).toNat 32

noncomputable def endCashFluxCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (mem : ByteArray) : ByteArray :=
  amt.toByteArray.write 0 (endCashFluxArg2Mem I mem)
    (endCashFluxOutPtr + ⟨100⟩).toNat 32

noncomputable def endCashFluxPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I))
    endCashFluxOutPtr.toNat
    (min endCashFluxOutSize (UInt256.ofNat out.size)).toNat

abbrev endCashEntryPc : UInt256 := ⟨1274⟩
abbrev endCashReturnPc : UInt256 := ⟨562⟩
abbrev endCashDecodedPc : UInt256 := ⟨1296⟩
abbrev endCashBodyPc : UInt256 := ⟨9609⟩
abbrev endCashFixUndefinedRawWord : UInt256 :=
  ⟨0x456e642f6669782d696c6b2d6e6f742d646566696e6564000000000000000000⟩

abbrev endCashInsufficientBagRawWord : UInt256 :=
  ⟨0x456e642f696e73756666696369656e742d6261672d62616c616e636500000000⟩

theorem endCashFixSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endCashFixSlot I = solcMappingSlot ⟨15⟩ (endCashIlkWord I) := by
  unfold endCashFixSlot endCashIlkKey fixSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endCashOutSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endCashOutSlot I =
      solcMappingSlot (solcMappingSlot ⟨17⟩ (endCashIlkWord I)) (solcSourceWord I) := by
  unfold endCashOutSlot endCashOutKey endCashIlkKey outSlot outIlkSlot mapSlot
    solcMappingSlot
  rw [keyValueToWord_address]
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endCashBagSlot_eq (I : ExecutionEnv) :
    endCashBagSlot I = solcMappingSlot ⟨16⟩ (solcSourceWord I) := by
  unfold endCashBagSlot endCashBagKey bagSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address]

theorem endCashFixHashMem_size (I : ExecutionEnv) :
    (endCashFixHashMem I).size = 96 := by
  simpa [endCashFixHashMem] using
    twoWordHashMem_size_96 (endCashIlkWord I) ⟨15⟩ solcFreePtrMem_size

theorem endCashFixHashMem_read64 (I : ExecutionEnv) :
    (endCashFixHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [endCashFixHashMem] using
    twoWordHashMem_read64 (endCashIlkWord I) ⟨15⟩ solcFreePtrMem_size
      solcFreePtrMem_read64

theorem endCashFixHashMem2_size (I : ExecutionEnv) :
    (endCashFixHashMem2 I).size = 96 := by
  simpa [endCashFixHashMem2] using
    twoWordHashMem_size_96 (endCashIlkWord I) ⟨15⟩ (endCashFixHashMem_size I)

theorem endCashFixHashMem2_read64 (I : ExecutionEnv) :
    (endCashFixHashMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [endCashFixHashMem2] using
    twoWordHashMem_read64 (endCashIlkWord I) ⟨15⟩ (endCashFixHashMem_size I)
      (endCashFixHashMem_read64 I)

theorem endCashFluxSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endCashFluxSelectorMem mem).size = 160 := by
  unfold endCashFluxSelectorMem
  exact toByteArray_write32_size_of_ge mem endCashFluxSelectorShifted
    endCashFluxOutPtr.toNat 96 160 hmem (by native_decide) (by native_decide)
    (by native_decide)

theorem endCashFluxSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCashFluxSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endCashFluxSelectorMem
  rw [toByteArray_write_read_below_of_gap endCashFluxSelectorShifted mem
    endCashFluxOutPtr.toNat 64 (by rw [hmem]) (by native_decide)
    (by rw [hmem]; native_decide), hread64]

theorem endCashFluxArg0Mem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxArg0Mem I mem).size = 164 := by
  unfold endCashFluxArg0Mem
  exact toByteArray_write32_size_of_le (endCashFluxSelectorMem mem) (endCashIlkWord I)
    132 160 164 (endCashFluxSelectorMem_size hmem)
    (by rw [endCashFluxSelectorMem_size hmem]; omega) (by omega)

theorem endCashFluxArg0Mem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCashFluxArg0Mem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endCashFluxArg0Mem
  change ((endCashIlkWord I).toByteArray.write 0 (endCashFluxSelectorMem mem) 132
      32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endCashFluxSelectorMem_size hmem]; omega) (by omega),
    endCashFluxSelectorMem_read64 hmem hread64]

theorem endCashFluxArg1Mem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxArg1Mem I mem).size = 196 := by
  unfold endCashFluxArg1Mem
  exact toByteArray_write32_size_of_ge (endCashFluxArg0Mem I mem) (endCashThisWord I)
    164 164 196 (endCashFluxArg0Mem_size I hmem)
    (by omega) (by native_decide) (by omega)

theorem endCashFluxArg1Mem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCashFluxArg1Mem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endCashFluxArg1Mem
  change ((endCashThisWord I).toByteArray.write 0 (endCashFluxArg0Mem I mem)
      164 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap (endCashThisWord I)
    (endCashFluxArg0Mem I mem) 164 64
    (by rw [endCashFluxArg0Mem_size I hmem]; native_decide)
    (by native_decide) (by rw [endCashFluxArg0Mem_size I hmem]; native_decide),
    endCashFluxArg0Mem_read64 I hmem hread64]

theorem endCashFluxArg2Mem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxArg2Mem I mem).size = 228 := by
  unfold endCashFluxArg2Mem
  exact toByteArray_write32_size_of_ge (endCashFluxArg1Mem I mem) (solcSourceWord I)
    196 196 228 (endCashFluxArg1Mem_size I hmem)
    (by omega) (by native_decide) (by omega)

theorem endCashFluxArg2Mem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCashFluxArg2Mem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endCashFluxArg2Mem
  change ((solcSourceWord I).toByteArray.write 0 (endCashFluxArg1Mem I mem)
      196 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap (solcSourceWord I)
    (endCashFluxArg1Mem I mem) 196 64
    (by rw [endCashFluxArg1Mem_size I hmem]; native_decide)
    (by native_decide) (by rw [endCashFluxArg1Mem_size I hmem]; native_decide),
    endCashFluxArg1Mem_read64 I hmem hread64]

theorem endCashFluxCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).size = 260 := by
  unfold endCashFluxCalldataMem
  exact toByteArray_write32_size_of_ge (endCashFluxArg2Mem I mem) amt
    228 228 260 (endCashFluxArg2Mem_size I hmem)
    (by omega) (by native_decide) (by omega)

theorem endCashFluxCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashFluxCalldataMem
  change (amt.toByteArray.write 0 (endCashFluxArg2Mem I mem) 228 32).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap amt (endCashFluxArg2Mem I mem) 228 64
    (by rw [endCashFluxArg2Mem_size I hmem]; native_decide)
    (by native_decide) (by rw [endCashFluxArg2Mem_size I hmem]; native_decide),
    endCashFluxArg2Mem_read64 I hmem hread64]

theorem endCashFluxPostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    endCashFluxPostCallMem σ I amt out =
      endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I) := by
  unfold endCashFluxPostCallMem
  have hmin : (min endCashFluxOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : endCashFluxOutSize ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
      exact Nat.zero_le _
    simp [endCashFluxOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero out
    (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I))
    0 endCashFluxOutPtr.toNat

theorem endCashFluxPostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashFluxPostCallMem σ I amt out).size = 260 := by
  rw [endCashFluxPostCallMem_eq]
  exact endCashFluxCalldataMem_size σ I amt (endCashFixHashMem2_size I)

theorem endCashFluxPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashFluxPostCallMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endCashFluxPostCallMem_eq]
  exact endCashFluxCalldataMem_read64 σ I amt
    (endCashFixHashMem2_size I) (endCashFixHashMem2_read64 I)

noncomputable def endCashOutInnerHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (endCashIlkWord I) ⟨17⟩ (endCashFluxPostCallMem σ I amt out)

noncomputable def endCashOutHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutInnerHashMem σ I amt out)

theorem endWordAt0Mem_size_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (wordAt0Mem word mem).size = 260 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 260 260 hmem (by omega) (by omega)

theorem endWordAt32Mem_size_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (wordAt32Mem word mem).size = 260 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 260 260 hmem (by omega) (by omega)

theorem endWordAt32Mem_read64_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
    (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem endWordAt32Mem_read0_64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread0 : mem.readWithPadding 0 32 = UInt256.toByteArray key) :
    (wordAt32Mem slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsize : (wordAt32Mem slot mem).size = 260 :=
    endWordAt32Mem_size_260 slot hmem
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (wordAt32Mem slot mem) 0 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize]; omega)]
  have hleft :
      (wordAt32Mem slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
    unfold wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega)]
    exact hread0
  have hright :
      (wordAt32Mem slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt32Mem
    rw [write32_read_back _ _ 32 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
    rw [toByteArray_extract_all]
  rw [hleft, hright]

theorem endTwoWordHashMem_size_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).size = 260 := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32 260 260
    (endWordAt0Mem_size_260 key hmem)
    (by rw [endWordAt0Mem_size_260 key hmem]; omega) (by omega)

theorem endTwoWordHashMem_read64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_260 key hmem]; omega) (by omega)
      (by rw [endWordAt0Mem_size_260 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem endTwoWordHashMem_read0_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_260 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem endTwoWordHashMem_read32_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [endWordAt0Mem_size_260 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem endTwoWordHashMem_read0_64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [endTwoWordHashMem_size_260 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [endTwoWordHashMem_size_260 key slot hmem]; omega),
      endTwoWordHashMem_read0_260 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [endTwoWordHashMem_size_260 key slot hmem]; omega),
      endTwoWordHashMem_read32_260 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem endCashOutInnerHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutInnerHashMem σ I amt out).size = 260 := by
  unfold endCashOutInnerHashMem
  exact endTwoWordHashMem_size_260 (endCashIlkWord I) ⟨17⟩
    (endCashFluxPostCallMem_size σ I amt out)

theorem endCashOutInnerHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutInnerHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashOutInnerHashMem
  exact endTwoWordHashMem_read64_260 (endCashIlkWord I) ⟨17⟩
    (endCashFluxPostCallMem_size σ I amt out)
    (endCashFluxPostCallMem_read64 σ I amt out)

theorem endCashOutInnerHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashOutInnerHashMem σ I amt out).readWithPadding 0 64))) =
      solcMappingSlot ⟨17⟩ (endCashIlkWord I) := by
  unfold endCashOutInnerHashMem
  rw [endTwoWordHashMem_read0_64_260 (endCashIlkWord I) ⟨17⟩
    (endCashFluxPostCallMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (endCashIlkWord I) ⟨17⟩

theorem endCashOutHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutHashMem σ I amt out).size = 260 := by
  unfold endCashOutHashMem
  exact endTwoWordHashMem_size_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutInnerHashMem_size σ I amt out)

theorem endCashOutHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashOutHashMem
  exact endTwoWordHashMem_read64_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutInnerHashMem_size σ I amt out)
    (endCashOutInnerHashMem_read64 σ I amt out)

theorem endCashOutHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashOutHashMem σ I amt out).readWithPadding 0 64))) =
      endCashOutSlot I := by
  rw [endCashOutSlot_eq (I := I) hsz68]
  unfold endCashOutHashMem
  rw [endTwoWordHashMem_read0_64_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutInnerHashMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) (solcMappingSlot ⟨17⟩ (endCashIlkWord I))

noncomputable def endCashOutStoreInnerHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (endCashIlkWord I) ⟨17⟩ (endCashOutHashMem σ I amt out)

noncomputable def endCashOutStoreHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutStoreInnerHashMem σ I amt out)

noncomputable def endCashBagHashMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  wordAt32Mem ⟨16⟩ (endCashOutStoreHashMem σ I amt out)

noncomputable def endCashOutHashMemAfterBag (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  wordAt32Mem (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashBagHashMem σ I amt out)

noncomputable def endCashLogDataMem (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (endCashWadWord I)).write 0
    (endCashOutHashMemAfterBag σ I amt out) 128 32

theorem endCashOutStoreInnerHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutStoreInnerHashMem σ I amt out).size = 260 := by
  unfold endCashOutStoreInnerHashMem
  exact endTwoWordHashMem_size_260 (endCashIlkWord I) ⟨17⟩
    (endCashOutHashMem_size σ I amt out)

theorem endCashOutStoreInnerHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutStoreInnerHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashOutStoreInnerHashMem
  exact endTwoWordHashMem_read64_260 (endCashIlkWord I) ⟨17⟩
    (endCashOutHashMem_size σ I amt out)
    (endCashOutHashMem_read64 σ I amt out)

theorem endCashOutStoreInnerHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashOutStoreInnerHashMem σ I amt out).readWithPadding 0 64))) =
      solcMappingSlot ⟨17⟩ (endCashIlkWord I) := by
  unfold endCashOutStoreInnerHashMem
  rw [endTwoWordHashMem_read0_64_260 (endCashIlkWord I) ⟨17⟩
    (endCashOutHashMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (endCashIlkWord I) ⟨17⟩

theorem endCashOutStoreHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutStoreHashMem σ I amt out).size = 260 := by
  unfold endCashOutStoreHashMem
  exact endTwoWordHashMem_size_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutStoreInnerHashMem_size σ I amt out)

theorem endCashOutStoreHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutStoreHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashOutStoreHashMem
  exact endTwoWordHashMem_read64_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutStoreInnerHashMem_size σ I amt out)
    (endCashOutStoreInnerHashMem_read64 σ I amt out)

theorem endCashOutStoreHashMem_read0 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutStoreHashMem σ I amt out).readWithPadding 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold endCashOutStoreHashMem
  exact endTwoWordHashMem_read0_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutStoreInnerHashMem_size σ I amt out)

theorem endCashOutStoreHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashOutStoreHashMem σ I amt out).readWithPadding 0 64))) =
      endCashOutSlot I := by
  rw [endCashOutSlot_eq (I := I) hsz68]
  unfold endCashOutStoreHashMem
  rw [endTwoWordHashMem_read0_64_260 (solcSourceWord I)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I))
    (endCashOutStoreInnerHashMem_size σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) (solcMappingSlot ⟨17⟩ (endCashIlkWord I))

theorem endCashBagHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashBagHashMem σ I amt out).size = 260 := by
  unfold endCashBagHashMem
  exact endWordAt32Mem_size_260 ⟨16⟩
    (endCashOutStoreHashMem_size σ I amt out)

theorem endCashBagHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashBagHashMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashBagHashMem
  exact endWordAt32Mem_read64_260 ⟨16⟩
    (endCashOutStoreHashMem_size σ I amt out)
    (endCashOutStoreHashMem_read64 σ I amt out)

theorem endCashBagHashMem_slot (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashBagHashMem σ I amt out).readWithPadding 0 64))) =
      endCashBagSlot I := by
  rw [endCashBagSlot_eq]
  unfold endCashBagHashMem
  rw [endWordAt32Mem_read0_64_260 (solcSourceWord I) ⟨16⟩
    (endCashOutStoreHashMem_size σ I amt out)
    (endCashOutStoreHashMem_read0 σ I amt out)]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨16⟩

theorem endCashOutHashMemAfterBag_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutHashMemAfterBag σ I amt out).size = 260 := by
  unfold endCashOutHashMemAfterBag
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le (endCashBagHashMem σ I amt out)
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I)) 32 260 260
    (endCashBagHashMem_size σ I amt out)
    (by rw [endCashBagHashMem_size σ I amt out]; omega) (by omega)
theorem endCashOutHashMemAfterBag_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashOutHashMemAfterBag σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashOutHashMemAfterBag
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [endCashBagHashMem_size σ I amt out]; omega) (by omega)
    (by rw [endCashBagHashMem_size σ I amt out]; omega)]
  exact endCashBagHashMem_read64 σ I amt out

theorem endCashLogDataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashLogDataMem σ I amt out).size = 260 := by
  unfold endCashLogDataMem
  exact toByteArray_write32_size_of_le (endCashOutHashMemAfterBag σ I amt out)
    (endCashWadWord I) 128 260 260
    (endCashOutHashMemAfterBag_size σ I amt out)
    (by rw [endCashOutHashMemAfterBag_size σ I amt out]; omega) (by omega)

theorem endCashLogDataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (amt : UInt256) (out : ByteArray) :
    (endCashLogDataMem σ I amt out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCashLogDataMem
  rw [toByteArray_write_read_below_of_gap (endCashWadWord I)
    (endCashOutHashMemAfterBag σ I amt out) 128 64
    (by rw [endCashOutHashMemAfterBag_size σ I amt out]; omega) (by omega)
    (by rw [endCashOutHashMemAfterBag_size σ I amt out]; native_decide)]
  exact endCashOutHashMemAfterBag_read64 σ I amt out

theorem endCashFluxCalldataMem_read128_4
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 128 4 = fluxSelector := by
  unfold endCashFluxCalldataMem
  rw [show (endCashFluxOutPtr + ⟨100⟩).toNat = 228 by native_decide]
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [endCashFluxArg2Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg2Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg2Mem
  rw [show (endCashFluxOutPtr + ⟨68⟩).toNat = 196 by native_decide]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [endCashFluxArg1Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg1Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg1Mem
  rw [show (endCashFluxOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [endCashFluxArg0Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg0Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg0Mem
  rw [show (endCashFluxOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endCashFluxSelectorMem_size hmem]; omega) (by omega)
    (by rw [endCashFluxSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxSelectorMem endCashFluxOutPtr
  change
    (endCashFluxSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
      fluxSelector
  rw [toByteArray_write_read_window_of_gap endCashFluxSelectorShifted mem 128 0 4
    (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  unfold endCashFluxSelectorShifted fluxSelector selectorBytes
  native_decide

theorem endCashFluxCalldataMem_read132_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 132 32 =
      (endCashIlkWord I).toByteArray := by
  unfold endCashFluxCalldataMem
  rw [show (endCashFluxOutPtr + ⟨100⟩).toNat = 228 by native_decide]
  rw [write32_read_below_len _ _ 228 132 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg2Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg2Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg2Mem
  rw [show (endCashFluxOutPtr + ⟨68⟩).toNat = 196 by native_decide]
  rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg1Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg1Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg1Mem
  rw [show (endCashFluxOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg0Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg0Mem_size I hmem]) (by omega) (by norm_num)]
  unfold endCashFluxArg0Mem
  rw [show (endCashFluxOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
    (by rw [endCashFluxSelectorMem_size hmem]; omega) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endCashFluxCalldataMem_read164_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 164 32 =
      (endCashThisWord I).toByteArray := by
  unfold endCashFluxCalldataMem
  rw [show (endCashFluxOutPtr + ⟨100⟩).toNat = 228 by native_decide]
  rw [write32_read_below_len _ _ 228 164 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg2Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg2Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endCashFluxArg2Mem
  rw [show (endCashFluxOutPtr + ⟨68⟩).toNat = 196 by native_decide]
  rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg1Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg1Mem_size I hmem]) (by omega) (by norm_num)]
  unfold endCashFluxArg1Mem
  rw [show (endCashFluxOutPtr + ⟨36⟩).toNat = 164 by native_decide]
  rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg0Mem_size I hmem]) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endCashFluxCalldataMem_read196_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 196 32 =
      (solcSourceWord I).toByteArray := by
  unfold endCashFluxCalldataMem
  rw [show (endCashFluxOutPtr + ⟨100⟩).toNat = 228 by native_decide]
  rw [write32_read_below_len _ _ 228 196 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg2Mem_size I hmem]) (by omega)
    (by rw [endCashFluxArg2Mem_size I hmem]) (by omega) (by norm_num)]
  unfold endCashFluxArg2Mem
  rw [show (endCashFluxOutPtr + ⟨68⟩).toNat = 196 by native_decide]
  rw [write32_read_prefix_len _ _ 196 32 (by rw [toByteArray_size])
    (by rw [endCashFluxArg1Mem_size I hmem]) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endCashFluxCalldataMem_read228_32
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 228 32 = amt.toByteArray := by
  unfold endCashFluxCalldataMem
  rw [show (endCashFluxOutPtr + ⟨100⟩).toNat = 228 by native_decide]
  rw [write32_read_back _ _ 228 (by rw [toByteArray_size])
    (by rw [endCashFluxArg2Mem_size I hmem])]
  rw [toByteArray_extract_all]

theorem endCashFluxCalldataMem_read128_132
    (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endCashFluxCalldataMem σ I amt mem).readWithPadding 128 132 =
      fluxSelector ++ (endCashIlkWord I).toByteArray ++
        (endCashThisWord I).toByteArray ++ (solcSourceWord I).toByteArray ++
          amt.toByteArray := by
  have hsize : (endCashFluxCalldataMem σ I amt mem).size = 260 :=
    endCashFluxCalldataMem_size σ I amt hmem
  rw [show 132 = 4 + 128 from rfl,
    byteArray_readWithPadding_split (endCashFluxCalldataMem σ I amt mem) 128 4 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (endCashFluxCalldataMem σ I amt mem) 132 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endCashFluxCalldataMem σ I amt mem) 164 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endCashFluxCalldataMem σ I amt mem) 196 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endCashFluxCalldataMem_read128_4 σ I amt hmem,
    endCashFluxCalldataMem_read132_32 σ I amt hmem,
    endCashFluxCalldataMem_read164_32 σ I amt hmem,
    endCashFluxCalldataMem_read196_32 σ I amt hmem,
    endCashFluxCalldataMem_read228_32 σ I amt hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endCashFluxEncode_eq (σ : AccountMap) (I : ExecutionEnv) (amt : UInt256)
    {mem : ByteArray} (hsz68 : 68 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "flux"
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat amt.toNat)] =
      some ((endCashFluxCalldataMem σ I amt mem).readWithPadding
        endCashFluxOutPtr.toNat endCashFluxInSize.toNat) := by
  change config.externalABI.encode? "flux"
      [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
        .address I.source, .int (Int.ofNat amt.toNat)] =
    some ((endCashFluxCalldataMem σ I amt mem).readWithPadding 128 132)
  rw [endCashFluxCalldataMem_read128_132 σ I amt hmem]
  have hbytes : endCashIlkBytes I = EVM.Word.toBytesBE (endCashIlkWord I) := by
    have hlen32 : (endCashIlkBytes I).length = 32 := by
      simpa [endCashIlkBytes] using endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endCashIlkBytes I) = endCashIlkWord I := by
      simpa [endCashIlkBytes, endCashIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega : 36 ≤ I.calldata.size))
    have hto := toBytesBE_bytesToWord_of_length (bs := endCashIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hthisWord : EVM.word ↑I.codeOwner = endCashThisWord I := by
    change UInt256.ofNat I.codeOwner.val = endCashThisWord I
    rfl
  have hsourceWord : EVM.word ↑I.source = solcSourceWord I := by
    change UInt256.ofNat I.source.val = solcSourceWord I
    rfl
  have hamtLt : amt.toNat < EVM.twoPow 256 := amt.val.isLt
  have hamtWord : EVM.word amt.toNat = amt := by
    show UInt256.ofNat amt.toNat = amt
    exact u256_ofNat_toNat _
  have hbytesLen : (EVM.Word.toBytesBE (endCashIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endCashIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, uint256,
    uint256Int, fluxSelector, selectorBytes, hbytes, hbytesLen, hthisWord, hsourceWord,
    hamtLt, hamtWord, zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem RD.endCashFixUndefinedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨9629⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
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
    raw push1 ⟨23⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨23⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endCashFixUndefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨23⟩ endCashFixUndefinedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨23⟩ endCashFixUndefinedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endDecode_cash_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cashTransition.params.map Param.name)
      (transitionSignature cashTransition).paramTypes I.calldata = some (endCashStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "wad"] [bytes32, uint256]
    I.calldata = _
  simpa [config, cashTransition, bytes32, bytes32Width, uint256, uint256Int,
    endCashStore, endCashIlkBytes, endCashWadWord, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (endDecode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "wad") hsz68)

theorem endDecode_cash_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (cashTransition.params.map Param.name)
      (transitionSignature cashTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "wad"] [bytes32, uint256]
    I.calldata = none
  simpa [config, cashTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecode_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "wad") hsz4 hshort)

theorem endReachCashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCashConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endCashEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xfe8507c6⟩ :=
    endSelWord_eq_of_beq I hsz 0xfe 0x85 0x07 0xc6 ⟨0xfe8507c6⟩
      (by native_decide)
      (by simpa [selIs, endCashConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup65FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup65FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup65FirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endCashEntryPc 3 hfirst
    (fun j hj => endGroup65ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

-- GENERALIZES Benchmarks.Dss.End.RD.endFileUintDecodeToRoutine:
-- parameterize the decoded PC and target routine for any unmasked two-word static decoder.
theorem RD.endCashDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endCashDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endCashBodyPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endCashBodyPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd1296 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1297 := rd1296.pop (by native_decide) (by evm_ov)
  have rd1298 := rd1297.dup1 (by native_decide) (by evm_ov)
  have rd1299 := rd1298.calldataload (by native_decide) (by evm_ov)
  have rd1300 := rd1299.swap1 (by native_decide) (by evm_ov)
  have rd1302 := rd1300.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1303 := rd1302.add (by native_decide) (by evm_ov)
  have rd1304 := rd1303.calldataload (by native_decide) (by evm_ov)
  have rd1305 := rd1304.push2 endCashBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endCashBodyPc, endCashDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd1305.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endCashX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCashEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endCashBodyPc
        [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endCashEntryPc) (ret := endCashReturnPc)
    (decoded := endCashDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endCashDecodeToBody
    (code := endBytecode) (ret := endCashReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endCashWadWord, endCashIlkWord] using hroutine⟩

theorem endCashX_fixZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCashBodyPc
      [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endCashIlkWord I
  have hslot : endCashFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endCashFixSlot_eq (I := I) hsz68
  have rd9614pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd9615 := rd9614pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9619pre := evm_run rd9615 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd9620 := rd9619pre.mstore 0 (twoWordHashMem key ⟨15⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9623pre := evm_run rd9620 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨15⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨15⟩ key solcFreePtrMem_size
  have rd9624pre := rd9623pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9625raw⟩ := rd9624pre.sload (by native_decide) (by evm_ov)
  have hfixRaw :
      solcSlotWord σ I (solcMappingSlot ⟨15⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endCashFixWord, endSlotWord] using hfix
  have hfixRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨15⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hfixRaw
  have rd9625zero := rd9625raw
  rw [hfixRaw'] at rd9625zero
  obtain ⟨_, _, rd9625⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9625⟩
        (⟨0⟩ :: endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endCashBodyPc, key] using rd9625zero⟩
  have rd9628pre := rd9625.push2 ⟨9705⟩ (by native_decide) (by evm_ov)
  have rd9629pre := rd9628pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd9629⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9629⟩
        [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd9629pre⟩
  exact RD.endCashFixUndefinedRevert rd9629
    (twoWordHashMem_size_96 key ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCashX_fixNonzeroVatLoaded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCashBodyPc
      [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9709⟩
      (endSlotWord ⟨1⟩ σ I :: endCashWadWord I :: endCashIlkWord I ::
        endCashReturnPc :: sel :: [])
      (twoWordHashMem (endCashIlkWord I) ⟨15⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let key := endCashIlkWord I
  have hslot : endCashFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endCashFixSlot_eq (I := I) hsz68
  have rd9614pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd9615 := rd9614pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9619pre := evm_run rd9615 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd9620 := rd9619pre.mstore 0 (twoWordHashMem key ⟨15⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9623pre := evm_run rd9620 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨15⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨15⟩ key solcFreePtrMem_size
  have rd9624pre := rd9623pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9625raw⟩ := rd9624pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9625⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9625⟩
        (endCashFixWord σ I :: endCashWadWord I :: endCashIlkWord I ::
          endCashReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [endCashBodyPc, key, endCashFixWord, endSlotWord, solcSlotWord, hslot]
        using rd9625raw⟩
  have rd9628 := rd9625.push2 ⟨9705⟩ (by native_decide) (by evm_ov)
  have rd9705 := rd9628.jumpiT (by native_decide) hfix (by jump_dest) (by evm_ov)
  have rd9708 := evm_run rd9705 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd9709raw⟩ := rd9708.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [key, endSlotWord, solcSlotWord] using rd9709raw⟩

theorem endCashX_rmulArgsLoaded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9709⟩
      (endSlotWord ⟨1⟩ σ I :: endCashWadWord I :: endCashIlkWord I ::
        endCashReturnPc :: sel :: [])
      (endCashFixHashMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9724⟩
      (endCashFixWord σ I :: endSlotWord ⟨1⟩ σ I :: endCashWadWord I ::
        endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFixHashMem2 I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let key := endCashIlkWord I
  have hslot : endCashFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endCashFixSlot_eq (I := I) hsz68
  have hmem1 : (endCashFixHashMem I).size = 96 := by
    simpa [endCashFixHashMem, key] using
      twoWordHashMem_size_96 key ⟨15⟩ solcFreePtrMem_size
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCashFixHashMem2 I).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    by
      simpa [endCashFixHashMem2, key] using
        twoWordHashMem_solcMappingSlot ⟨15⟩ key hmem1
  have rd9714pre := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd9714 := rd9714pre.mstore 0
    (wordAt0Mem key (endCashFixHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9718pre := evm_run rd9714 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd9719 := rd9718pre.mstore 0
    (endCashFixHashMem2 I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd9722pre := evm_run rd9719 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9723pre := rd9722pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd9724raw⟩ := rd9723pre.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [key, endCashFixHashMem2, endCashFixWord, endSlotWord, solcSlotWord, hslot]
      using rd9724raw⟩

theorem endCashX_rmulStackReady {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9724⟩
      (endCashFixWord σ I :: endSlotWord ⟨1⟩ σ I :: endCashWadWord I ::
        endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd9736 := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9744 := evm_run rd9736 with [
    raw push4 endCashFluxSelectorWord (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd9745 := RD.address rd9744 (by native_decide) (by evm_ov)
  have rd9754 := evm_run rd9745 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨9758⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd10114 := evm_run rd9754 with [
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endCashVatWord, endCashThisWord, endCashFluxSelectorWord,
      endSlotWord, solcSlotWord, solcAddrMask, u256_land_comm] using rd10114⟩

theorem endCashX_rmulEntry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCashBodyPc
      [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, hvat⟩ := endCashX_fixNonzeroVatLoaded hsz68 hfix h
  obtain ⟨_, _, hargs⟩ := endCashX_rmulArgsLoaded hsz68 (by
    simpa [endCashFixHashMem] using hvat)
  exact endCashX_rmulStackReady hargs

theorem endCashX_rmulMulEntry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨10139⟩, endRayWord, ⟨0⟩,
        endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd10130 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd10130ray := rd10130.pushConst endRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd10170 := evm_run rd10130ray with [
    raw push2 ⟨10139⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endRayWord] using rd10170⟩

theorem endCashX_mulHelperOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem : ByteArray}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ret :: R) mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : R.length + 16 ≤ 1024) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdivNe :
      UInt256.div (x * y) y ≠ x := by
    have hbase := endU256_mul_div_overflow_ne x y hover
    intro hbad
    have hmul : y * x = x * y := by
      simpa using u256_mul_comm y x
    exact hbase (by simpa [hmul] using hbad)
  have hyCond : y ≠ ⟨0⟩ := by
    intro hzero
    have hprodZero : x.toNat * y.toNat = 0 := by
      simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have rd10179 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hyNonzero : UInt256.isZero y = ⟨0⟩ :=
    isZero_eq_zero_of_ne hyCond
  have rd10180 := rd10179.jumpiNT (by native_decide) hyNonzero (by evm_ov)
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
  have rd10194 := rd10192.jumpiT (by native_decide) hyCond (by jump_dest) (by evm_ov)
  have rd10201 := evm_run rd10194 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqCond :
      UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rdFallthrough := rd10201.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem endCashX_mulHelperReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem : ByteArray}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ret :: R) mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (x * y :: R) mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hdiv :
      UInt256.div (x * y) y = x := by
    apply u256_inj
    rw [udiv_toNat]
    have hprod : (x * y).toNat = x.toNat * y.toNat := by
      rw [umul_toNat x y hfit]
    have hyNatNe : y.toNat ≠ 0 := by
      intro hy0
      apply hy
      exact u256_inj hy0
    have hyPos : 0 < y.toNat := Nat.pos_of_ne_zero hyNatNe
    rw [hprod]
    simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat hyPos
  have rd10179 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have hyNonzero : UInt256.isZero y = ⟨0⟩ :=
    isZero_eq_zero_of_ne hy
  have rd10180 := rd10179.jumpiNT (by native_decide) hyNonzero (by evm_ov)
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
  have rd10194 := rd10192.jumpiT (by native_decide) hy (by jump_dest) (by evm_ov)
  have rd10201 := evm_run rd10194 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
    rw [hdiv, u256_eq_refl]
    exact one_ne_zero_uint
  have rd10108 := rd10201.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
  have rdRet := evm_run rd10108 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) hret (by evm_ov)]
  exact ⟨_, _, by simpa using rdRet⟩

theorem endCashX_rmulOverflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hover : UInt256.size ≤ (endCashWadWord I).toNat * (endCashFixWord σ I).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hmul⟩ := endCashX_rmulMulEntry h
  exact endCashX_mulHelperOverflow hover hmul
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCashX_rmulReturns {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endCashFixWord σ I, endCashWadWord I, ⟨9758⟩, solcSourceWord I,
        endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9758⟩
      [endCashAmtWord σ I, solcSourceWord I, endCashThisWord I, endCashIlkWord I,
        endCashFluxSelectorWord, endCashVatWord σ I, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, hmul⟩ := endCashX_rmulMulEntry h
  obtain ⟨_, _, hretMul⟩ :=
    endCashX_mulHelperReturns
      (x := endCashWadWord I) (y := endCashFixWord σ I) (ret := ⟨10139⟩)
      (R := [endRayWord, ⟨0⟩, endCashFixWord σ I, endCashWadWord I, ⟨9758⟩,
        solcSourceWord I, endCashThisWord I, endCashIlkWord I, endCashFluxSelectorWord,
        endCashVatWord σ I, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel])
      hfit hfix hmul (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10146pre := evm_run hretMul with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨10146⟩ (by native_decide) (by evm_ov)]
  have rd10146 := rd10146pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd9758 := evm_run rd10146 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endCashAmtWord, endRayWord] using rd9758⟩

theorem endCashX_fluxExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel amt : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9758⟩
      [amt, solcSourceWord I, endCashThisWord I, endCashIlkWord I,
        endCashFluxSelectorWord, endCashVatWord σ I, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9839⟩
      (endCashVatWord σ I :: endCashVatWord σ I :: ⟨0⟩ :: endCashFluxOutPtr ::
        endCashFluxInSize :: endCashFluxOutPtr :: endCashFluxOutSize ::
        endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endCashFixHashMem2 I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCashFixHashMem2 I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCashFixHashMem2_size I]; decide) (by decide)
      (endCashFixHashMem2_read64 I)
  have hcallMem :
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)).size = 260 :=
    endCashFluxCalldataMem_size σ I amt (endCashFixHashMem2_size I)
  have hcallRead64 :
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endCashFluxCalldataMem_read64 σ I amt
      (endCashFixHashMem2_size I) (endCashFixHashMem2_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorMask :
      UInt256.land endCashFluxSelectorWord (⟨0xffffffff⟩ : UInt256) =
        endCashFluxSelectorWord := by
    native_decide
  have hthisMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endCashThisWord I) = endCashThisWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    unfold endCashThisWord
    have haddr : I.codeOwner.val < UInt256.size :=
      lt_of_lt_of_le I.codeOwner.isLt (show AccountAddress.size ≤ UInt256.size from by decide)
    apply solcAddrMask_clean
    rw [UInt256.toNat_ofNat_of_lt]
    · simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.codeOwner.isLt
    · exact haddr
  have hsourceMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (solcSourceWord I) = solcSourceWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
    exact solcAddrMask_clean (solcSourceWord_canonical I)
  have rd9839 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endCashFluxSelectorMem (endCashFixHashMem2 I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endCashFluxArg0Mem I (endCashFixHashMem2 I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp only [endCashFluxArg0Mem, endCashFluxOutPtr]
        rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat =
          ((⟨128⟩ : UInt256) + ⟨4⟩).toNat from by native_decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endCashFluxArg1Mem I (endCashFixHashMem2 I)) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        rw [hthisMask]
        simp only [endCashFluxArg1Mem, endCashFluxOutPtr]
        rw [show ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨128⟩)).toNat =
          ((⟨128⟩ : UInt256) + ⟨36⟩).toNat from by native_decide])
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
    raw mstore 3 (endCashFluxArg2Mem I (endCashFixHashMem2 I)) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        rw [hsourceMask]
        simp only [endCashFluxArg2Mem, endCashFluxOutPtr]
        rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
            ((⟨4⟩ : UInt256) + ⟨128⟩))).toNat =
          ((⟨128⟩ : UInt256) + ⟨68⟩).toNat from by native_decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I))
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        simp only [endCashFluxCalldataMem, endCashFluxOutPtr]
        rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
            ((⟨4⟩ : UInt256) + ⟨128⟩)))).toNat =
          ((⟨128⟩ : UInt256) + ⟨100⟩).toNat from by native_decide])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endCashFluxSelectorMem, endCashFluxArg0Mem, endCashFluxArg1Mem,
      endCashFluxArg2Mem, endCashFluxCalldataMem, endCashFluxOutPtr, endCashFluxInSize,
      endCashFluxOutSize, endCashFluxEndPtr, endCashFluxSelectorShifted,
      endCashFluxSelectorWord, endCashVatWord, endSlotWord, solcSlotWord, solcAddrMask,
      hselectorMask, hthisMask, hsourceMask, u256_land_comm] using rd9839⟩

theorem endCashX_fluxNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel amt : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9758⟩
      [amt, solcSourceWord I, endCashThisWord I, endCashIlkWord I,
        endCashFluxSelectorWord, endCashVatWord σ I, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd9839⟩ := endCashX_fluxExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨9839⟩) (okPc := ⟨9851⟩) rd9839
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem endCashX_fluxCallReady {cA gh bl σ σ₀ A I} {g : Sat256} {sel amt : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9758⟩
      [amt, solcSourceWord I, endCashThisWord I, endCashIlkWord I,
        endCashFluxSelectorWord, endCashVatWord σ I, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashFixHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9854⟩
      (gasWord :: endCashVatWord σ I :: ⟨0⟩ :: endCashFluxOutPtr ::
        endCashFluxInSize :: endCashFluxOutPtr :: endCashFluxOutSize ::
        endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd9839⟩ := endCashX_fluxExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd9854⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨9839⟩) (okPc := ⟨9851⟩) rd9839
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd9854⟩

theorem endCashX_fluxPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel amt gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9854⟩
      (gasWord :: endCashVatWord σ I :: ⟨0⟩ :: endCashFluxOutPtr ::
        endCashFluxInSize :: endCashFluxOutPtr :: endCashFluxOutSize ::
        endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endCashVatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endCashVatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)).readWithPadding
            endCashFluxOutPtr.toNat endCashFluxInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCashFluxEndPtr :: endCashFluxSelectorWord ::
            endCashVatWord σ I :: endCashWadWord I :: endCashIlkWord I ::
            endCashReturnPc :: sel :: [])
          (endCashFluxPostCallMem σ I amt out) (UInt256.ofNat 9) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd9855raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endCashFluxOutPtr.toNat endCashFluxInSize.toNat)
          endCashFluxOutPtr.toNat endCashFluxOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endCashFluxOutPtr endCashFluxInSize endCashFluxOutSize
      native_decide
    simpa [endCashFluxPostCallMem, endCashFluxOutPtr, endCashFluxInSize,
      endCashFluxOutSize, endCashFluxEndPtr, haw] using rd9855raw

theorem endCashX_fluxCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel amt gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9854⟩
      (gasWord :: endCashVatWord σ I :: ⟨0⟩ :: endCashFluxOutPtr ::
        endCashFluxInSize :: endCashFluxOutPtr :: endCashFluxOutSize ::
        endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
      (⟨0⟩ :: endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxCalldataMem σ I amt (endCashFixHashMem2 I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd9855raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCashFluxOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endCashFluxOutPtr.toNat endCashFluxInSize.toNat)
        endCashFluxOutPtr.toNat endCashFluxOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endCashFluxOutPtr endCashFluxInSize endCashFluxOutSize
    native_decide
  simpa [endCashFluxOutPtr, endCashFluxInSize, endCashFluxOutSize, endCashFluxEndPtr,
    hmin, byteArray_write_len_zero, haw] using rd9855raw

theorem endCashX_fluxCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
      (⟨0⟩ :: endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨9855⟩) (okPc := ⟨9871⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem endCashX_fluxCallSucceeded {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
      (⟨1⟩ :: endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9873⟩
      (endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨9855⟩) (okPc := ⟨9871⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCashX_outAddEntry {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9855⟩
      (⟨1⟩ :: endCashFluxEndPtr :: endCashFluxSelectorWord :: endCashVatWord σ I ::
        endCashWadWord I :: endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashFluxPostCallMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endCashWadWord I, endCashOutWord σ' I, ⟨9911⟩, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k' C' := by
  obtain ⟨_, _, rd9873⟩ := endCashX_fluxCallSucceeded (g := g) h
  have rd9879pre := evm_run rd9873 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rd9879pre.mstore 0
    (wordAt0Mem (endCashIlkWord I)
      (endCashFluxPostCallMem σ I (endCashAmtWord σ I) out))
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (endCashOutInnerHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I)) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (endCashOutInnerHashMem_slot σ I (endCashAmtWord σ I) out)
    (by native_decide) (by evm_ov)
  have rdOuterKeyPrefix := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdOuterKeyPrefix.mstore 0
    (wordAt0Mem (solcSourceWord I) (endCashOutInnerHashMem σ I (endCashAmtWord σ I) out))
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0
    (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSlot := rdOuterHashPrefix.keccak256 0 (endCashOutSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (endCashOutHashMem_slot σ I (endCashAmtWord σ I) out hsz68)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide) (by evm_ov)
  have rdLoaded : ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9901⟩
      (endCashOutWord σ' I :: endCashVatWord σ I :: endCashWadWord I ::
        endCashIlkWord I :: endCashReturnPc :: sel :: [])
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endCashOutWord, endSlotWord, solcSlotWord] using rdLoadedRaw⟩
  obtain ⟨_, _, rdLoaded⟩ := rdLoaded
  have rdJumpTarget := evm_run rdLoaded with [
    raw push2 ⟨9911⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdJumpTarget.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endCashX_outAddOverflow {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤ (endCashOutWord σ' I).toNat + (endCashWadWord I).toNat)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endCashWadWord I, endCashOutWord σ' I, ⟨9911⟩, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let outWord := endCashOutWord σ' I
  let wad := endCashWadWord I
  have hover' : UInt256.size ≤ wad.toNat + outWord.toNat := by
    dsimp [outWord, wad]
    simpa [Nat.add_comm] using hover
  have hsum_lt2 : wad.toNat + outWord.toNat < 2 * UInt256.size := by
    have hout : outWord.toNat < UInt256.size := outWord.val.isLt
    have hwad : wad.toNat < UInt256.size := wad.val.isLt
    omega
  have hmod : (wad.toNat + outWord.toNat) % UInt256.size =
      wad.toNat + outWord.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (wad + outWord).toNat = wad.toNat + outWord.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (wad + outWord) outWord = ⟨1⟩ := by
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
    simpa [outWord, wad] using rd10099
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

theorem endCashX_outAddSuccess {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hfit : (endCashOutWord σ' I).toNat + (endCashWadWord I).toNat < UInt256.size)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10092⟩
      [endCashWadWord I, endCashOutWord σ' I, ⟨9911⟩, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9911⟩
      [endCashOutWord σ' I + endCashWadWord I, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k' C' := by
  let outWord := endCashOutWord σ' I
  let wad := endCashWadWord I
  have hfit' : wad.toNat + outWord.toNat < UInt256.size := by
    dsimp [outWord, wad]
    simpa [Nat.add_comm] using hfit
  have haddNat : (wad + outWord).toNat = wad.toNat + outWord.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit']
  have hlt : UInt256.lt (wad + outWord) outWord = ⟨0⟩ :=
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
    simpa [outWord, wad] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10100
  have rd10108pre := evm_run rd10100 with [
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd9911 := evm_run rd10108pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hcomm :
      endCashWadWord I + endCashOutWord σ' I =
        endCashOutWord σ' I + endCashWadWord I :=
    u256_add_comm (endCashWadWord I) (endCashOutWord σ' I)
  exact ⟨_, _, by simpa [outWord, wad, hcomm] using rd9911⟩

theorem endCashX_outStoreHash {cA cA' gh bl σ σ' σ₀ A I} {g sel outNew : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9911⟩
      [outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9940⟩
      [endCashOutSlot I, outNew, solcMappingSlot ⟨17⟩ (endCashIlkWord I), ⟨64⟩,
        ⟨32⟩, ⟨0⟩, outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k' C' := by
  have rd9916pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rd9916pre.mstore 0
    (wordAt0Mem (endCashIlkWord I)
      (endCashOutHashMem σ I (endCashAmtWord σ I) out))
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (endCashOutStoreInnerHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (solcMappingSlot ⟨17⟩ (endCashIlkWord I)) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (endCashOutStoreInnerHashMem_slot σ I (endCashAmtWord σ I) out)
    (by native_decide) (by evm_ov)
  have rdOuterKeyPrefix := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdOuterKeyPrefix.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (endCashOutStoreInnerHashMem σ I (endCashAmtWord σ I) out))
    (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0
    (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOutSlotPrefix := evm_run rdOuterMem with [
    raw dup2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOutSlot := rdOutSlotPrefix.keccak256 0 (endCashOutSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (endCashOutStoreHashMem_slot σ I (endCashAmtWord σ I) out hsz68)
    (by native_decide) (by evm_ov)
  have rdSstoreReady := evm_run rdOutSlot with [
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdSstoreReady⟩

theorem endCashX_outStoreAtHash {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9940⟩
      [endCashOutSlot I, outNew, solcMappingSlot ⟨17⟩ (endCashIlkWord I), ⟨64⟩,
        ⟨32⟩, ⟨0⟩, outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9941⟩
      [solcMappingSlot ⟨17⟩ (endCashIlkWord I), ⟨64⟩, ⟨32⟩, ⟨0⟩, outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  obtain ⟨_, _, rdStoredRaw⟩ := h.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endCashPostAccountMap] using rdStoredRaw⟩

theorem endCashX_bagSlotReady {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9941⟩
      [solcMappingSlot ⟨17⟩ (endCashIlkWord I), ⟨64⟩, ⟨32⟩, ⟨0⟩, outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9947⟩
      [endCashBagSlot I, ⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I), outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  have rdBagMemPrefix := evm_run h with [
    raw push1 ⟨16⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdBagMem := rdBagMemPrefix.mstore 0
    (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdBagSlotPrefix := evm_run rdBagMem with [
    raw swap3 (by native_decide) (by evm_ov)]
  have rdBagSlot := rdBagSlotPrefix.keccak256 0 (endCashBagSlot I) (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (endCashBagHashMem_slot σ I (endCashAmtWord σ I) out)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, rdBagSlot⟩

theorem endCashX_bagLoaded {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9947⟩
      [endCashBagSlot I, ⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I), outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9948⟩
      [solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
        ⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I), outNew, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  obtain ⟨_, _, rdBagLoadedRaw⟩ := h.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rdBagLoadedRaw⟩

theorem endCashX_bagRestoreReady {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9948⟩
      [solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
        ⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I), outNew, endCashWadWord I,
        endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9950⟩
      [⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I),
        solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
        outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  have rdRestorePrefix := evm_run h with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdRestorePrefix⟩

theorem endCashX_bagRestoreMem {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9950⟩
      [⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I),
        solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
        outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
        outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  have rdRestored := h.mstore 0
    (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  exact ⟨_, _, rdRestored⟩

theorem endCashX_bagLoadRestore {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9947⟩
      [endCashBagSlot I, ⟨32⟩, solcMappingSlot ⟨17⟩ (endCashIlkWord I), outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashBagHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [endCashPostBagWord σ' I outNew, outNew, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  obtain ⟨_, _, rdBagLoaded⟩ := endCashX_bagLoaded (g := g) h
  obtain ⟨_, _, rdRestoreReady⟩ := endCashX_bagRestoreReady (g := g) rdBagLoaded
  obtain ⟨_, _, rdRestored⟩ := endCashX_bagRestoreMem (g := g) rdRestoreReady
  change ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
    [solcSlotWord (endCashPostAccountMap σ' I outNew) I (endCashBagSlot I),
      outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
    (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
    (cA', endCashPostAccountMap σ' I outNew) k' C'
  exact ⟨_, _, rdRestored⟩

theorem endCashX_bagLoadGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9941⟩
      [solcMappingSlot ⟨17⟩ (endCashIlkWord I), ⟨64⟩, ⟨32⟩, ⟨0⟩, outNew,
        endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutStoreHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [endCashPostBagWord σ' I outNew, outNew, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  obtain ⟨_, _, rdBagSlot⟩ := endCashX_bagSlotReady (g := g) h
  exact endCashX_bagLoadRestore (g := g) rdBagSlot

theorem endCashX_outStoreGuard {cA cA' gh bl σ σ' σ₀ A I} {g sel outNew : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9911⟩
      [outNew, endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [endCashPostBagWord σ' I outNew, outNew, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k' C' := by
  obtain ⟨_, _, rdStoreHash⟩ := endCashX_outStoreHash (g := g) hsz68 h
  obtain ⟨_, _, rdStored⟩ := endCashX_outStoreAtHash (g := g) hperm rdStoreHash
  exact endCashX_bagLoadGuard (g := g) rdStored

theorem endCashX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σ : AccountMap} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨10033⟩
      [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have rd10040pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide) mem_cost
      (mloadFreePtrValue
        (by rw [endCashOutHashMemAfterBag_size σ I (endCashAmtWord σ I) out]; decide)
        (by decide) (endCashOutHashMemAfterBag_read64 σ I (endCashAmtWord σ I) out))
      (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdLogMem := rd10040pre.mstore 0
    (endCashLogDataMem σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10047pre := evm_run rdLogMem with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide) mem_cost
      (mloadFreePtrValue
        (by rw [endCashLogDataMem_size σ I (endCashAmtWord σ I) out]; decide)
        (by decide) (endCashLogDataMem_read64 σ I (endCashAmtWord σ I) out))
      (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdTopic := rd10047pre.pushConst
    (⟨0x888c7c01b06fd8004523e2bc9a274be1feaa9f03579ae5f568061dac078793c9⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd10088pre := evm_run rdTopic with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLog := RD.log3
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0x888c7c01b06fd8004523e2bc9a274be1feaa9f03579ae5f568061dac078793c9⟩)
    (d := endCashIlkWord I) (e := solcSourceWord I)
    (t := [endCashWadWord I, endCashIlkWord I, endCashReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 9).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd10088pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopWad := RD.pop (a := endCashWadWord I)
    (t := [endCashIlkWord I, endCashReturnPc, sel]) rdLog
    (by native_decide) (by evm_ov)
  have rdPopIlk := RD.pop (a := endCashIlkWord I) (t := [endCashReturnPc, sel])
    rdPopWad (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endCashReturnPc) (t := [sel]) rdPopIlk
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endCashReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem endCashX_outRequireReturns {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : outNew.toNat ≤ (endCashPostBagWord σ' I outNew).toNat)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [endCashPostBagWord σ' I outNew, outNew, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    RDret endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cA', endCashPostAccountMap σ' I outNew) ByteArray.empty := by
  let bagWord := endCashPostBagWord σ' I outNew
  have hlt : UInt256.lt bagWord outNew = ⟨0⟩ := by
    apply ult_zero
    dsimp [bagWord]
    exact hle
  have rd9952pre := evm_run h with [raw lt (by native_decide) (by evm_ov)]
  have rd9952 := by
    simpa [bagWord] using rd9952pre
  rw [hlt] at rd9952
  have rd9953pre := evm_run rd9952 with [raw iszero (by native_decide) (by evm_ov)]
  have rd9953 := by
    simpa using rd9953pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd9953
  have rd10033 := evm_run rd9953 with [
    raw push2 ⟨10033⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact endCashX_logReturn hperm rd10033

theorem endCash_solcErrorStringMem0_size_260 {mem : ByteArray} (hmem : mem.size = 260) :
    (solcErrorStringMem0 mem).size = 260 := by
  unfold solcErrorStringMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 128 260 260
    hmem (by omega) (by omega)

theorem endCash_solcErrorStringMem1_size_260 {mem : ByteArray} (hmem : mem.size = 260) :
    (solcErrorStringMem1 mem).size = 260 := by
  unfold solcErrorStringMem1
  exact toByteArray_write32_size_of_le (solcErrorStringMem0 mem) ⟨32⟩ 132 260 260
    (endCash_solcErrorStringMem0_size_260 hmem)
    (by rw [endCash_solcErrorStringMem0_size_260 hmem]; omega) (by omega)

theorem endCash_solcErrorStringMem2_size_260 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem2 len mem).size = 260 := by
  unfold solcErrorStringMem2
  exact toByteArray_write32_size_of_le (solcErrorStringMem1 mem) len 164 260 260
    (endCash_solcErrorStringMem1_size_260 hmem)
    (by rw [endCash_solcErrorStringMem1_size_260 hmem]; omega) (by omega)

theorem endCash_solcErrorStringMem3_size_260 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem3 len word mem).size = 260 := by
  unfold solcErrorStringMem3
  exact toByteArray_write32_size_of_le (solcErrorStringMem2 len mem) word 196 260 260
    (endCash_solcErrorStringMem2_size_260 len hmem)
    (by rw [endCash_solcErrorStringMem2_size_260 len hmem]; omega) (by omega)

theorem endCash_solcErrorStringMem3_read64_260 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [endCash_solcErrorStringMem2_size_260 len hmem]; omega) (by omega)
      (by rw [endCash_solcErrorStringMem2_size_260 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [endCash_solcErrorStringMem1_size_260 hmem]; omega) (by omega)
      (by rw [endCash_solcErrorStringMem1_size_260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [endCash_solcErrorStringMem0_size_260 hmem]; omega) (by omega)
      (by rw [endCash_solcErrorStringMem0_size_260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem RD.endCashInsufficientBagRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨9957⟩ stk mem (UInt256.ofNat 9) rdata acc k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
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
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨28⟩ mem)
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endCashInsufficientBagRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem3 ⟨28⟩ endCashInsufficientBagRawWord mem)
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost
      (mloadFreePtrValue
        (by rw [endCash_solcErrorStringMem3_size_260 ⟨28⟩ endCashInsufficientBagRawWord hmem]; decide)
        (by decide)
        (endCash_solcErrorStringMem3_read64_260 ⟨28⟩ endCashInsufficientBagRawWord
          hmem hread64))
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endCashX_outRequireReverts {cA cA' gh bl σ σ' σ₀ A I}
    {g sel outNew : UInt256} {out : ByteArray} {k C : ℕ}
    (hgt : (endCashPostBagWord σ' I outNew).toNat < outNew.toNat)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9951⟩
      [endCashPostBagWord σ' I outNew, outNew, endCashWadWord I, endCashIlkWord I,
        endCashReturnPc, sel]
      (endCashOutHashMemAfterBag σ I (endCashAmtWord σ I) out) (UInt256.ofNat 9) out
      (cA', endCashPostAccountMap σ' I outNew) k C) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let bagWord := endCashPostBagWord σ' I outNew
  have hlt : UInt256.lt bagWord outNew = ⟨1⟩ := by
    apply ult_one
    dsimp [bagWord]
    exact hgt
  have rd9952pre := evm_run h with [raw lt (by native_decide) (by evm_ov)]
  have rd9952 := by
    simpa [bagWord] using rd9952pre
  rw [hlt] at rd9952
  have rd9953pre := evm_run rd9952 with [raw iszero (by native_decide) (by evm_ov)]
  have rd9953 := by
    simpa using rd9953pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd9953
  have rd9957pre := evm_run rd9953 with [
    raw push2 ⟨10033⟩ (by native_decide) (by evm_ov)]
  have rd9957 := rd9957pre.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.endCashInsufficientBagRevert rd9957
    (endCashOutHashMemAfterBag_size σ I (endCashAmtWord σ I) out)
    (endCashOutHashMemAfterBag_read64 σ I (endCashAmtWord σ I) out)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalExpr_endCash_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endCashStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endCashIlkBytes I))
  rw [endCashStore_get_ilk]
  rfl

theorem evalStorageRef_endCash_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endCashStore I } evm
      (fixRef (.var "ilk")) = .ok (endCashFixEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endCash_ilk evm I
  simp [endCashFixEvaledRef, endCashIlkKey, hilk, endCashIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, fixRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endCash_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
      (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endCashFixSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endCashStore I })
    (slot := fixRef (.var "ilk"))
    (er := endCashFixEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCashFixSlot I))
    (hbase := by simp [endCashStore, fixRef])
    (her := evalStorageRef_endCash_fix evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCashFixSlot I))

theorem evalExpr_endCash_fix_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashFixSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
      (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCashStore I } evm
        (.storage (fixRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [hfix] using evalExpr_endCash_fix evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endCashStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endCash_fix_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashFixSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
      (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCashStore I } evm
        (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endCashFixSlot I)).toNat)) :=
    evalExpr_endCash_fix evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endCashStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hneInt :
      Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endCashFixSlot I)).toNat ≠ 0 := by
    intro hbad
    apply hfix
    apply u256_inj
    have hnat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (endCashFixSlot I)).toNat = 0 := by
      exact Nat.cast_eq_zero.mp hbad
    simpa using hnat
  exact endEvalExpr_ne_int_true hstorage hzero hneInt

theorem evalStorageRef_endCash_vat {locals : Store} (_hbase : locals.get? "vat" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vatRef = .ok ({ base := "vat", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]

theorem evalExpr_endCash_vat {locals : Store} (evm : EVM.State)
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
    (her := evalStorageRef_endCash_vat hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨1⟩)

theorem endCashVatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endCashVatWord σ I = endCashVatWord τ I := by
  simp [endCashVatWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩]

theorem endCashVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endCashVatWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endCashVatWord σ I)
  have htarget : endCashVatWord σ I = endCashVatWord τ I :=
    endCashVatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endCashVatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endCashVatWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endCashVatWord σ I)
  have htarget : endCashVatWord σ I = endCashVatWord τ I :=
    endCashVatWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem endCashVatAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endCashVatAddr σ I = AccountAddress.ofUInt256 (endCashVatWord σ I) := by
  simpa [endCashVatAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endCashVatWord σ I)).symm

theorem endCashVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
      (endCashVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endCashVatWord σ I) (addr := endCashVatAddr σ I)
      (endCashVatAddr_eq_ofUInt256 σ I) hzero

theorem endCashVatCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
      (endCashVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endCashVatWord σ I) (addr := endCashVatAddr σ I)
      (endCashVatAddr_eq_ofUInt256 σ I) hne

theorem endCashStmtRmulReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecStmt config { contract := contract, locals := endCashStore I } evm0
      (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
      (.ok { contract := contract, locals := endCashStoreAmt σ I } evm0) := by
  intro evm0
  have hwad :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endCashWadWord I).toNat)) := by
    simpa [endCashStore] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endCashStore I)
        (name := "wad") (value := endCashWadWord I) (by simp [endCashStore])
  have hfixExpr :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endCashFixWord σ I).toNat)) := by
    have hstorage := evalExpr_endCash_fix evm0 I hsz68
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endCashStore I } evm0
        [.var "wad", .storage (fixRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endCashWadWord I).toNat),
            .int (Int.ofNat (endCashFixWord σ I).toNat)] := by
    simp [evalExprs?, hwad, hfixExpr, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endCashWadWord I).toNat),
            .int (Int.ofNat (endCashFixWord σ I).toNat)] =
        some (endUintBinaryLocals (endCashWadWord I) (endCashFixWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionReturn (evm := evm0)
      (x := endCashWadWord I) (y := endCashFixWord σ I)
      (prod := endCashWadWord I * endCashFixWord σ I)
      (q := endCashAmtWord σ I) rfl hfit rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endCashStore I })
    (evm := evm0) (name := "rmul") (retVar := "amt")
    (args := [.var "wad", .storage (fixRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endCashWadWord I).toNat),
        .int (Int.ofNat (endCashFixWord σ I).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endCashWadWord I) (endCashFixWord σ I))
    hargs (by rfl) hbind hbody
  simpa [endCashStoreAmt, resumeAfterInternalCall, collapseReturns, endCashAmtWord] using hstmt

theorem endCashBodyReverts_fixZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCashFixSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hfix
  have hguard :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endCash_fix_ne_false evm0 I hsz68 hfixLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cashTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endCashStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0))
      (rest :=
        [ .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ++
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endCashBodyReverts_rmulOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (endCashWadWord I).toNat * (endCashFixWord σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCashFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCash_fix_ne_true evm0 I hsz68 hfixLoad
  have hwad :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.var "wad") = .ok (.int (Int.ofNat (endCashWadWord I).toNat)) := by
    simpa [endCashStore] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endCashStore I)
        (name := "wad") (value := endCashWadWord I) (by simp [endCashStore])
  have hfixExpr :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endCashFixWord σ I).toNat)) := by
    have hstorage := evalExpr_endCash_fix evm0 I hsz68
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endCashStore I } evm0
        [.var "wad", .storage (fixRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endCashWadWord I).toNat),
            .int (Int.ofNat (endCashFixWord σ I).toNat)] := by
    simp [evalExprs?, hwad, hfixExpr, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endCashWadWord I).toNat),
            .int (Int.ofNat (endCashFixWord σ I).toNat)] =
        some (endUintBinaryLocals (endCashWadWord I) (endCashFixWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := endCashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        .reverted := by
    have hbody :=
      endExecRmulFunctionRevertMul (evm := evm0)
        (x := endCashWadWord I) (y := endCashFixWord σ I) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := endCashStore I })
      (evm := evm0) (name := "rmul") (retVar := "amt")
      (args := [.var "wad", .storage (fixRef (.var "ilk"))])
      (argVals :=
        [.int (Int.ofNat (endCashWadWord I).toNat),
          .int (Int.ofNat (endCashFixWord σ I).toNat)])
      (callee := rmulFunction)
      (locals := endUintBinaryLocals (endCashWadWord I) (endCashFixWord σ I))
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body .reverted := by
    simp only [cashTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hrmulStmt
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCashBodyReverts_fluxNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCashFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hbad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCash_fix_ne_true evm0 I hsz68 hfixLoad
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := endCashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := endCashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashStmtRmulReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hsz68 hfit
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.storage vatRef) = .ok (.address (endCashVatAddr σ I)) := by
    have hbase : (endCashStoreAmt σ I).get? "vat" = none := by
      simp [endCashStoreAmt, endCashStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashVatAddr, endCashVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endCash_vat (locals := endCashStoreAmt σ I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endCashVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endCashVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardFlux :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm0)
        (locals := endCashStoreAmt σ I) (receiver := .storage vatRef)
        (retVar := "_flux") (name := "flux") (sendVal := 0)
        (args := [.var "ilk", thisAddr, sender, .var "amt"]) (perm := true)
        hguardFlux
  have hfluxWithTail :
      ExecBlock config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ++
          [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
            .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
            .require
              (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
        .reverted := by
    exact.execBlock_append_term
      (s2 :=
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body .reverted := by
    simp only [cashTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    simpa using hfluxWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCashBodyReverts_fluxCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endCashVatAddr σ I)) "flux" 0
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)]
        (false, evmFlux, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCashFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hbad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCash_fix_ne_true evm0 I hsz68 hfixLoad
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := endCashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := endCashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashStmtRmulReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hsz68 hfit
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.storage vatRef) = .ok (.address (endCashVatAddr σ I)) := by
    have hbase : (endCashStoreAmt σ I).get? "vat" = none := by
      simp [endCashStoreAmt, endCashStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashVatAddr, endCashVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endCash_vat (locals := endCashStoreAmt σ I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endCashVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endCashVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardFlux :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
    have hget :
        (endCashStoreAmt σ I).get? "ilk" =
          some (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
      rw [endCashStoreAmt, store_get_ne _ _ (by native_decide), endCashStore_get_ilk]
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endCashStoreAmt σ I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endCashIlkBytes I))
    rw [hget]
    rfl
  have hthis :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        thisAddr = .ok (.address I.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, evm0, initState, pure]
  have hsender :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evm0, initState, pure]
  have hamt :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.var "amt") = .ok (.int (Int.ofNat (endCashAmtWord σ I).toNat)) := by
    simpa [endCashStoreAmt] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endCashStoreAmt σ I)
        (name := "amt") (value := endCashAmtWord σ I) (by simp [endCashStoreAmt])
  have hfluxArgs :
      evalExprs? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        [.var "ilk", thisAddr, sender, .var "amt"] =
          .ok [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
            .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)] := by
    simp [evalExprs?, hilk, hthis, hsender, hamt, EvalResult.bind, bind, pure]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmFlux)
        (locals := endCashStoreAmt σ I) (receiver := .storage vatRef)
        (retVar := "_flux") (name := "flux") (target := endCashVatAddr σ I)
        (sendVal := 0) (args := [.var "ilk", thisAddr, sender, .var "amt"])
        (argVals :=
          [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
            .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)])
        (out := out) (perm := true)
        hguardFlux hreceiver hfluxArgs hcall
  have hfluxWithTail :
      ExecBlock config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ++
          [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
            .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
            .require
              (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
        .reverted := by
    exact.execBlock_append_term
      (s2 :=
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body .reverted := by
    simp only [cashTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    simpa using hfluxWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem evalStorageRef_endCash_out (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (hsrc : evm.executionEnv.source = I.source)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endCashStoreFlux σ I } evm
      (outRef (.var "ilk") sender) = .ok (endCashEvaledOutRef I) := by
  have hlen : (endCashIlkBytes I).length = bytes32Width.val + 1 := by
    simpa [endCashIlkBytes] using endBytes32ArgBytes_len (I := I) (by omega)
  have hmin : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    simpa [endCashIlkBytes, List.length_take, List.length_drop] using hlen
  have hget :
      (endCashStoreFlux σ I).get? "ilk" =
        some (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
    rw [endCashStoreFlux, store_get_ne _ _ (by native_decide),
      endCashStoreAmt, store_get_ne _ _ (by native_decide), endCashStore_get_ilk]
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef, sender,
    envValue, endCashEvaledOutRef, endCashIlkKey, endCashOutKey, hsrc, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hget, hmin]

theorem evalExpr_endCash_out (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (hsrc : evm.executionEnv.source = I.source)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCashStoreFlux σ I } evm
      (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endCashStoreFlux σ I })
    (slot := outRef (.var "ilk") sender)
    (er := endCashEvaledOutRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCashOutSlot I))
    (hbase := by
      change (endCashStoreFlux σ I).get? "out" = none
      rw [endCashStoreFlux, store_get_ne _ _ (by native_decide),
        endCashStoreAmt, store_get_ne _ _ (by native_decide),
        endCashStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp)
    (her := evalStorageRef_endCash_out evm I σ hsrc hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCashOutSlot I))

theorem evalStorageRef_endCash_out_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (.fixedBytes bytes32Width (endCashIlkBytes I)))
    (hsrc : evm.executionEnv.source = I.source)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (outRef (.var "ilk") sender) = .ok (endCashEvaledOutRef I) := by
  have hlen : (endCashIlkBytes I).length = bytes32Width.val + 1 := by
    simpa [endCashIlkBytes] using endBytes32ArgBytes_len (I := I) (by omega)
  have hmin : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    simpa [endCashIlkBytes, List.length_take, List.length_drop] using hlen
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef, sender,
    envValue, endCashEvaledOutRef, endCashIlkKey, endCashOutKey, hsrc, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hget, hmin]

theorem evalExpr_endCash_out_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hbase : locals.get? "out" = none)
    (hget : locals.get? "ilk" = some (.fixedBytes bytes32Width (endCashIlkBytes I)))
    (hsrc : evm.executionEnv.source = I.source)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := outRef (.var "ilk") sender)
    (er := endCashEvaledOutRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCashOutSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endCash_out_of_get evm I hget hsrc hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCashOutSlot I))

theorem evalStorageRef_endCash_bag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (_hbase : locals.get? "bag" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (bagRef sender) = .ok (endCashEvaledBagRef I) := by
  simp [evalStorageRef, evalStorageRefStep, bagRef, sender, envValue, endCashEvaledBagRef,
    endCashBagKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_endCash_bag {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hbase : locals.get? "bag" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashBagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := bagRef sender)
    (er := endCashEvaledBagRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCashBagSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endCash_bag evm I hbase hsrc)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCashBagSlot I))

theorem endCashAssignOut {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (outNew : UInt256)
    (hbase : locals.get? "out" = none)
    (hget : locals.get? "ilk" = some (.fixedBytes bytes32Width (endCashIlkBytes I)))
    (hsrc : evm.executionEnv.source = I.source)
    (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (outRef (.var "ilk") sender) (.int (Int.ofNat outNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endCashPostState evm I outNew) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endCashOutSlot I))
      (hbase := hbase)
      (her := evalStorageRef_endCash_out_of_get evm I hget hsrc hsz68)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endCashPostState] using
    endStorageLocStore_uint256 evm (endCashOutSlot I) outNew

theorem endCashEvalExpr_le_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hle]

theorem endCashEvalExpr_le_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : b < a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  have hnot : ¬ a ≤ b := by omega
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hnot]

theorem endCashTailReverts_outAddOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsrc : evm.executionEnv.source = I.source)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat) :
    ExecBlock config { contract := contract, locals := endCashStoreFlux σ I } evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.var "outNew") (.storage (bagRef sender))) ]
      .reverted := by
  let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
  have hout :
      evalExpr? config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.storage (outRef (.var "ilk") sender)) = .ok (.int (Int.ofNat outWord.toNat)) := by
    simpa [outWord] using evalExpr_endCash_out evm I σ hsrc hsz68
  have hwad :
      evalExpr? config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.var "wad") = .ok (.int (Int.ofNat (endCashWadWord I).toNat)) := by
    simpa [endCashStoreFlux, endCashStoreAmt, endCashStore] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endCashStoreFlux σ I)
        (name := "wad") (value := endCashWadWord I)
        (by
          rw [endCashStoreFlux, endCashStoreAmt, endCashStore,
            store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
            store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endCashStoreFlux σ I } evm
        [.storage (outRef (.var "ilk") sender), .var "wad"] =
          .ok [.int (Int.ofNat outWord.toNat),
            .int (Int.ofNat (endCashWadWord I).toNat)] := by
    simp [evalExprs?, hout, hwad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat outWord.toNat),
            .int (Int.ofNat (endCashWadWord I).toNat)] =
        some (endUintBinaryLocals outWord (endCashWadWord I)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
        .reverted := by
    have hbody :=
      endExecAddFunctionRevert (evm := evm) (x := outWord) (y := endCashWadWord I) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := endCashStoreFlux σ I })
      (evm := evm) (name := "add") (retVar := "outNew")
      (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
      (argVals :=
        [.int (Int.ofNat outWord.toNat),
          .int (Int.ofNat (endCashWadWord I).toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals outWord (endCashWadWord I))
      hargs (by rfl) hbind hbody
  exact ExecBlock.consRevert haddStmt

theorem endCashTailPrefixOutAssigned (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsrc : evm.executionEnv.source = I.source)
    (hfit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat <
        UInt256.size) :
    let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
    let outNew := outWord + endCashWadWord I
    ExecBlock config { contract := contract, locals := endCashStoreFlux σ I } evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew") ]
      (.ok { contract := contract, locals := endCashStoreOutNew σ I outNew }
        (endCashPostState evm I outNew)) := by
  intro outWord outNew
  have hout :
      evalExpr? config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.storage (outRef (.var "ilk") sender)) = .ok (.int (Int.ofNat outWord.toNat)) := by
    simpa [outWord] using evalExpr_endCash_out evm I σ hsrc hsz68
  have hwad :
      evalExpr? config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.var "wad") = .ok (.int (Int.ofNat (endCashWadWord I).toNat)) := by
    simpa [endCashStoreFlux, endCashStoreAmt, endCashStore] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endCashStoreFlux σ I)
        (name := "wad") (value := endCashWadWord I)
        (by
          rw [endCashStoreFlux, endCashStoreAmt, endCashStore,
            store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
            store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endCashStoreFlux σ I } evm
        [.storage (outRef (.var "ilk") sender), .var "wad"] =
          .ok [.int (Int.ofNat outWord.toNat),
            .int (Int.ofNat (endCashWadWord I).toNat)] := by
    simp [evalExprs?, hout, hwad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat outWord.toNat),
            .int (Int.ofNat (endCashWadWord I).toNat)] =
        some (endUintBinaryLocals outWord (endCashWadWord I)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have haddStmt :
      ExecStmt config { contract := contract, locals := endCashStoreFlux σ I } evm
        (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
        (.ok { contract := contract, locals := endCashStoreOutNew σ I outNew } evm) := by
    have hbody :=
      endExecAddFunctionReturn (evm := evm) (x := outWord) (y := endCashWadWord I)
        (sum := outNew) rfl hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endCashStoreFlux σ I })
      (evm := evm) (name := "add") (retVar := "outNew")
      (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
      (argVals :=
        [.int (Int.ofNat outWord.toNat), .int (Int.ofNat (endCashWadWord I).toNat)])
      (callee := addFunction) (locals := endUintBinaryLocals outWord (endCashWadWord I))
      hargs (by rfl) hbind hbody
    simpa [endCashStoreOutNew, resumeAfterInternalCall, collapseReturns, outNew] using hstmt
  have houtNew :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evm
        (.var "outNew") = .ok (.int (Int.ofNat outNew.toNat)) := by
    simpa [endCashStoreOutNew] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endCashStoreOutNew σ I outNew)
        (name := "outNew") (value := outNew) (by simp [endCashStoreOutNew])
  have hassign :
      assignStorageRef? config { contract := contract, locals := endCashStoreOutNew σ I outNew }
        evm .storage (outRef (.var "ilk") sender) (.int (Int.ofNat outNew.toNat)) =
          .ok ({ contract := contract, locals := endCashStoreOutNew σ I outNew },
            endCashPostState evm I outNew) := by
    exact endCashAssignOut evm I outNew
      (by simp [endCashStoreOutNew, endCashStoreFlux, endCashStoreAmt, endCashStore])
      (by
        rw [endCashStoreOutNew, store_get_ne _ _ (by native_decide),
          endCashStoreFlux, store_get_ne _ _ (by native_decide),
          endCashStoreAmt, store_get_ne _ _ (by native_decide), endCashStore_get_ilk])
      hsrc hsz68
  refine ExecBlock.consNormal haddStmt ?_
  exact ExecBlock.consNormal (ExecStmt.assign houtNew hassign) ExecBlock.nil

theorem endCashTailReverts_outExceedsBag (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsrc : evm.executionEnv.source = I.source)
    (hfit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat <
        UInt256.size)
    (hgt :
      let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
      let outNew := outWord + endCashWadWord I
      let evmPost := endCashPostState evm I outNew
      (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat <
        outNew.toNat) :
    let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
    let outNew := outWord + endCashWadWord I
    ExecBlock config { contract := contract, locals := endCashStoreFlux σ I } evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.var "outNew") (.storage (bagRef sender))) ]
      .reverted := by
  intro outWord outNew
  let evmPost := endCashPostState evm I outNew
  have hprefix := endCashTailPrefixOutAssigned evm I σ hsz68 hsrc hfit
  dsimp [outWord, outNew] at hprefix
  have henvPost : evmPost.executionEnv = evm.executionEnv := by
    simpa [evmPost, endCashPostState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner (endCashOutSlot I) outNew
  have hsrcPost : evmPost.executionEnv.source = I.source := by
    rw [henvPost]
    exact hsrc
  have houtNew :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.var "outNew") = .ok (.int (Int.ofNat outNew.toNat)) := by
    simpa [endCashStoreOutNew] using
      endEvalExpr_varUInt256 (evm := evmPost) (locals := endCashStoreOutNew σ I outNew)
        (name := "outNew") (value := outNew) (by simp [endCashStoreOutNew])
  have hbag :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.storage (bagRef sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat)) := by
    exact evalExpr_endCash_bag evmPost I
      (by simp [endCashStoreOutNew, endCashStoreFlux, endCashStoreAmt, endCashStore])
      hsrcPost
  have hreq :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.binary .le (.var "outNew") (.storage (bagRef sender))) =
          .ok (.bool false) := by
    apply endCashEvalExpr_le_int_false houtNew hbag
    exact Int.ofNat_lt.mpr (by simpa [evmPost, outWord, outNew] using hgt)
  have htail :
      ExecBlock config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        [ .require
          (.binary .le (.var "outNew") (.storage (bagRef sender))) ]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreq)
  have happ :=.execBlock_append
    (s2 := [ .require
      (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
    hprefix htail
  simpa [evmPost] using happ

theorem endCashTailReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsrc : evm.executionEnv.source = I.source)
    (hfit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat <
        UInt256.size)
    (hle :
      let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
      let outNew := outWord + endCashWadWord I
      let evmPost := endCashPostState evm I outNew
      outNew.toNat ≤
        (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat) :
    let outWord := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)
    let outNew := outWord + endCashWadWord I
    ExecBlock config { contract := contract, locals := endCashStoreFlux σ I } evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.var "outNew") (.storage (bagRef sender))) ]
      (.ok { contract := contract, locals := endCashStoreOutNew σ I outNew }
        (endCashPostState evm I outNew)) := by
  intro outWord outNew
  let evmPost := endCashPostState evm I outNew
  have hprefix := endCashTailPrefixOutAssigned evm I σ hsz68 hsrc hfit
  dsimp [outWord, outNew] at hprefix
  have henvPost : evmPost.executionEnv = evm.executionEnv := by
    simpa [evmPost, endCashPostState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner (endCashOutSlot I) outNew
  have hsrcPost : evmPost.executionEnv.source = I.source := by
    rw [henvPost]
    exact hsrc
  have houtNew :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.var "outNew") = .ok (.int (Int.ofNat outNew.toNat)) := by
    simpa [endCashStoreOutNew] using
      endEvalExpr_varUInt256 (evm := evmPost) (locals := endCashStoreOutNew σ I outNew)
        (name := "outNew") (value := outNew) (by simp [endCashStoreOutNew])
  have hbag :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.storage (bagRef sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat)) := by
    exact evalExpr_endCash_bag evmPost I
      (by simp [endCashStoreOutNew, endCashStoreFlux, endCashStoreAmt, endCashStore])
      hsrcPost
  have hreq :
      evalExpr? config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        (.binary .le (.var "outNew") (.storage (bagRef sender))) =
          .ok (.bool true) := by
    apply endCashEvalExpr_le_int_true houtNew hbag
    exact Int.ofNat_le.mpr (by simpa [evmPost, outWord, outNew] using hle)
  have htail :
      ExecBlock config { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost
        [ .require
          (.binary .le (.var "outNew") (.storage (bagRef sender))) ]
        (.ok { contract := contract, locals := endCashStoreOutNew σ I outNew } evmPost) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil
  have happ :=.execBlock_append
    (s2 := [ .require
      (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
    hprefix htail
  simpa [evmPost] using happ

theorem endCashPrefixFluxSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endCashVatAddr σ I)) "flux" 0
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)]
        (true, evmFlux, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endCashStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
          .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
      (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
  intro evm0
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCashFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashFixWord, endSlotWord, solcSlotWord] using hbad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endCashStore I } evm0
        (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endCash_fix_ne_true evm0 I hsz68 hfixLoad
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := endCashStore I } evm0
        (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
        (.ok { contract := contract, locals := endCashStoreAmt σ I } evm0) := by
    simpa [evm0] using
      endCashStmtRmulReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hsz68 hfit
  have hreceiver :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.storage vatRef) = .ok (.address (endCashVatAddr σ I)) := by
    have hbase : (endCashStoreAmt σ I).get? "vat" = none := by
      simp [endCashStoreAmt, endCashStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCashVatAddr, endCashVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endCash_vat (locals := endCashStoreAmt σ I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endCashVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endCashVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardFlux :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
    have hget :
        (endCashStoreAmt σ I).get? "ilk" =
          some (.fixedBytes bytes32Width (endCashIlkBytes I)) := by
      rw [endCashStoreAmt, store_get_ne _ _ (by native_decide), endCashStore_get_ilk]
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endCashStoreAmt σ I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endCashIlkBytes I))
    rw [hget]
    rfl
  have hthis :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        thisAddr = .ok (.address I.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, evm0, initState, pure]
  have hsender :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evm0, initState, pure]
  have hamt :
      evalExpr? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (.var "amt") = .ok (.int (Int.ofNat (endCashAmtWord σ I).toNat)) := by
    simpa [endCashStoreAmt] using
      endEvalExpr_varUInt256 (evm := evm0) (locals := endCashStoreAmt σ I)
        (name := "amt") (value := endCashAmtWord σ I) (by simp [endCashStoreAmt])
  have hfluxArgs :
      evalExprs? config { contract := contract, locals := endCashStoreAmt σ I } evm0
        [.var "ilk", thisAddr, sender, .var "amt"] =
          .ok [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
            .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)] := by
    simp [evalExprs?, hilk, hthis, hsender, hamt, EvalResult.bind, bind, pure]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := endCashStoreAmt σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
    have hdec : config.externalABI.decode? "flux" out = some [] := by
      simp [config, externalABI, decodeVoid?]
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmFlux)
      (locals := endCashStoreAmt σ I) (receiver := .storage vatRef)
      (retVar := "_flux") (name := "flux") (target := endCashVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk", thisAddr, sender, .var "amt"])
      (argVals :=
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)])
      (out := out) (perm := true) (value := [])
      hguardFlux hreceiver hfluxArgs hcall hdec
    simpa [checkedExternalCallStmts, endCashStoreFlux, collapseReturns] using hblock
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
            .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
    simp only [nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    simpa using hfluxBlock
  simpa using hblock

theorem endCashBodyReverts_outAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endCashVatAddr σ I)) "flux" 0
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hsrcFlux : evmFlux.executionEnv.source = I.source)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
            .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
    simpa [evm0] using
      endCashPrefixFluxSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmFlux := evmFlux) (out := out)
        hwv hsz68 hfix hfit hcodeSize hcall
  have htail :=
    endCashTailReverts_outAddOverflow evmFlux I σ hsz68 hsrcFlux hover
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body .reverted := by
    have happ :=.execBlock_append
      (s2 :=
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      hprefix htail
    simpa [cashTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCashBodyReverts_outExceedsBag {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endCashVatAddr σ I)) "flux" 0
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hsrcFlux : evmFlux.executionEnv.source = I.source)
    (hfitAdd :
      (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat <
        UInt256.size)
    (hgt :
      let outWord := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)
      let outNew := outWord + endCashWadWord I
      let evmPost := endCashPostState evmFlux I outNew
      (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat <
        outNew.toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
            .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
    simpa [evm0] using
      endCashPrefixFluxSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmFlux := evmFlux) (out := out)
        hwv hsz68 hfix hfit hcodeSize hcall
  have htail := endCashTailReverts_outExceedsBag evmFlux I σ hsz68 hsrcFlux hfitAdd hgt
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body .reverted := by
    have happ :=.execBlock_append
      (s2 :=
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      hprefix htail
    simpa [cashTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endCashBodyReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmFlux : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord σ I ≠ ⟨0⟩)
    (hfit : (endCashWadWord I).toNat * (endCashFixWord σ I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCashVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endCashVatAddr σ I)) "flux" 0
        [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
          .address I.source, .int (Int.ofNat (endCashAmtWord σ I).toNat)]
        (true, evmFlux, out) true)
    (hsrcFlux : evmFlux.executionEnv.source = I.source)
    (hfitAdd :
      (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)).toNat +
          (endCashWadWord I).toNat <
        UInt256.size)
    (hle :
      let outWord := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)
      let outNew := outWord + endCashWadWord I
      let evmPost := endCashPostState evmFlux I outNew
      outNew.toNat ≤
        (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner (endCashBagSlot I)).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let outWord := Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner (endCashOutSlot I)
    let outNew := outWord + endCashWadWord I
    ExecTransitionBody config contract evm0 (endCashStore I) cashTransition.body
      (.returned { contract := contract, locals := endCashStoreOutNew σ I outNew }
        (endCashPostState evmFlux I outNew) none) := by
  intro evm0 outWord outNew
  have hprefix :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
            .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
          checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.var "ilk", thisAddr, sender, .var "amt"] "_flux")
        (.ok { contract := contract, locals := endCashStoreFlux σ I } evmFlux) := by
    simpa [evm0] using
      endCashPrefixFluxSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmFlux := evmFlux) (out := out)
        hwv hsz68 hfix hfit hcodeSize hcall
  have htail := endCashTailReturns evmFlux I σ hsz68 hsrcFlux hfitAdd hle
  have hblock :
      ExecBlock config { contract := contract, locals := endCashStore I } evm0
        cashTransition.body
        (.ok { contract := contract, locals := endCashStoreOutNew σ I outNew }
          (endCashPostState evmFlux I outNew)) := by
    have happ :=.execBlock_append
      (s2 :=
        [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
          .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
          .require
            (.binary .le (.var "outNew") (.storage (bagRef sender))) ])
      hprefix htail
    simpa [cashTransition, List.append_assoc, outWord, outNew] using happ
  simpa [ExecTransitionBody, evm0, outWord, outNew] using ExecFuncBody.execBlockOK hblock

theorem endCashX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCashEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endCashEntryPc) (ret := endCashReturnPc)
    (decoded := endCashDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endCashBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some cashTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endCashEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endCashX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_cash_none_short hsz4 hshort)

theorem endCashBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf cashTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endCashConcreteSelector := by
    simpa [endCashSelectorBytes, endCashConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCashConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some cashTransition :=
    endDispatchCash hsel
  have hreach := endReachCashBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_cash_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endCashX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hfixCouple : endCashFixWord σ_evm I = endCashFixWord σ_solm I := by
      simpa [endCashFixWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endCashFixSlot I) ⟨0⟩
    by_cases hfix : endCashFixWord σ_evm I = ⟨0⟩
    · have hfixSolm : endCashFixWord σ_solm I = ⟨0⟩ := by
        rw [← hfixCouple]
        exact hfix
      have hbody :
          ExecTransitionBody config contract evmSolm (endCashStore I)
            cashTransition.body .reverted := by
        simpa [evmSolm] using
          endCashBodyReverts_fixZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 hfixSolm
      exact (endCashX_fixZero (g := Sat256.ofUInt256 g) hsz68 hfix hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hfixSolm : endCashFixWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hfix (by rw [hfixCouple, hbad])
      obtain ⟨_, _, hrmulEntry⟩ :=
        endCashX_rmulEntry (g := Sat256.ofUInt256 g) hsz68 hfix hbodyReach
      by_cases hover :
          UInt256.size ≤ (endCashWadWord I).toNat * (endCashFixWord σ_evm I).toNat
      · have hoverSolm :
            UInt256.size ≤ (endCashWadWord I).toNat * (endCashFixWord σ_solm I).toNat := by
          rwa [← hfixCouple]
        have hbody :
          ExecTransitionBody config contract evmSolm (endCashStore I)
            cashTransition.body .reverted := by
          simpa [evmSolm] using
            endCashBodyReverts_rmulOverflow
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz68 hfixSolm hoverSolm
        exact (endCashX_rmulOverflow (g := Sat256.ofUInt256 g) hover hrmulEntry)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hfit :
            (endCashWadWord I).toNat * (endCashFixWord σ_evm I).toNat < UInt256.size :=
          Nat.lt_of_not_ge hover
        have hfitSolm :
            (endCashWadWord I).toNat * (endCashFixWord σ_solm I).toNat < UInt256.size := by
          rwa [← hfixCouple]
        obtain ⟨_, _, hafterRmul⟩ :=
          endCashX_rmulReturns (g := Sat256.ofUInt256 g) hfit hfix hrmulEntry
        by_cases hvatCode :
            Reasoning.Theory.extCodeSizeWord σ_evm (endCashVatWord σ_evm I) =
              ⟨0⟩
        · have hvatCodeSolm :
              Reasoning.Theory.extCodeSizeWord σ_solm
                (endCashVatWord σ_solm I) = ⟨0⟩ :=
            endCashVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract evmSolm (endCashStore I)
                cashTransition.body .reverted := by
            simpa [evmSolm] using
              endCashBodyReverts_fluxNoCode
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                hwv hsz68 hfixSolm hfitSolm hvatCodeSolm
          exact (endCashX_fluxNoCode (g := Sat256.ofUInt256 g) hafterRmul hvatCode)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hvatCodeNE :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (endCashVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
          have hvatCodeSolmNE :
              Reasoning.Theory.extCodeSizeWord σ_solm
                (endCashVatWord σ_solm I) ≠ ⟨0⟩ :=
            endCashVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
          obtain ⟨gasWord, _, _, hcallReady⟩ :=
            endCashX_fluxCallReady (g := Sat256.ofUInt256 g) hafterRmul hvatCodeNE
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd9855, hout⟩ :=
              endCashX_fluxPostCall hcallReady hdepthLt
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
                EVM.address (endCashVatAddr σ_evm I) =
                  AccountAddress.ofUInt256 (endCashVatWord σ_evm I) := by
              have hAddressId (a : AccountAddress) : EVM.address a = a := by
                apply Fin.ext
                show ↑a % EVM.twoPow 160 = ↑a
                rw [Nat.mod_eq_of_lt]
                exact a.isLt
              calc
                EVM.address (endCashVatAddr σ_evm I)
                    = EVM.address (AccountAddress.ofUInt256 (endCashVatWord σ_evm I)) := by
                      rw [endCashVatAddr_eq_ofUInt256]
                _ = AccountAddress.ofUInt256 (endCashVatWord σ_evm I) :=
                      hAddressId (AccountAddress.ofUInt256 (endCashVatWord σ_evm I))
            have hcallEvm :
                typedCallViaEVM config
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (endCashVatAddr σ_evm I)) "flux" 0
                  [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
                    .address I.source,
                    .int (Int.ofNat (endCashAmtWord σ_evm I).toNat)]
                  (z,
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'
                      substate := A'
                      createdAccounts := cA' },
                    out) true := by
              exact callCoincides
                (cfg := config)
                (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (name := "flux")
                (args :=
                  [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
                    .address I.source,
                    .int (Int.ofNat (endCashAmtWord σ_evm I).toNat)])
                (tgt := EVM.address (endCashVatAddr σ_evm I))
                (targetWord := endCashVatWord σ_evm I)
                (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
                (z := z) (o := out) (g'' := g'') (callGas := callGas)
                (mem := endCashFluxCalldataMem σ_evm I (endCashAmtWord σ_evm I)
                  (endCashFixHashMem2 I))
                (inOff := endCashFluxOutPtr) (inSize := endCashFluxInSize)
                (callPerm := true)
                hdepthNe htgt
                (endCashFluxEncode_eq σ_evm I (endCashAmtWord σ_evm I)
                  hsz68 (endCashFixHashMem2_size I))
                (by simpa [initState, hperm] using hΘeq)
            obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hStateCall⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm)
                (by simp [initState]) hAccounts
            have hVatAddr : endCashVatAddr σ_evm I = endCashVatAddr σ_solm I := by
              simp [endCashVatAddr, endCashVatWord_accountMapEquiv hAccounts]
            have hAmtWord : endCashAmtWord σ_evm I = endCashAmtWord σ_solm I := by
              simp [endCashAmtWord, hfixCouple]
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endCashVatAddr σ_solm I)) "flux" 0
                  [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
                    .address I.source,
                    .int (Int.ofNat (endCashAmtWord σ_solm I).toNat)]
                  (z,
                    { evmSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' },
                    out) true := by
              simpa [evmSolm, hVatAddr, hAmtWord] using hcallSolmRaw
            cases z
            · have hbody :
                  ExecTransitionBody config contract evmSolm (endCashStore I)
                    cashTransition.body .reverted := by
                simpa [evmSolm] using
                  endCashBodyReverts_fluxCallFailed
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmFlux :=
                      { evmSolm with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' })
                    (out := out)
                    hwv hsz68 hfixSolm hfitSolm hvatCodeSolmNE
                    (by simpa [evmSolm] using hcallSolm)
              exact (endCashX_fluxCallFailed (g := g) rd9855 hout)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · let evmFluxEvm :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ'
                  substate := A'
                  createdAccounts := cA' }
              let evmFluxSolm :=
                { evmSolm with
                  accountMap := σ'_solm
                  substate := A'_solm
                  createdAccounts := cA' }
              have hsrcFlux : evmFluxSolm.executionEnv.source = I.source := by
                simp [evmFluxSolm, evmSolm, initState]
              have houtCouple :
                  endCashOutWord σ' I =
                    Solm.EVM.storageLoad evmFluxSolm evmFluxSolm.executionEnv.codeOwner
                      (endCashOutSlot I) := by
                have hload := hStateCall.storageLoad_codeOwner (endCashOutSlot I)
                simpa [evmFluxEvm, evmFluxSolm, initState, Solm.EVM.storageLoad,
                  State.lookupAccount, endCashOutWord, endSlotWord, solcSlotWord] using hload
              obtain ⟨_, _, rdAddEntry⟩ := endCashX_outAddEntry (g := g) hsz68 rd9855
              by_cases hoverAdd :
                  UInt256.size ≤
                    (endCashOutWord σ' I).toNat + (endCashWadWord I).toNat
              · have hoverSolm :
                    UInt256.size ≤
                      (Solm.EVM.storageLoad evmFluxSolm evmFluxSolm.executionEnv.codeOwner
                            (endCashOutSlot I)).toNat +
                        (endCashWadWord I).toNat := by
                  rw [← houtCouple]
                  exact hoverAdd
                have hbody :
                    ExecTransitionBody config contract evmSolm (endCashStore I)
                      cashTransition.body .reverted := by
                  simpa [evmFluxSolm, evmSolm] using
                    endCashBodyReverts_outAddOverflow
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g)
                      (evmFlux := evmFluxSolm) (out := out)
                      hwv hsz68 hfixSolm hfitSolm hvatCodeSolmNE
                      (by simpa [evmFluxSolm, evmSolm] using hcallSolm)
                      hsrcFlux hoverSolm
                exact (endCashX_outAddOverflow hoverAdd rdAddEntry)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · let outNew := endCashOutWord σ' I + endCashWadWord I
                let outWordSolm :=
                  Solm.EVM.storageLoad evmFluxSolm evmFluxSolm.executionEnv.codeOwner
                    (endCashOutSlot I)
                let outNewSolm := outWordSolm + endCashWadWord I
                have hfitAdd :
                    (endCashOutWord σ' I).toNat + (endCashWadWord I).toNat <
                      UInt256.size :=
                  by omega
                have hfitAddSolm :
                    (Solm.EVM.storageLoad evmFluxSolm evmFluxSolm.executionEnv.codeOwner
                          (endCashOutSlot I)).toNat +
                        (endCashWadWord I).toNat <
                      UInt256.size := by
                  rw [← houtCouple]
                  exact hfitAdd
                obtain ⟨_, _, rdAddReturn⟩ := endCashX_outAddSuccess hfitAdd rdAddEntry
                have rdAddReturn' := by
                  simpa [outNew] using rdAddReturn
                obtain ⟨_, _, rdGuard⟩ :=
                  endCashX_outStoreGuard (g := g) (outNew := outNew)
                    hperm hsz68 rdAddReturn'
                have houtNewCouple : outNew = outNewSolm := by
                  simp [outNew, outNewSolm, outWordSolm, houtCouple]
                have hStatePost :
                    EVMStateEquiv (endCashPostState evmFluxEvm I outNew)
                      (endCashPostState evmFluxSolm I outNewSolm) := by
                  simpa [evmFluxEvm, evmFluxSolm, endCashPostState, houtNewCouple] using
                    hStateCall.storageStore_codeOwner (endCashOutSlot I) (val₁ := outNew)
                      (val₂ := outNewSolm) houtNewCouple
                have hbagPostEvm :
                    Solm.EVM.storageLoad (endCashPostState evmFluxEvm I outNew)
                      (endCashPostState evmFluxEvm I outNew).executionEnv.codeOwner
                      (endCashBagSlot I) =
                        endCashPostBagWord σ' I outNew := by
                    simp [evmFluxEvm, endCashPostState, endCashPostBagWord,
                      endCashPostAccountMap, initState, storageStore_accountMap,
                      storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, endSlotWord, solcSlotWord]
                have hbagPostSolm :
                    Solm.EVM.storageLoad (endCashPostState evmFluxSolm I outNewSolm)
                      (endCashPostState evmFluxSolm I outNewSolm).executionEnv.codeOwner
                      (endCashBagSlot I) =
                        endCashPostBagWord σ' I outNew := by
                  rw [← hStatePost.storageLoad_codeOwner (endCashBagSlot I)]
                  exact hbagPostEvm
                by_cases hgt : (endCashPostBagWord σ' I outNew).toNat < outNew.toNat
                · have hgtSolm :
                      let outWord :=
                        Solm.EVM.storageLoad evmFluxSolm
                          evmFluxSolm.executionEnv.codeOwner (endCashOutSlot I)
                      let outNew := outWord + endCashWadWord I
                      let evmPost := endCashPostState evmFluxSolm I outNew
                      (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner
                          (endCashBagSlot I)).toNat <
                        outNew.toNat := by
                    simpa [outWordSolm, outNewSolm, hbagPostSolm, houtNewCouple] using hgt
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endCashStore I)
                        cashTransition.body .reverted := by
                    simpa [evmFluxSolm, evmSolm, outWordSolm, outNewSolm] using
                      endCashBodyReverts_outExceedsBag
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g)
                        (evmFlux := evmFluxSolm) (out := out)
                        hwv hsz68 hfixSolm hfitSolm hvatCodeSolmNE
                        (by simpa [evmFluxSolm, evmSolm] using hcallSolm)
                        hsrcFlux hfitAddSolm hgtSolm
                  exact (endCashX_outRequireReverts (outNew := outNew) hgt rdGuard)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hle :
                      outNew.toNat ≤ (endCashPostBagWord σ' I outNew).toNat :=
                    Nat.le_of_not_gt hgt
                  have hleSolm :
                      let outWord :=
                        Solm.EVM.storageLoad evmFluxSolm
                          evmFluxSolm.executionEnv.codeOwner (endCashOutSlot I)
                      let outNew := outWord + endCashWadWord I
                      let evmPost := endCashPostState evmFluxSolm I outNew
                      outNew.toNat ≤
                        (Solm.EVM.storageLoad evmPost evmPost.executionEnv.codeOwner
                          (endCashBagSlot I)).toNat := by
                    simpa [outWordSolm, outNewSolm, hbagPostSolm, houtNewCouple] using hle
                  have hret := endCashX_outRequireReturns
                    (outNew := outNew) hperm hle rdGuard
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endCashStore I)
                        cashTransition.body
                        (.returned
                          { contract := contract,
                            locals := endCashStoreOutNew σ_solm I outNewSolm }
                          (endCashPostState evmFluxSolm I outNewSolm) none) := by
                    simpa [evmFluxSolm, evmSolm, outWordSolm, outNewSolm] using
                      endCashBodyReturns
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g)
                        (evmFlux := evmFluxSolm) (out := out)
                        hwv hsz68 hfixSolm hfitSolm hvatCodeSolmNE
                        (by simpa [evmFluxSolm, evmSolm] using hcallSolm)
                        hsrcFlux hfitAddSolm hleSolm
                  exact hret.reEquivExecutionGenEVMStateEquiv
                    (evm'_evm := endCashPostState evmFluxEvm I outNew)
                    (evm'_solm := endCashPostState evmFluxSolm I outNewSolm)
                    hcode hdispatch hdecode hbody
                    (by
                      simp [evmFluxEvm, endCashPostState, initState,
                        storageStore_createdAccounts])
                    (by
                      simpa [evmFluxEvm, endCashPostState, initState,
                        storageStore_accountMap, endCashPostAccountMap] using
                          accountMapEquiv.refl (endCashPostAccountMap σ' I outNew))
                    hStatePost
                    (by
                      simpa [cashTransition] using
                        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                          (t := []) (dvs := []) rfl (by native_decide)
                          (by native_decide)))
          · rw [not_lt] at hdepthLt
            have hdepthEq : I.depth = 1024 :=
              Fin.ext (by have := I.depth.isLt; omega)
            obtain ⟨_, _, rd9855⟩ :=
              endCashX_fluxCallDepthLimit (g := g) hcallReady hdepthEq
            let A_flux :=
              (evmSolm.addAccessedAccount (EVM.address (endCashVatAddr σ_solm I))).substate
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endCashVatAddr σ_solm I)) "flux" 0
                  [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
                    .address I.source,
                    .int (Int.ofNat (endCashAmtWord σ_solm I).toNat)]
                  (false, { evmSolm with substate := A_flux }, ByteArray.empty) true := by
              simpa [evmSolm, A_flux] using
                (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                  (tgt := EVM.address (endCashVatAddr σ_solm I)) (name := "flux")
                  (args :=
                    [.fixedBytes bytes32Width (endCashIlkBytes I), .address I.codeOwner,
                      .address I.source,
                      .int (Int.ofNat (endCashAmtWord σ_solm I).toNat)])
                  (callPerm := true)
                  (endCashFluxEncode_eq σ_solm I (endCashAmtWord σ_solm I)
                    hsz68 (endCashFixHashMem2_size I))
                  (by simpa [evmSolm, initState] using hdepthEq))
            have hbody :
                ExecTransitionBody config contract evmSolm (endCashStore I)
                  cashTransition.body .reverted := by
              simpa [evmSolm] using
                endCashBodyReverts_fluxCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmFlux := { evmSolm with substate := A_flux })
                  (out := ByteArray.empty)
                  hwv hsz68 hfixSolm hfitSolm hvatCodeSolmNE
                  (by simpa [evmSolm] using hcallSolm)
            exact (endCashX_fluxCallFailed (g := g) rd9855 (by native_decide))
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endCashBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
