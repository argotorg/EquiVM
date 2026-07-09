import Benchmarks.Dss.End.Pack
import Benchmarks.Dss.End.Cash
import Benchmarks.Dss.End.Thaw

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `flow(bytes32)` transition -/

abbrev endFlowConcreteSelector : ByteArray := selectorBytes 0x4a 0x10 0xea 0xa6

abbrev endFlowIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endFlowIlkValue (I : ExecutionEnv) : Value := endBytes32ArgValue I

abbrev endFlowStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endFlowIlkValue I)

abbrev endFlowIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endFlowFixEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "fix", steps := [.mindex (endFlowIlkKey I)] }

abbrev endFlowFixSlot (I : ExecutionEnv) : UInt256 := fixSlot (endFlowIlkKey I)

abbrev endFlowFixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endFlowFixSlot I) σ I

abbrev endFlowDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

abbrev endFlowEntryPc : UInt256 := ⟨635⟩
abbrev endFlowReturnPc : UInt256 := ⟨562⟩
abbrev endFlowDecodedPc : UInt256 := ⟨657⟩
abbrev endFlowBodyPc : UInt256 := ⟨2718⟩
abbrev endFlowFixDefinedRawWord : UInt256 :=
  ⟨0x456e642f6669782d696c6b2d616c72656164792d646566696e65640000000000⟩

abbrev endFlowFixLogTopic : UInt256 :=
  ⟨0x8d1d5ae676a6db1f6f14414f8a6c78941bbfb700fe3f3be6d3245f26c2f2d550⟩

abbrev endFlowVatIlksSelectorWord : UInt256 := ⟨0xd9638d36⟩

abbrev endFlowVatIlksSelectorShifted : UInt256 :=
  ⟨0xd9638d3600000000000000000000000000000000000000000000000000000000⟩

abbrev endFlowVatIlksOutPtr : UInt256 := ⟨128⟩

abbrev endFlowVatIlksInSize : UInt256 := ⟨36⟩

abbrev endFlowVatIlksOutSize : UInt256 := ⟨160⟩

abbrev endFlowVatIlksEndPtr : UInt256 := ⟨164⟩

abbrev endFlowVatIlkArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endFlowVatIlkRateWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev endFlowVatIlkSpotWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

abbrev endFlowVatIlkLineWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 96 128))

abbrev endFlowVatIlkDustWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 128 160))

abbrev endFlowStoreVatIlk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStore I).insert "vatIlk"
    (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
      .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])

abbrev endFlowStoreRate (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreVatIlk I out).insert "rate"
    (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat))

abbrev endFlowArtSlot (I : ExecutionEnv) : UInt256 := ArtSlot (endFlowIlkKey I)

abbrev endFlowArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "Art", steps := [.mindex (endFlowIlkKey I)] }

abbrev endFlowArtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endFlowArtSlot I) σ I

abbrev endFlowTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endFlowIlkKey I)

abbrev endFlowTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endFlowIlkKey I)] }

abbrev endFlowTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endFlowTagSlot I) σ I

abbrev endFlowGapSlot (I : ExecutionEnv) : UInt256 := gapSlot (endFlowIlkKey I)

abbrev endFlowGapEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gap", steps := [.mindex (endFlowIlkKey I)] }

abbrev endFlowGapWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endFlowGapSlot I) σ I

abbrev endFlowWad0Word (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.div (endFlowArtWord σ I * endFlowVatIlkRateWord out) endRayWord

abbrev endFlowStoreWad0 (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreRate I out).insert "wad0"
    (.int (Int.ofNat (endFlowWad0Word σ I out).toNat))

abbrev endFlowWadWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.div (endFlowWad0Word σ I out * endFlowTagWord σ I) endRayWord

abbrev endFlowStoreWad (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreWad0 σ I out).insert "wad"
    (.int (Int.ofNat (endFlowWadWord σ I out).toNat))

abbrev endFlowNum0Word (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.sub (endFlowWadWord σ I out) (endFlowGapWord σ I)

abbrev endFlowStoreNum0 (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreWad σ I out).insert "num0"
    (.int (Int.ofNat (endFlowNum0Word σ I out).toNat))

abbrev endFlowNumWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  endFlowNum0Word σ I out * endRayWord

abbrev endFlowStoreNum (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreNum0 σ I out).insert "num"
    (.int (Int.ofNat (endFlowNumWord σ I out).toNat))

abbrev endFlowDenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (endFlowDebtWord σ I) endRayWord

abbrev endFlowStoreDen (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreNum σ I out).insert "den"
    (.int (Int.ofNat (endFlowDenWord σ I).toNat))

abbrev endFlowFixVWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.div (endFlowNumWord σ I out) (endFlowDenWord σ I)

abbrev endFlowStoreFixV (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFlowStoreDen σ I out).insert "fixV"
    (.int (Int.ofNat (endFlowFixVWord σ I out).toNat))

def endFlowPostState (evm : EVM.State) (I : ExecutionEnv) (fixV : UInt256) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endFlowFixSlot I) fixV

def endFlowPostAccountMap (σ : AccountMap) (I : ExecutionEnv) (fixV : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (endFlowFixSlot I) fixV

noncomputable def endFlowFixHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem

noncomputable def endFlowVatIlksSelectorMem (mem : ByteArray) : ByteArray :=
  endFlowVatIlksSelectorShifted.toByteArray.write 0 mem endFlowVatIlksOutPtr.toNat 32

noncomputable def endFlowVatIlksArg0Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (endFlowIlkWord I).toByteArray.write 0 (endFlowVatIlksSelectorMem mem)
    (endFlowVatIlksOutPtr + ⟨4⟩).toNat 32

noncomputable def endFlowVatIlksCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  endFlowVatIlksArg0Mem I mem

noncomputable def endFlowVatIlksPostCallMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  out.write 0 (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) endFlowVatIlksOutPtr.toNat
    (min endFlowVatIlksOutSize.toNat out.size)

theorem endFlow_wordAt0Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem endFlow_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [endFlow_wordAt0Mem_size_of_ge64 key hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    endFlow_wordAt0Mem_size_of_ge64 key hmem]
  omega

theorem endFlow_twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [endFlow_wordAt0Mem_size_of_ge64 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem endFlow_twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size])
      (by rw [endFlow_wordAt0Mem_size_of_ge64 key hmem]; omega)]
  rw [toByteArray_extract_all]

theorem endFlow_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmem64 : 64 ≤ mem.size := by omega
  have hword0 : (wordAt0Mem key mem).size = mem.size :=
    endFlow_wordAt0Mem_size_of_ge64 key hmem64
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hword0]; omega) (by omega) (by rw [hword0]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem endFlow_twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [endFlow_twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [endFlow_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      endFlow_twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [endFlow_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      endFlow_twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [endFlow_twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem endFlowVatIlksSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endFlowVatIlksSelectorMem mem).size = 160 := by
  unfold endFlowVatIlksSelectorMem
  exact toByteArray_write32_size_of_ge mem endFlowVatIlksSelectorShifted
    128 96 160 hmem (by omega) (by native_decide) (by omega)

theorem endFlowVatIlksSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFlowVatIlksSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksSelectorMem
  change (endFlowVatIlksSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding
    64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap endFlowVatIlksSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem endFlowVatIlksArg0Mem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFlowVatIlksArg0Mem I mem).size = 164 := by
  unfold endFlowVatIlksArg0Mem
  exact toByteArray_write32_size_of_le (endFlowVatIlksSelectorMem mem) (endFlowIlkWord I)
    132 160 164 (endFlowVatIlksSelectorMem_size hmem)
    (by rw [endFlowVatIlksSelectorMem_size hmem]; omega) (by omega)

theorem endFlowVatIlksArg0Mem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFlowVatIlksArg0Mem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksArg0Mem
  change ((endFlowIlkWord I).toByteArray.write 0 (endFlowVatIlksSelectorMem mem)
      132 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endFlowVatIlksSelectorMem_size hmem]; omega) (by omega),
    endFlowVatIlksSelectorMem_read64 hmem hread64]

theorem endFlowVatIlksCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFlowVatIlksCalldataMem I mem).size = 164 := by
  unfold endFlowVatIlksCalldataMem
  exact endFlowVatIlksArg0Mem_size I hmem

theorem endFlowVatIlksCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFlowVatIlksCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksCalldataMem
  exact endFlowVatIlksArg0Mem_read64 I hmem hread64

theorem endFlowVatIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endFlowVatIlksPostCallMem I out).size = 288 := by
  unfold endFlowVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  change (out.write 0 (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) 128 160).size =
    288
  rw [write_eq_gen_extend out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
    128 160
    (by omega) (by omega)
    (by
      rw [endFlowFixHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
      omega)
    (by
      rw [endFlowFixHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
      omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endFlowFixHashMem]
  rw [endFlowVatIlksCalldataMem_size I
    (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
  omega

theorem endFlowVatIlksPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endFlowVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  change ByteArray.readWithPadding
      (out.write 0 (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) 128 160) 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
    128 160 64 (by omega) (by omega)
    (by
      rw [endFlowFixHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
      omega)
    (by omega)]
  exact endFlowVatIlksCalldataMem_read64 I
    (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size
      solcFreePtrMem_read64)

theorem endFlowVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray) :
    64 < (endFlowVatIlksPostCallMem I out).size := by
  unfold endFlowVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endFlowFixHashMem]
    rw [endFlowVatIlksCalldataMem_size I
      (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
    omega
  · by_cases hext :
        (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size < 128 + min 160 out.size
    · rw [write_eq_gen_extend out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _)
        (by
          rw [endFlowFixHashMem]
          rw [endFlowVatIlksCalldataMem_size I
            (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
          omega)
        hext]
      have hbaseSize : (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size = 164 := by
        rw [endFlowFixHashMem]
        exact endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      have hprefix :
          ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract 0 128).size =
            128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      rw [ByteArray.size_append, hprefix, hsrc]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega
    · have hin :
          128 + min 160 out.size ≤
            (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size := by
        omega
      rw [write_eq_gen out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
        128 (min 160 out.size) hlen0 (Nat.min_le_right _ _) hin]
      have hbaseSize : (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size = 164 := by
        rw [endFlowFixHashMem]
        exact endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      have hprefix :
          ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract 0 128).size =
            128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      have htail :
          ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract
            (128 + min 160 out.size)
            (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size).size =
              164 - (128 + min 160 out.size) := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc, htail]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega

theorem endFlowVatIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endFlowVatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endFlowVatIlksCalldataMem_read64 I
      (by
        rw [endFlowFixHashMem]
        exact twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      (by
        rw [endFlowFixHashMem]
        exact twoWordHashMem_read64 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
  · rw [write_read_below_gen_extend out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
      128 (min 160 out.size) 64 hlen0 (Nat.min_le_right _ _)
      (by
        rw [endFlowFixHashMem]
        rw [endFlowVatIlksCalldataMem_size I
          (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
        omega)
      (by native_decide)]
    exact endFlowVatIlksCalldataMem_read64 I
      (by
        rw [endFlowFixHashMem]
        exact twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      (by
        rw [endFlowFixHashMem]
        exact twoWordHashMem_read64 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)

theorem endFlowVatIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endFlowVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endFlowVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by exact endFlowVatIlksPostCallMem_size_gt64 I out)
    (by decide)
    (endFlowVatIlksPostCallMem_read64 I out)

theorem endFlowVatIlksPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endFlowVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endFlowVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endFlowVatIlksPostCallMem_size_long I out hlo]; decide)
    (by decide)
    (endFlowVatIlksPostCallMem_read64_long I out hlo)

theorem endFlowVatIlksPostCallMem_read160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (endFlowVatIlksPostCallMem I out).readWithPadding 160 32 = out.extract 32 64 := by
  unfold endFlowVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
    128 160
    (by omega) (by omega)
    (by
      rw [endFlowFixHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
      omega)
    (by
      rw [endFlowFixHashMem]
      rw [endFlowVatIlksCalldataMem_size I
        (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
      omega)]
  have hprefix :
      ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    rw [endFlowFixHashMem]
    rw [endFlowVatIlksCalldataMem_size I
      (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)]
    omega
  have hsrc : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract 0 128 ++
        out.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤
        ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).extract 0 128 ++
          out.extract 0 160).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endFlowVatIlksPostCallMem_mload160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 160 ≤ out.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endFlowVatIlksPostCallMem I out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endFlowVatIlksPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      endFlowVatIlkRateWord out := by
  unfold endFlowVatIlkRateWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((endFlowVatIlksPostCallMem I out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [endFlowVatIlksPostCallMem_read160_long I out hlo]
  · exact not_or.mpr
      ⟨by rw [endFlowVatIlksPostCallMem_size_long I out hlo]; decide, by native_decide⟩

theorem endFlowVatIlksSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (endFlowVatIlksSelectorMem mem).extract 128 132 = ilksSelector := by
  unfold endFlowVatIlksSelectorMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_eq endFlowVatIlksSelectorShifted mem 128 (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem endFlowVatIlksCalldataMem_read128_36 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFlowVatIlksCalldataMem I mem).readWithPadding 128 36 =
      ilksSelector ++ (endFlowIlkWord I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [endFlowVatIlksCalldataMem_size I hmem])]
  unfold endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide,
    write32_eq _ (endFlowVatIlksSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [endFlowVatIlksSelectorMem_size hmem]; omega)]
  have hAsz : ((endFlowVatIlksSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, endFlowVatIlksSelectorMem_size hmem]
    omega
  have hBsz : ((endFlowIlkWord I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((endFlowVatIlksSelectorMem mem).extract 0 132 ++
        (endFlowIlkWord I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      (endFlowIlkWord I).toByteArray.extract 0 32 = (endFlowIlkWord I).toByteArray := by
    have h := @ByteArray.extract_zero_size (endFlowIlkWord I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), endFlowVatIlksSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem endFlowVatIlksEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hsz36 : 36 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "vatIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endFlowVatIlksCalldataMem I mem).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "vatIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endFlowVatIlksCalldataMem I mem).readWithPadding 128 36)
  rw [endFlowVatIlksCalldataMem_read128_36 I hmem]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endFlowIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) hsz36
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endFlowIlkWord I := by
      simpa [endBytes32ArgBytes, endFlowIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endFlowIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endFlowIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endFlow_bytesToWord_drop_take32_eq_extract (out : ByteArray) (start : ℕ) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]
  simp

theorem endFlowVatIlksDecode_ok_aux {out : ByteArray} (hlo : 160 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out =
      some [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := endFlow_bytesToWord_drop_take32_eq_extract out 0
  have hword32 := endFlow_bytesToWord_drop_take32_eq_extract out 32
  have hword64 := endFlow_bytesToWord_drop_take32_eq_extract out 64
  have hword96 := endFlow_bytesToWord_drop_take32_eq_extract out 96
  have hword128 := endFlow_bytesToWord_drop_take32_eq_extract out 128
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 0) htake0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 32) htake32]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 64) htake64]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 96) htake96]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 128) htake128]
  simp only [Option.bind_some]
  rw [hword0, hword32, hword64, hword96, hword128]

theorem endFlowVatIlksDecode_ok {out : ByteArray} (hlo : 160 ≤ out.size) :
    config.externalABI.decode? "vatIlks" out =
      some [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)] := by
  have h := endFlowVatIlksDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endFlowVatIlksDecode_none_short_aux {out : ByteArray} (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases htake0 : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) htake0]
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases htake32 : ((out.toList.drop 32).take 32).length = 32
    · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32]
      simp only [Option.bind_some]
      by_cases htake64 : ((out.toList.drop 64).take 32).length = 32
      · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 64) htake64]
        simp only [Option.bind_some]
        by_cases htake96 : ((out.toList.drop 96).take 32).length = 32
        · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 96) htake96]
          simp only [Option.bind_some]
          have htake128 :
              ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 128) htake128]
          simp
        · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 96) htake96]
          simp
      · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 64) htake64]
        simp
    · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32]
      simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) htake0]
    simp

theorem endFlowVatIlksDecode_none_short {out : ByteArray} (hshort : out.size < 160) :
    config.externalABI.decode? "vatIlks" out = none := by
  have h := endFlowVatIlksDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endFlowVatIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFlowVatIlksOutSize (UInt256.ofNat out.size)).toNat = min 160 out.size := by
  change (min (UInt256.ofNat 160) (UInt256.ofNat out.size)).toNat = min 160 out.size
  by_cases hle : 160 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 160 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 160)]
    exact umin_ofNat_right_toNat_of_lt (c := 160) (n := out.size) (by decide) hlt hout

theorem endFlowFixSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixSlot I = solcMappingSlot ⟨15⟩ (endFlowIlkWord I) := by
  unfold endFlowFixSlot endFlowIlkKey fixSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endFlowArtSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFlowArtSlot I = solcMappingSlot ⟨14⟩ (endFlowIlkWord I) := by
  unfold endFlowArtSlot endFlowIlkKey ArtSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endFlowTagSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFlowTagSlot I = solcMappingSlot ⟨12⟩ (endFlowIlkWord I) := by
  unfold endFlowTagSlot endFlowIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endFlowGapSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFlowGapSlot I = solcMappingSlot ⟨13⟩ (endFlowIlkWord I) := by
  unfold endFlowGapSlot endFlowIlkKey gapSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem RD.endFlowFixDefinedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨2807⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
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
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endFlowFixDefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ endFlowFixDefinedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ endFlowFixDefinedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endDecode_flow_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = some (endFlowStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, endFlowStore, endFlowIlkValue, endFlowIlkWord, bytes32, bytes32Width,
    abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_flow_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem endReachFlowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFlowConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFlowEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x4a10eaa6⟩ :=
    endSelWord_eq_of_beq I hsz 0x4a 0x10 0xea 0xa6 ⟨0x4a10eaa6⟩
      (by native_decide)
      (by simpa [selIs, endFlowConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endFlowEntryPc 0 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endFlowX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endFlowEntryPc) (ret := endFlowReturnPc)
    (decoded := endFlowDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endFlowDecodedPc) (ret := endFlowReturnPc)
    (routine := endFlowBodyPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endFlowIlkWord, calldataWord] using hroutine⟩

theorem endFlowX_debtZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hdebt : endFlowDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2721 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2722raw⟩ := rd2721.sload (by native_decide) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd2722zero := rd2722raw
  rw [hdebtRaw] at rd2722zero
  obtain ⟨_, _, rd2722⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2722⟩
        (⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endFlowBodyPc] using rd2722zero⟩
  have rd2725 := rd2722.push2 ⟨2786⟩ (by native_decide) (by evm_ov)
  have rd2726 := rd2725.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2726⟩
        [endFlowIlkWord I, endFlowReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd2726⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2726⟩) (len := ⟨13⟩)
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

theorem endFlowX_fixNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endFlowIlkWord I
  have hslot : endFlowFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endFlowFixSlot_eq (I := I) hsz36
  have rd2721 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2722raw⟩ := rd2721.sload (by native_decide) (by evm_ov)
  have rd2722 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2722⟩
        (endFlowDebtWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using rd2722raw⟩
  obtain ⟨_, _, rd2722⟩ := rd2722
  have rd2725 := rd2722.push2 ⟨2786⟩ (by native_decide) (by evm_ov)
  have rd2786 := rd2725.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)
  have rd2790pre := evm_run rd2786 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2791 := rd2790pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2796pre := evm_run rd2791 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2797 := rd2796pre.mstore 0 (twoWordHashMem key ⟨15⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2800pre := evm_run rd2797 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨15⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨15⟩ key solcFreePtrMem_size
  have rd2801pre := rd2800pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2802raw⟩ := rd2801pre.sload (by native_decide) (by evm_ov)
  have rd2802 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2802⟩
        (endFlowFixWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    have hfixRaw :
        solcSlotWord σ I (solcMappingSlot ⟨15⟩ key) = endFlowFixWord σ I := by
      rw [← hslot]
      simp [endFlowFixWord, endSlotWord]
    exact ⟨_, _, by simpa [hfixRaw] using rd2802raw⟩
  obtain ⟨_, _, rd2802⟩ := rd2802
  have rd2803raw := rd2802.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endFlowFixWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hfix
  have rd2803 := rd2803raw
  rw [hzero] at rd2803
  have rd2806 := rd2803.push2 ⟨2883⟩ (by native_decide) (by evm_ov)
  have rd2807 := rd2806.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2807⟩
        [endFlowIlkWord I, endFlowReturnPc, sel]
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd2807⟩
  exact RD.endFlowFixDefinedRevert rdTail
    (twoWordHashMem_size_96 key ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_vatIlksExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2948⟩
      (endPackVatWord σ I :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  let key := endFlowIlkWord I
  have hslot : endFlowFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endFlowFixSlot_eq (I := I) hsz36
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
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size = 164 :=
    endFlowVatIlksCalldataMem_size I
      (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
  have hcallRead64 :
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endFlowVatIlksCalldataMem_read64 I
      (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size
        solcFreePtrMem_read64)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ I) = endPackVatWord σ I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ I)
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd2721 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2722raw⟩ := rd2721.sload (by native_decide) (by evm_ov)
  have rd2722 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2722⟩
        (endFlowDebtWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using rd2722raw⟩
  obtain ⟨_, _, rd2722⟩ := rd2722
  have rd2725 := rd2722.push2 ⟨2786⟩ (by native_decide) (by evm_ov)
  have rd2786 := rd2725.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)
  have rd2790pre := evm_run rd2786 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2791 := rd2790pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2796pre := evm_run rd2791 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2797 := rd2796pre.mstore 0 (twoWordHashMem key ⟨15⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2800pre := evm_run rd2797 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨15⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨15⟩ key solcFreePtrMem_size
  have rd2801pre := rd2800pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2802raw⟩ := rd2801pre.sload (by native_decide) (by evm_ov)
  have rd2802 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2802⟩
        (endFlowFixWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    have hfixRaw :
        solcSlotWord σ I (solcMappingSlot ⟨15⟩ key) = endFlowFixWord σ I := by
      rw [← hslot]
      simp [endFlowFixWord, endSlotWord]
    exact ⟨_, _, by simpa [hfixRaw] using rd2802raw⟩
  obtain ⟨_, _, rd2802⟩ := rd2802
  have rd2803raw := rd2802.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endFlowFixWord σ I) = ⟨1⟩ := by
    rw [hfix]
    native_decide
  have rd2803 := rd2803raw
  rw [hzero] at rd2803
  have rd2806 := rd2803.push2 ⟨2883⟩ (by native_decide) (by evm_ov)
  have rd2883 := rd2806.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2886 := evm_run rd2883 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2887raw⟩ := rd2886.sload (by native_decide) (by evm_ov)
  have rd2887 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2887⟩
        (endSlotWord ⟨1⟩ σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd2887raw⟩
  obtain ⟨_, _, rd2887⟩ := rd2887
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFlowFixHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFlowFixHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endFlowFixHashMem, twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩
        solcFreePtrMem_size]; decide)
      (by decide)
      (by
        rw [endFlowFixHashMem]
        exact twoWordHashMem_read64 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
  have rd2948 := evm_run rd2887 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endFlowVatIlksSelectorMem (endFlowFixHashMem I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr, endFlowFixHashMem, key,
          hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksCalldataMem, endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr,
          endFlowFixHashMem, key])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksSelectorMem, endFlowVatIlksArg0Mem, endFlowVatIlksCalldataMem,
      endFlowFixHashMem,
      endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
      endFlowVatIlksEndPtr, endFlowVatIlksSelectorShifted, endFlowVatIlksSelectorWord,
      endPackVatWord, endSlotWord, solcSlotWord, solcAddrMask, hselectorShift, hvatMask,
      hinSize, hendPtr, u256_land_comm]
      using rd2948⟩

theorem endFlowX_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2948⟩ := endFlowX_vatIlksExtcodesizeGuard hsz36 hdebt hfix h
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2948⟩) (okPc := ⟨2960⟩) rd2948
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_vatIlksCallReady {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2963⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd2948⟩ := endFlowX_vatIlksExtcodesizeGuard hsz36 hdebt hfix h
  obtain ⟨gasWord, k', C', rd2963⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2948⟩) (okPc := ⟨2960⟩) rd2948
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd2963⟩

theorem endFlowX_vatIlksPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2963⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 6)
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
          ((endFlowVatIlksCalldataMem I (endFlowFixHashMem I)).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endPackVatWord σ I :: ⟨0⟩ ::
            endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
          (endFlowVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd2964raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endFlowVatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
      native_decide
    simpa [endFlowVatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd2964raw

theorem endFlowX_vatIlksCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2963⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksCalldataMem I (endFlowFixHashMem I)) (UInt256.ofNat 9)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd2964raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFlowVatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd2964raw

theorem endFlowX_vatIlksCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨2964⟩) (okPc := ⟨2980⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_vatIlksCallSucceeded {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σ I :: ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2982⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨2964⟩) (okPc := ⟨2980⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endFlowX_vatIlksReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2982⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hlo : 160 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3010⟩
      (endFlowVatIlkRateWord out :: ⟨32⟩ :: ⟨0⟩ :: endFlowIlkWord I ::
        endFlowReturnPc :: sel :: [])
      (endFlowVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k' C' := by
  have hmload64 := endFlowVatIlksPostCallMem_mload64 I out
  have hmload160Raw := endFlowVatIlksPostCallMem_mload160_long I out hlo
  have hmload160 :
      (if ((⟨32⟩ : UInt256) + ⟨128⟩).toNat ≥
            (endFlowVatIlksPostCallMem I out).size
          ∨ (⟨32⟩ : UInt256) + ⟨128⟩ ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((endFlowVatIlksPostCallMem I out).readWithPadding
            ((⟨32⟩ : UInt256) + ⟨128⟩).toNat 32))) =
        endFlowVatIlkRateWord out := by
    simpa [show ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ by native_decide]
      using hmload160Raw
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd2994 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3002⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd2994
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd3010 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endFlowVatIlkRateWord out) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksOutSize] using rd3010⟩

theorem endFlowX_vatIlksReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2982⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (endFlowVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C)
    (hshort : out.size < 160) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endFlowVatIlksPostCallMem_mload64 I out
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd2994 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3002⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd2994
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_wad0RmulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3010⟩
      (endFlowVatIlkRateWord out :: ⟨32⟩ :: ⟨0⟩ :: endFlowIlkWord I ::
        endFlowReturnPc :: sel :: [])
      (endFlowVatIlksPostCallMem I out) (UInt256.ofNat 9) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (endFlowVatIlkRateWord out :: endFlowArtWord σ' I :: ⟨3041⟩ ::
        ⟨3061⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord out :: endFlowIlkWord I ::
        endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out))
      (UInt256.ofNat 9) out (cA', σ') k' C' := by
  let key := endFlowIlkWord I
  have hslot : endFlowArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [key] using endFlowArtSlot_eq (I := I) hsz36
  have hmemSize :
      (endFlowVatIlksPostCallMem I out).size = 288 :=
    endFlowVatIlksPostCallMem_size_long I out hlo
  have rd3014pre := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3015 := rd3014pre.mstore 0
    (wordAt0Mem key (endFlowVatIlksPostCallMem I out))
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key]) (by native_decide) (by evm_ov)
  have rd3020pre := evm_run rd3015 with [
    raw push1 ⟨14⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd3020 := rd3020pre.mstore 0
    (twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out))
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0
          (wordAt0Mem key (endFlowVatIlksPostCallMem I out)) 32 32 =
        (⟨14⟩ : UInt256).toByteArray.write 0
          (wordAt0Mem key (endFlowVatIlksPostCallMem I out)) 32 32
      rfl)
    (by native_decide) (by evm_ov)
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)).readWithPadding
            0 64))) =
        solcMappingSlot ⟨14⟩ key :=
    endFlow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨14⟩ key
      (by rw [hmemSize]; omega)
  have rd3023pre := evm_run rd3020 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3024pre := rd3023pre.keccak256 0 (solcMappingSlot ⟨14⟩ key)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3025raw⟩ := rd3024pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3025⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3025⟩
        (endFlowArtWord σ' I :: endFlowVatIlkRateWord out :: ⟨0⟩ :: ⟨0⟩ ::
          endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out))
        (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endFlowArtWord, endSlotWord, solcSlotWord, key, hslot] using rd3025raw⟩
  have rd10114 := evm_run rd3025 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨3061⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3041⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [key] using rd10114⟩

theorem endFlowX_wadRmulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3041⟩
      (endFlowWad0Word σ' I out :: ⟨3061⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (endFlowTagWord σ' I :: endFlowWad0Word σ' I out :: ⟨3061⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord out :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k' C' := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  have hslot : endFlowTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endFlowTagSlot_eq (I := I) hsz36
  have hmemSize : mem14.size = (endFlowVatIlksPostCallMem I out).size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by
        have hbase := endFlowVatIlksPostCallMem_size_gt64 I out
        omega)
  have rd3046pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3047 := rd3046pre.mstore 0 (wordAt0Mem key mem14)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem14]) (by native_decide) (by evm_ov)
  have rd3051pre := evm_run rd3047 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3052 := rd3051pre.mstore 0 (twoWordHashMem key ⟨12⟩ mem14)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      change (⟨12⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem14) 32 32 =
        (⟨12⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem14) 32 32
      rfl)
    (by native_decide) (by evm_ov)
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ mem14).readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ key :=
    endFlow_twoWordHashMem_solcMappingSlot_of_ge64 ⟨12⟩ key
      (by
        rw [hmemSize]
        exact le_of_lt (endFlowVatIlksPostCallMem_size_gt64 I out))
  have rd3055pre := evm_run rd3052 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3056pre := rd3055pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3057raw⟩ := rd3056pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3057⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3057⟩
        (endFlowTagWord σ' I :: endFlowWad0Word σ' I out :: ⟨3061⟩ :: ⟨0⟩ ::
          endFlowVatIlkRateWord out :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ mem14) (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endFlowTagWord, endSlotWord, solcSlotWord, key, hslot, mem14] using rd3057raw⟩
  have rd10114 := evm_run rd3057 with [
    raw push2 ⟨10114⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [key, mem14] using rd10114⟩

theorem endFlowX_mulHelperOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {x y ret aw : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ret :: R) mem aw rdata acc k C)
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
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem endFlowX_mulHelperReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {x y ret aw : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (x * y :: R) mem aw rdata acc k' C' := by
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

theorem endFlowX_mulHelperReturnsZero {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {x y ret aw : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hy : y = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (x * y :: R) mem aw rdata acc k' C' := by
  have hyZero : UInt256.isZero y ≠ ⟨0⟩ := by
    rw [hy]
    native_decide
  have rd10179 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨10197⟩ (by native_decide) (by evm_ov)]
  have rd10197 := rd10179.jumpiT (by native_decide) hyZero (by jump_dest) (by evm_ov)
  have rd10108pre := evm_run rd10197 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10108 := rd10108pre.jumpiT (by native_decide) hyZero (by jump_dest) (by evm_ov)
  have rdRet := evm_run rd10108 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) hret (by evm_ov)]
  exact ⟨_, _, by simpa [hy] using rdRet⟩

theorem endFlowX_rmulMulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
        (y :: x :: ret :: R) mem (UInt256.ofNat 9) rdata (cA', σ') k C)
      (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (y :: x :: ⟨10139⟩ :: endRayWord :: ⟨0⟩ :: y :: x :: ret :: R)
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
    have rd10130 := evm_run h with [
      raw jumpdest (by native_decide)
        (by simp; omega),
      raw push1 ⟨0⟩ (by native_decide)
        (by simp; omega)]
    have rd10130ray := rd10130.pushConst endRayWord
      (width := 12) (op := .PUSH12) (by decide) (by native_decide)
      (by simp; omega)
    have rd10170 := evm_run rd10130ray with [
      raw push2 ⟨10139⟩ (by native_decide)
        (by simp; omega),
      raw dup5 (by native_decide)
        (by simp; omega),
      raw dup5 (by native_decide)
        (by simp; omega),
      raw push2 ⟨10170⟩ (by native_decide)
        (by simp; omega),
      raw jump (by native_decide) (by jump_dest)
        (by simp; omega)]
    exact ⟨_, _, by simpa [endRayWord] using rd10170⟩

theorem endFlowX_rmulOverflow {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (y :: x :: ret :: R) mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hov : R.length + 21 ≤ 1024) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hmul⟩ := endFlowX_rmulMulEntry h (by omega)
  exact endFlowX_mulHelperOverflow
      (x := x) (y := y) (ret := ⟨10139⟩)
      (R := [endRayWord, ⟨0⟩, y, x, ret] ++ R)
      (mem := mem) hover (by simpa using hmul)
      (by simp; omega)

theorem endFlowX_rmulReturns {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (y :: x :: ret :: R) mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div (x * y) endRayWord :: R) mem (UInt256.ofNat 9) rdata
      (cA', σ') k' C' := by
  obtain ⟨_, _, hmul⟩ := endFlowX_rmulMulEntry h (by omega)
  obtain ⟨_, _, hretMul⟩ :=
    endFlowX_mulHelperReturns
      (x := x) (y := y) (ret := ⟨10139⟩)
        (R := [endRayWord, ⟨0⟩, y, x, ret] ++ R)
        (mem := mem) hfit hy (by simpa using hmul) (by jump_dest)
        (by simp; omega)
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10146pre := evm_run hretMul with [
    raw jumpdest (by native_decide)
      (by simp; omega),
    raw dup2 (by native_decide)
      (by simp; omega),
    raw push2 ⟨10146⟩ (by native_decide)
      (by simp; omega)]
  have rd10146 := rd10146pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by simp; omega)
  have rdRet := evm_run rd10146 with [
    raw jumpdest (by native_decide)
      (by simp; omega),
    raw div (by native_decide)
      (by simp; omega),
    raw swap4 (by native_decide)
      (by simp; omega),
    raw swap3 (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw jump (by native_decide) hret
      (by simp; omega)]
  exact ⟨_, _, by simpa [endRayWord] using rdRet⟩

theorem endFlowX_rmulReturnsZero {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (hy : y = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      (y :: x :: ret :: R) mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hret : (D_J endBytecode 0).contains ret = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.div (x * y) endRayWord :: R) mem (UInt256.ofNat 9) rdata
      (cA', σ') k' C' := by
  obtain ⟨_, _, hmul⟩ := endFlowX_rmulMulEntry h (by omega)
  obtain ⟨_, _, hretMul⟩ :=
    endFlowX_mulHelperReturnsZero
      (x := x) (y := y) (ret := ⟨10139⟩)
      (R := [endRayWord, ⟨0⟩, y, x, ret] ++ R)
      (mem := mem) hy (by simpa using hmul) (by jump_dest)
      (by simp; omega)
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10146pre := evm_run hretMul with [
    raw jumpdest (by native_decide)
      (by simp; omega),
    raw dup2 (by native_decide)
      (by simp; omega),
    raw push2 ⟨10146⟩ (by native_decide)
      (by simp; omega)]
  have rd10146 := rd10146pre.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by simp; omega)
  have rdRet := evm_run rd10146 with [
    raw jumpdest (by native_decide)
      (by simp; omega),
    raw div (by native_decide)
      (by simp; omega),
    raw swap4 (by native_decide)
      (by simp; omega),
    raw swap3 (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw pop (by native_decide)
      (by simp; omega),
    raw jump (by native_decide) hret
      (by simp; omega)]
  exact ⟨_, _, by simpa [endRayWord, hy] using rdRet⟩

theorem endFlowX_tailSubEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
      (endFlowGapWord σ' I :: endFlowWadWord σ' I out :: ⟨3119⟩ ::
        ⟨3137⟩ :: endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
        endFlowVatIlkRateWord out :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨13⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
          (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out))))
      (UInt256.ofNat 9) out (cA', σ') k' C' := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  let mem12 := twoWordHashMem key ⟨12⟩ mem14
  let mem13 := twoWordHashMem key ⟨13⟩ mem12
  have h0 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        key :: endFlowReturnPc :: sel :: [])
      mem12 (UInt256.ofNat 9) out (cA', σ') k C := by
    simpa [key, mem14, mem12] using h
  have hgapSlot : endFlowGapSlot I = solcMappingSlot ⟨13⟩ key := by
    simpa [key] using endFlowGapSlot_eq (I := I) hsz36
  have hpostSize : (endFlowVatIlksPostCallMem I out).size = 288 :=
    endFlowVatIlksPostCallMem_size_long I out hlo
  have hmem14Size : mem14.size = (endFlowVatIlksPostCallMem I out).size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmem12Size : mem12.size = mem14.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hmem14Size, hpostSize]; omega)
  have hgapHash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem13.readWithPadding 0 64))) =
        solcMappingSlot ⟨13⟩ key :=
    endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem12) ⟨13⟩ key
      (by rw [hmem12Size, hmem14Size, hpostSize]; omega)
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd3064 := evm_run h0 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd3077 := rd3064.pushConst endRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3079 := evm_run rd3077 with [
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd3080raw⟩ := rd3079.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3080⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3080⟩
        (endFlowDebtWord σ' I :: endRayWord :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem12 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using rd3080raw⟩
  have rd3084 := evm_run rd3080 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3086⟩ (by native_decide) (by evm_ov)]
  have rd3086pre := rd3084.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd3088raw := evm_run rd3086pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd3088⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3088⟩
        (endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem12 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowDenWord, endRayWord] using rd3088raw⟩
  have rd3094 := evm_run rd3088 with [
    raw push2 ⟨3137⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨3119⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd3101pre := evm_run rd3094 with [
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3102 := rd3101pre.mstore 0 (wordAt0Mem key mem12)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem12]) (by native_decide) (by evm_ov)
  have rd3107pre := evm_run rd3102 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3108 := rd3107pre.mstore 0 mem13 (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨13⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem12) 32 32 =
        mem13
      simp [mem13, twoWordHashMem, wordAt32Mem])
    (by native_decide) (by evm_ov)
  have rd3113 := evm_run rd3108 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd3114pre := rd3113.keccak256 0 (endFlowGapSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simpa [mem13, key, hgapSlot] using hgapHash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3115raw⟩ := rd3114pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3115⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3115⟩
        (endFlowGapWord σ' I :: endFlowWadWord σ' I out :: ⟨3119⟩ ::
          ⟨3137⟩ :: endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endFlowGapWord, endSlotWord, solcSlotWord, key, hgapSlot] using rd3115raw⟩
  have rd10154 := evm_run rd3115 with [
    raw push2 ⟨10154⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [key, mem14, mem12, mem13] using rd10154⟩

theorem endFlowX_tailSubUnderflow {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hlt : (endFlowWadWord σ' I out).toNat < (endFlowGapWord σ' I).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd10154⟩ := endFlowX_tailSubEntry hsz36 hlo h
  have hsubNat : (UInt256.sub (endFlowWadWord σ' I out) (endFlowGapWord σ' I)).toNat =
      UInt256.size + (endFlowWadWord σ' I out).toNat - (endFlowGapWord σ' I).toNat :=
    usub_toNat_underflow hlt
  have hgt :
      UInt256.gt (UInt256.sub (endFlowWadWord σ' I out) (endFlowGapWord σ' I))
        (endFlowWadWord σ' I out) = ⟨1⟩ := by
    show UInt256.fromBool
        (decide (UInt256.sub (endFlowWadWord σ' I out) (endFlowGapWord σ' I) >
          endFlowWadWord σ' I out)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub (endFlowWadWord σ' I out) (endFlowGapWord σ' I)).toNat >
        (endFlowWadWord σ' I out).toNat
      rw [hsubNat]
      have hgap : (endFlowGapWord σ' I).toNat < UInt256.size :=
        (endFlowGapWord σ' I).val.isLt
      omega
  have rd10165pre := evm_run rd10154 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10165 := rd10165pre
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10165
  have rd10166 := rd10165.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd10166 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endFlowX_tailMulEntry {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hleSub : (endFlowGapWord σ' I).toNat ≤ (endFlowWadWord σ' I out).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      (endRayWord :: endFlowNum0Word σ' I out :: ⟨3137⟩ ::
        endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
        endFlowVatIlkRateWord out :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨13⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
          (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out))))
      (UInt256.ofNat 9) out (cA', σ') k' C' := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  let mem12 := twoWordHashMem key ⟨12⟩ mem14
  let mem13 := twoWordHashMem key ⟨13⟩ mem12
  obtain ⟨_, _, rd10154⟩ := endFlowX_tailSubEntry hsz36 hlo h
  obtain ⟨_, _, rd3119raw⟩ :=
    RD.solcCheckedSubSuccess
      (pc := ⟨10154⟩) (okPc := ⟨10108⟩)
      (a := endFlowWadWord σ' I out) (b := endFlowGapWord σ' I)
      (ret := ⟨3119⟩)
      (R := [⟨3137⟩, endFlowDenWord σ' I, endFlowWadWord σ' I out,
        endFlowVatIlkRateWord out, key, endFlowReturnPc, sel])
      (by simpa [key, mem14, mem12, mem13] using rd10154)
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      hleSub (by jump_dest) (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3119⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
        (endFlowNum0Word σ' I out :: ⟨3137⟩ :: endFlowDenWord σ' I ::
          endFlowWadWord σ' I out :: endFlowVatIlkRateWord out :: key ::
          endFlowReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowNum0Word] using rd3119raw⟩
  have rd3120 := rd3119.jumpdest (by native_decide) (by evm_ov)
  have rd3133 := rd3120.pushConst endRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10170 := evm_run rd3133 with [
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [key, mem14, mem12, mem13] using rd10170⟩

theorem endFlowX_tailMulOverflow {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hleSub : (endFlowGapWord σ' I).toNat ≤ (endFlowWadWord σ' I out).toNat)
    (hover : UInt256.size ≤ (endFlowNum0Word σ' I out).toNat * endRayWord.toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  let mem12 := twoWordHashMem key ⟨12⟩ mem14
  let mem13 := twoWordHashMem key ⟨13⟩ mem12
  obtain ⟨_, _, rd10170⟩ := endFlowX_tailMulEntry hsz36 hlo hleSub h
  exact endFlowX_mulHelperOverflow
    (x := endFlowNum0Word σ' I out) (y := endRayWord)
    (ret := ⟨3137⟩)
    (R := [endFlowDenWord σ' I, endFlowWadWord σ' I out,
      endFlowVatIlkRateWord out, key, endFlowReturnPc, sel])
    (mem := mem13) hover (by simpa [key, mem14, mem12, mem13] using rd10170)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_tailDenGuard {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hleSub : (endFlowGapWord σ' I).toNat ≤ (endFlowWadWord σ' I out).toNat)
    (hfitMul : (endFlowNum0Word σ' I out).toNat * endRayWord.toNat < UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3137⟩
      (endFlowNumWord σ' I out :: endFlowDenWord σ' I ::
        endFlowWadWord σ' I out :: endFlowVatIlkRateWord out :: endFlowIlkWord I ::
        endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨13⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
          (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out))))
      (UInt256.ofNat 9) out (cA', σ') k' C' := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  let mem12 := twoWordHashMem key ⟨12⟩ mem14
  let mem13 := twoWordHashMem key ⟨13⟩ mem12
  obtain ⟨_, _, rd10170⟩ := endFlowX_tailMulEntry hsz36 hlo hleSub h
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, rd3137raw⟩ :=
    endFlowX_mulHelperReturns
      (x := endFlowNum0Word σ' I out) (y := endRayWord)
      (ret := ⟨3137⟩)
      (R := [endFlowDenWord σ' I, endFlowWadWord σ' I out,
        endFlowVatIlkRateWord out, key, endFlowReturnPc, sel])
      (mem := mem13) hfitMul hrayNonzero
      (by simpa [key, mem14, mem12, mem13] using rd10170)
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endFlowNumWord, key, mem14, mem12, mem13] using rd3137raw⟩

theorem endFlowInvalidError {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  rcases RD.conclude h with hoog | ⟨k', C', s', hX, hcode, hpc, _hstk, _hgas, hk, hC,
    _hmem, _haw, _hrdata, _hacc⟩
  · exact Or.inl hoog
  · have hdec' : decode s'.executionEnv.code s'.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s' = .error .InvalidInstruction := by
      have hstep' := Ethereum.EVM.step_invalid s' hdec'
      simpa [hcode] using hstep'
    have hfuel : g.toNat + 1 - k' = (g.toNat + 1 - (k' + 1)) + 1 := by
      omega
    exact Or.inr (by
      rw [hX, hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s' _ _ hstep)

theorem endFlowX_tailDenInvalid {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hleSub : (endFlowGapWord σ' I).toNat ≤ (endFlowWadWord σ' I out).toNat)
    (hfitMul : (endFlowNum0Word σ' I out).toNat * endRayWord.toNat < UInt256.size)
    (hden : endFlowDenWord σ' I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .InvalidInstruction := by
  obtain ⟨_, _, rd3137⟩ := endFlowX_tailDenGuard hsz36 hlo hleSub hfitMul h
  have rd3142 := evm_run rd3137 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3144⟩ (by native_decide) (by evm_ov)]
  have rd3143 := rd3142.jumpiNT (by native_decide) (by simpa using hden) (by evm_ov)
  exact endFlowInvalidError rd3143 (by native_decide)

theorem endFlowX_tailReturns {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 160 ≤ out.size)
    (hleSub : (endFlowGapWord σ' I).toNat ≤ (endFlowWadWord σ' I out).toNat)
    (hfitMul : (endFlowNum0Word σ' I out).toNat * endRayWord.toNat < UInt256.size)
    (hden : endFlowDenWord σ' I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
      (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩ (endFlowVatIlksPostCallMem I out)))
      (UInt256.ofNat 9) out (cA', σ') k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', endFlowPostAccountMap σ' I (endFlowFixVWord σ' I out))
      ByteArray.empty := by
  let key := endFlowIlkWord I
  let mem14 := twoWordHashMem key ⟨14⟩ (endFlowVatIlksPostCallMem I out)
  let mem12 := twoWordHashMem key ⟨12⟩ mem14
  let mem13 := twoWordHashMem key ⟨13⟩ mem12
  let mem15 := twoWordHashMem key ⟨15⟩ mem13
  have h0 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3061⟩
      (endFlowWadWord σ' I out :: ⟨0⟩ :: endFlowVatIlkRateWord out ::
        key :: endFlowReturnPc :: sel :: [])
      mem12 (UInt256.ofNat 9) out (cA', σ') k C := by
    simpa [key, mem14, mem12] using h
  have hgapSlot : endFlowGapSlot I = solcMappingSlot ⟨13⟩ key := by
    simpa [key] using endFlowGapSlot_eq (I := I) hsz36
  have hfixSlot : endFlowFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endFlowFixSlot_eq (I := I) hsz36
  have hpostSize : (endFlowVatIlksPostCallMem I out).size = 288 :=
    endFlowVatIlksPostCallMem_size_long I out hlo
  have hmem14Size : mem14.size = (endFlowVatIlksPostCallMem I out).size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmem12Size : mem12.size = mem14.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨12⟩
      (by rw [hmem14Size, hpostSize]; omega)
  have hmem13Size : mem13.size = mem12.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨13⟩
      (by rw [hmem12Size, hmem14Size, hpostSize]; omega)
  have hmem15Size : mem15.size = mem13.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨15⟩
      (by rw [hmem13Size, hmem12Size, hmem14Size, hpostSize]; omega)
  have hmem14Read64 :
      mem14.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨14⟩
      (by rw [hpostSize]; omega) (endFlowVatIlksPostCallMem_read64 I out)
  have hmem12Read64 :
      mem12.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨12⟩
      (by rw [hmem14Size, hpostSize]; omega) hmem14Read64
  have hmem13Read64 :
      mem13.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨13⟩
      (by rw [hmem12Size, hmem14Size, hpostSize]; omega) hmem12Read64
  have hmem15Read64 :
      mem15.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨15⟩
      (by rw [hmem13Size, hmem12Size, hmem14Size, hpostSize]; omega) hmem13Read64
  have hgapHash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem13.readWithPadding 0 64))) =
        solcMappingSlot ⟨13⟩ key :=
    endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem12) ⟨13⟩ key
      (by rw [hmem12Size, hmem14Size, hpostSize]; omega)
  have hfixHash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem15.readWithPadding 0 64))) =
        solcMappingSlot ⟨15⟩ key :=
    endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem13) ⟨15⟩ key
      (by rw [hmem13Size, hmem12Size, hmem14Size, hpostSize]; omega)
  have hrayNonzero : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd3064 := evm_run h0 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd3077 := rd3064.pushConst endRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3079 := evm_run rd3077 with [
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd3080raw⟩ := rd3079.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3080⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3080⟩
        (endFlowDebtWord σ' I :: endRayWord :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem12 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using rd3080raw⟩
  have rd3084 := evm_run rd3080 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3086⟩ (by native_decide) (by evm_ov)]
  have rd3086pre := rd3084.jumpiT (by native_decide) hrayNonzero
    (by jump_dest) (by evm_ov)
  have rd3088raw := evm_run rd3086pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd3088⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3088⟩
        (endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem12 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowDenWord, endRayWord] using rd3088raw⟩
  have rd3094 := evm_run rd3088 with [
    raw push2 ⟨3137⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨3119⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd3101pre := evm_run rd3094 with [
    raw push1 ⟨13⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3102 := rd3101pre.mstore 0 (wordAt0Mem key mem12)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem12]) (by native_decide) (by evm_ov)
  have rd3107pre := evm_run rd3102 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3108 := rd3107pre.mstore 0 mem13 (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨13⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem12) 32 32 =
        mem13
      simp [mem13, twoWordHashMem, wordAt32Mem])
    (by native_decide) (by evm_ov)
  have rd3113 := evm_run rd3108 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have rd3114pre := rd3113.keccak256 0 (endFlowGapSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simpa [mem13, key, hgapSlot] using hgapHash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3115raw⟩ := rd3114pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3115⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3115⟩
        (endFlowGapWord σ' I :: endFlowWadWord σ' I out :: ⟨3119⟩ ::
          ⟨3137⟩ :: endFlowDenWord σ' I :: endFlowWadWord σ' I out ::
          endFlowVatIlkRateWord out :: key :: endFlowReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endFlowGapWord, endSlotWord, solcSlotWord, key, hgapSlot] using rd3115raw⟩
  have rd10154 := evm_run rd3115 with [
    raw push2 ⟨10154⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd3119raw⟩ :=
    RD.solcCheckedSubSuccess
      (pc := ⟨10154⟩) (okPc := ⟨10108⟩)
      (a := endFlowWadWord σ' I out) (b := endFlowGapWord σ' I)
      (ret := ⟨3119⟩)
      (R := [⟨3137⟩, endFlowDenWord σ' I, endFlowWadWord σ' I out,
        endFlowVatIlkRateWord out, key, endFlowReturnPc, sel])
      rd10154
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      hleSub (by jump_dest) (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3119⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
        (endFlowNum0Word σ' I out :: ⟨3137⟩ :: endFlowDenWord σ' I ::
          endFlowWadWord σ' I out :: endFlowVatIlkRateWord out :: key ::
          endFlowReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowNum0Word] using rd3119raw⟩
  have rd3120 := rd3119.jumpdest (by native_decide) (by evm_ov)
  have rd3133 := rd3120.pushConst endRayWord
    (width := 12) (op := .PUSH12) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd10170 := evm_run rd3133 with [
    raw push2 ⟨10170⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  obtain ⟨_, _, rd3137raw⟩ :=
    endFlowX_mulHelperReturns
      (x := endFlowNum0Word σ' I out) (y := endRayWord)
      (ret := ⟨3137⟩)
      (R := [endFlowDenWord σ' I, endFlowWadWord σ' I out,
        endFlowVatIlkRateWord out, key, endFlowReturnPc, sel])
      (mem := mem13) hfitMul hrayNonzero (by simpa using rd10170)
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3137⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3137⟩
        (endFlowNumWord σ' I out :: endFlowDenWord σ' I ::
          endFlowWadWord σ' I out :: endFlowVatIlkRateWord out :: key ::
          endFlowReturnPc :: sel :: [])
        mem13 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowNumWord] using rd3137raw⟩
  have rd3142 := evm_run rd3137 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨3144⟩ (by native_decide) (by evm_ov)]
  have rd3144pre := rd3142.jumpiT (by native_decide) hden (by jump_dest) (by evm_ov)
  have rd3149pre := evm_run rd3144pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3150 := rd3149pre.mstore 0 (wordAt0Mem key mem13)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simp [wordAt0Mem, key, mem13]) (by native_decide) (by evm_ov)
  have rd3154pre := evm_run rd3150 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3155 := rd3154pre.mstore 0 mem15 (UInt256.ofNat 9)
    (by native_decide) mem_cost
    (by
      change (⟨15⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem13) 32 32 =
        mem15
      simp [mem15, twoWordHashMem, wordAt32Mem])
    (by native_decide) (by evm_ov)
  have rd3159 := evm_run rd3155 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd3160pre := rd3159.keccak256 0 (endFlowFixSlot I)
    (UInt256.ofNat 9) (by native_decide) mem_cost
    (by simpa [mem15, key, hfixSlot] using hfixHash)
    (by native_decide) (by evm_ov)
  have rd3166raw := evm_run rd3160pre with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd3166⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3166⟩
        (endFlowFixSlot I :: endFlowFixVWord σ' I out :: ⟨64⟩ :: ⟨0⟩ ::
          endFlowWadWord σ' I out :: endFlowVatIlkRateWord out :: key ::
          endFlowReturnPc :: sel :: [])
        mem15 (UInt256.ofNat 9) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endFlowFixVWord] using rd3166raw⟩
  obtain ⟨_, _, rd3167raw⟩ := rd3166.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3167⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3167⟩
        (⟨64⟩ :: ⟨0⟩ :: endFlowWadWord σ' I out :: endFlowVatIlkRateWord out ::
          key :: endFlowReturnPc :: sel :: [])
        mem15 (UInt256.ofNat 9) out
        (cA', endFlowPostAccountMap σ' I (endFlowFixVWord σ' I out)) k' C' := by
    exact ⟨_, _, by simpa [endFlowPostAccountMap] using rd3167raw⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem15.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem15.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [hmem15Size, hmem13Size, hmem12Size, hmem14Size, hpostSize]; decide)
      (by decide) hmem15Read64
  have rd3168 := rd3167.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by native_decide) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd3169 := evm_run rd3168 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd3170 := rd3169.pushConst endFlowFixLogTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := rd3170.swap2 (by native_decide) (by evm_ov)
  have rdLog := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := endFlowFixLogTopic) (d := key)
    (t := [endFlowWadWord σ' I out, endFlowVatIlkRateWord out, key,
      endFlowReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 9).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rdLogPrefix (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJump := evm_run rdLog with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rdReturn := RD.jumpdest (pc := endFlowReturnPc) (stk := [sel]) rdJump
    (by native_decide) (by evm_ov)
  exact RD.stop rdReturn (by native_decide) (by evm_ov)

theorem endFlowCheckedVatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFlowStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFlowStore I).get? "vat" = none := by
      simp [endFlowStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFlowStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endPackVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm0)
      (locals := endFlowStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endFlowCheckedVatIlksFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFlowStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFlowStore I).get? "vat" = none := by
      simp [endFlowStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFlowStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endFlowStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endFlowStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endFlowStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs (by simpa [evm0] using hcall)

theorem endFlowCheckedVatIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFlowStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFlowStore I).get? "vat" = none := by
      simp [endFlowStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFlowStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endFlowStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endFlowStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
      (locals := endFlowStore I) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs
      (by simpa [evm0] using hcall) (endFlowVatIlksDecode_none_short hshort)

theorem endFlowCheckedVatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFlowStore I } evm0
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFlowStore I).get? "vat" = none := by
      simp [endFlowStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFlowStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0 (.var "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((endFlowStore I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endFlowStore, store_get_self]
    rfl
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, EvalResult.bind, bind, pure]
  have hvalue := endFlowVatIlksDecode_ok (out := out) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm0) (evm' := evmVat)
    (locals := endFlowStore I) (receiver := .storage vatRef)
    (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := out) (perm := true)
    (value :=
      [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])
    hguard hreceiver hargs (by simpa [evm0] using hcall) hvalue
  simpa [checkedExternalCallStmts, endFlowStoreVatIlk, collapseReturns] using hblock

theorem evalStorageRef_endFlow_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endFlowStore I } evm
      debtRef = .ok ({ base := "debt", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]

theorem evalExpr_endFlow_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.storage debtRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endFlowStore I })
    (slot := debtRef)
    (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := by simp [endFlowStore, debtRef])
    (her := evalStorageRef_endFlow_debt evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨11⟩)

theorem evalExpr_endFlow_debt_of_base {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hbase : locals.get? "debt" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage debtRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := debtRef)
    (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind,
        hbase])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨11⟩)

theorem evalExpr_endFlow_debt_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage debtRef) = .ok (.int 0) := by
    simpa [hdebt] using evalExpr_endFlow_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endFlow_debt_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage debtRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) :=
    evalExpr_endFlow_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  apply hdebt
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem evalExpr_endFlow_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm (.var "ilk") =
      .ok (endFlowIlkValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endFlowStore I).get? "ilk") =
    .ok (endFlowIlkValue I)
  rw [endFlowStore, store_get_self]
  rfl

theorem evalStorageRef_endFlow_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endFlowStore I } evm
      (fixRef (.var "ilk")) = .ok (endFlowFixEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endFlow_ilk evm I
  simp [endFlowFixEvaledRef, endFlowIlkKey, hilk, endFlowIlkValue, endBytes32ArgValue,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, fixRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalStorageRef_endFlow_fix_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (fixRef (.var "ilk")) = .ok (endFlowFixEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [endFlowFixEvaledRef, endFlowIlkKey, endFlowIlkValue, endBytes32ArgValue,
    endBytes32ArgKey, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, fixRef,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, evalExpr?,
    ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem evalExpr_endFlow_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endFlowFixSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endFlowStore I })
    (slot := fixRef (.var "ilk"))
    (er := endFlowFixEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endFlowFixSlot I))
    (hbase := by simp [endFlowStore, fixRef])
    (her := evalStorageRef_endFlow_fix evm I hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endFlowFixSlot I))

theorem evalExpr_endFlow_fix_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfix :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowFixSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endFlowFixSlot I)).toNat)) :=
    evalExpr_endFlow_fix evm I hsz36
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply hfix
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem evalExpr_endFlow_fix_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfix :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowFixSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage (fixRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [hfix] using evalExpr_endFlow_fix evm I hsz36
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_eq_int_true hstorage hzero rfl

theorem evalExpr_endFlow_vatIlk_rate (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endFlowStoreVatIlk I out } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
            .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endFlowStoreVatIlk I out).get? "vatIlk") =
        .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkRateWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkSpotWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkLineWord out).toNat),
          .int (Int.ofNat (endFlowVatIlkDustWord out).toNat)])
    rw [endFlowStoreVatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalStorageRef_endFlow_Art_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ArtRef (.var "ilk")) = .ok (endFlowArtEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ArtRef,
    endFlowArtEvaledRef, endFlowIlkValue, endBytes32ArgValue, endFlowIlkKey,
    endBytes32ArgKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, evalExpr?,
    pure, bind, ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem evalExpr_endFlow_Art_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv) (hbase : locals.get? "Art" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ArtRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endFlowArtSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := ArtRef (.var "ilk"))
    (er := endFlowArtEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endFlowArtSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endFlow_Art_of_get evm I hget hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endFlowArtSlot I))

theorem evalStorageRef_endFlow_tag_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (tagRef (.var "ilk")) = .ok (endFlowTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, tagRef,
    endFlowTagEvaledRef, endFlowIlkValue, endBytes32ArgValue, endFlowIlkKey,
    endBytes32ArgKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, evalExpr?,
    pure, bind, ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem evalExpr_endFlow_tag_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv) (hbase : locals.get? "tag" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endFlowTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := tagRef (.var "ilk"))
    (er := endFlowTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endFlowTagSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endFlow_tag_of_get evm I hget hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endFlowTagSlot I))

theorem evalStorageRef_endFlow_gap_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (gapRef (.var "ilk")) = .ok (endFlowGapEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, gapRef,
    endFlowGapEvaledRef, endFlowIlkValue, endBytes32ArgValue, endFlowIlkKey,
    endBytes32ArgKey, valueToKey?, EvalResult.ofOption, EvalResult.bind, evalExpr?,
    pure, bind, ← Std.HashMap.get?_eq_getElem?, hget]
  rw [if_pos hargLen]

theorem evalExpr_endFlow_gap_of_get {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv) (hbase : locals.get? "gap" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (gapRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endFlowGapSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := gapRef (.var "ilk"))
    (er := endFlowGapEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endFlowGapSlot I))
    (hbase := hbase)
    (her := evalStorageRef_endFlow_gap_of_get evm I hget hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endFlowGapSlot I))

theorem endFlowStmtRate (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    ExecStmt config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok { contract := contract, locals := endFlowStoreRate I out } evm) := by
  simpa [endFlowStoreRate] using
    ExecStmt.letDecl (evalExpr_endFlow_vatIlk_rate evm I out)

theorem endFlowStmtWad0RmulReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hfit : (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endFlowStoreRate I out } evm
      (.internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0")
      (.ok { contract := contract, locals := endFlowStoreWad0 σ I out } evm) := by
  have hArt :
      evalExpr? config { contract := contract, locals := endFlowStoreRate I out } evm
        (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowArtWord σ I).toNat)) := by
    have hbase : (endFlowStoreRate I out).get? "Art" = none := by
      simp [endFlowStoreRate, endFlowStoreVatIlk, endFlowStore]
    have hget : (endFlowStoreRate I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget hsz36
    simpa [hArtLoad] using hstorage
  have hrate :
      evalExpr? config { contract := contract, locals := endFlowStoreRate I out } evm
        (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat)) := by
    simpa [endFlowStoreRate] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreRate I out)
        (name := "rate") (value := endFlowVatIlkRateWord out)
        (by simp [endFlowStoreRate])
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreRate I out } evm
        [.storage (ArtRef (.var "ilk")), .var "rate"] =
          .ok [.int (Int.ofNat (endFlowArtWord σ I).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)] := by
    simp [evalExprs?, hArt, hrate, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFlowArtWord σ I).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)] =
        some (endUintBinaryLocals (endFlowArtWord σ I) (endFlowVatIlkRateWord out)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionReturn (evm := evm)
      (x := endFlowArtWord σ I) (y := endFlowVatIlkRateWord out)
      (prod := endFlowArtWord σ I * endFlowVatIlkRateWord out)
      (q := endFlowWad0Word σ I out) rfl hfit rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreRate I out })
    (evm := evm) (name := "rmul") (retVar := "wad0")
    (args := [.storage (ArtRef (.var "ilk")), .var "rate"])
    (argVals :=
      [.int (Int.ofNat (endFlowArtWord σ I).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFlowArtWord σ I) (endFlowVatIlkRateWord out))
    hargs (by rfl) hbind hbody
  simpa [endFlowStoreWad0, resumeAfterInternalCall, collapseReturns, endFlowWad0Word] using hstmt

theorem endFlowStmtWadRmulReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hfit : (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
      (.internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad")
      (.ok { contract := contract, locals := endFlowStoreWad σ I out } evm) := by
  have hwad0 :
      evalExpr? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        (.var "wad0") = .ok (.int (Int.ofNat (endFlowWad0Word σ I out).toNat)) := by
    simpa [endFlowStoreWad0] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreWad0 σ I out)
        (name := "wad0") (value := endFlowWad0Word σ I out)
        (by simp [endFlowStoreWad0])
  have htag :
      evalExpr? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowTagWord σ I).toNat)) := by
    have hbase : (endFlowStoreWad0 σ I out).get? "tag" = none := by
      simp [endFlowStoreWad0, endFlowStoreRate, endFlowStoreVatIlk, endFlowStore]
    have hget : (endFlowStoreWad0 σ I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreWad0, store_get_ne _ _ (by native_decide),
        endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_tag_of_get evm I hbase hget hsz36
    simpa [hTagLoad] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        [.var "wad0", .storage (tagRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
            .int (Int.ofNat (endFlowTagWord σ I).toNat)] := by
    simp [evalExprs?, hwad0, htag, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
            .int (Int.ofNat (endFlowTagWord σ I).toNat)] =
        some (endUintBinaryLocals (endFlowWad0Word σ I out) (endFlowTagWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionReturn (evm := evm)
      (x := endFlowWad0Word σ I out) (y := endFlowTagWord σ I)
      (prod := endFlowWad0Word σ I out * endFlowTagWord σ I)
      (q := endFlowWadWord σ I out) rfl hfit rfl
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreWad0 σ I out })
    (evm := evm) (name := "rmul") (retVar := "wad")
    (args := [.var "wad0", .storage (tagRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
        .int (Int.ofNat (endFlowTagWord σ I).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFlowWad0Word σ I out) (endFlowTagWord σ I))
    hargs (by rfl) hbind hbody
  simpa [endFlowStoreWad, resumeAfterInternalCall, collapseReturns, endFlowWadWord] using hstmt

theorem endFlowStmtNum0SubReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hle : (endFlowGapWord σ I).toNat ≤ (endFlowWadWord σ I out).toNat) :
    ExecStmt config { contract := contract, locals := endFlowStoreWad σ I out } evm
      (.internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0")
      (.ok { contract := contract, locals := endFlowStoreNum0 σ I out } evm) := by
  have hwad :
      evalExpr? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        (.var "wad") = .ok (.int (Int.ofNat (endFlowWadWord σ I out).toNat)) := by
    simpa [endFlowStoreWad] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreWad σ I out)
        (name := "wad") (value := endFlowWadWord σ I out)
        (by simp [endFlowStoreWad])
  have hgap :
      evalExpr? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        (.storage (gapRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowGapWord σ I).toNat)) := by
    have hbase : (endFlowStoreWad σ I out).get? "gap" = none := by
      simp [endFlowStoreWad, endFlowStoreWad0, endFlowStoreRate, endFlowStoreVatIlk,
        endFlowStore]
    have hget : (endFlowStoreWad σ I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreWad, store_get_ne _ _ (by native_decide),
        endFlowStoreWad0, store_get_ne _ _ (by native_decide),
        endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_gap_of_get evm I hbase hget hsz36
    simpa [hGapLoad] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        [.var "wad", .storage (gapRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
            .int (Int.ofNat (endFlowGapWord σ I).toNat)] := by
    simp [evalExprs?, hwad, hgap, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
            .int (Int.ofNat (endFlowGapWord σ I).toNat)] =
        some (endUintBinaryLocals (endFlowWadWord σ I out) (endFlowGapWord σ I)) := by
    simp [subFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecSubFunctionReturn (evm := evm)
      (x := endFlowWadWord σ I out) (y := endFlowGapWord σ I)
      (diff := endFlowNum0Word σ I out) rfl hle
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreWad σ I out })
    (evm := evm) (name := "sub") (retVar := "num0")
    (args := [.var "wad", .storage (gapRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
        .int (Int.ofNat (endFlowGapWord σ I).toNat)])
    (callee := subFunction)
    (locals := endUintBinaryLocals (endFlowWadWord σ I out) (endFlowGapWord σ I))
    hargs (by rfl) hbind hbody
  simpa [endFlowStoreNum0, resumeAfterInternalCall, collapseReturns, endFlowNum0Word] using hstmt

theorem endFlowStmtNumMulReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hfit : (endFlowNum0Word σ I out).toNat * endRayWord.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
      (.internalCall "mul" [.var "num0", .intLit RAY] "num")
      (.ok { contract := contract, locals := endFlowStoreNum σ I out } evm) := by
  have hnum0 :
      evalExpr? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        (.var "num0") = .ok (.int (Int.ofNat (endFlowNum0Word σ I out).toNat)) := by
    simpa [endFlowStoreNum0] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreNum0 σ I out)
        (name := "num0") (value := endFlowNum0Word σ I out)
        (by simp [endFlowStoreNum0])
  have hRay :
      evalExpr? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        (.intLit RAY) = .ok (.int (Int.ofNat endRayWord.toNat)) := by
    have hRayEq : RAY = Int.ofNat endRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRayEq]
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        [.var "num0", .intLit RAY] =
          .ok [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
            .int (Int.ofNat endRayWord.toNat)] := by
    simp [evalExprs?, hnum0, hRay, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
            .int (Int.ofNat endRayWord.toNat)] =
        some (endUintBinaryLocals (endFlowNum0Word σ I out) endRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecMulFunctionReturn (evm := evm)
      (x := endFlowNum0Word σ I out) (y := endRayWord)
      (prod := endFlowNumWord σ I out) rfl hfit
  have hstmt := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreNum0 σ I out })
    (evm := evm) (name := "mul") (retVar := "num")
    (args := [.var "num0", .intLit RAY])
    (argVals :=
      [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
        .int (Int.ofNat endRayWord.toNat)])
    (callee := mulFunction)
    (locals := endUintBinaryLocals (endFlowNum0Word σ I out) endRayWord)
    hargs (by rfl) hbind hbody
  simpa [endFlowStoreNum, resumeAfterInternalCall, collapseReturns, endFlowNumWord] using hstmt

theorem endFlowStmtDenLet (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hDebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ =
        endFlowDebtWord σ I) :
    ExecStmt config { contract := contract, locals := endFlowStoreNum σ I out } evm
      (.letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)))
      (.ok { contract := contract, locals := endFlowStoreDen σ I out } evm) := by
  have hbase : (endFlowStoreNum σ I out).get? "debt" = none := by
    simp [endFlowStoreNum, endFlowStoreNum0, endFlowStoreWad, endFlowStoreWad0,
      endFlowStoreRate, endFlowStoreVatIlk, endFlowStore]
  have hdebt :
      evalExpr? config { contract := contract, locals := endFlowStoreNum σ I out } evm
        (.storage debtRef) = .ok (.int (Int.ofNat (endFlowDebtWord σ I).toNat)) := by
    have hstorage := evalExpr_endFlow_debt_of_base evm I hbase
    simpa [hDebtLoad] using hstorage
  have hRay :
      evalExpr? config { contract := contract, locals := endFlowStoreNum σ I out } evm
        (.intLit RAY) = .ok (.int (Int.ofNat endRayWord.toNat)) := by
    have hRayEq : RAY = Int.ofNat endRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRayEq]
  have hdiv :
      evalExpr? config { contract := contract, locals := endFlowStoreNum σ I out } evm
        (.binary .div (.storage debtRef) (.intLit RAY)) =
          .ok (.int (Int.ofNat (endFlowDenWord σ I).toNat)) :=
    endEvalExpr_div_uint256_ok hdebt hRay (by native_decide) rfl
  simpa [endFlowStoreDen] using ExecStmt.letDecl hdiv

theorem endFlowStmtFixVLet (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hden : endFlowDenWord σ I ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endFlowStoreDen σ I out } evm
      (.letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")))
      (.ok { contract := contract, locals := endFlowStoreFixV σ I out } evm) := by
  have hnum :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.var "num") = .ok (.int (Int.ofNat (endFlowNumWord σ I out).toNat)) := by
    simpa [endFlowStoreDen, endFlowStoreNum] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreDen σ I out)
        (name := "num") (value := endFlowNumWord σ I out)
        (by
          rw [endFlowStoreDen, store_get_ne _ _ (by native_decide),
            endFlowStoreNum, store_get_self])
  have hdenExpr :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.var "den") = .ok (.int (Int.ofNat (endFlowDenWord σ I).toNat)) := by
    simpa [endFlowStoreDen] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreDen σ I out)
        (name := "den") (value := endFlowDenWord σ I)
        (by simp [endFlowStoreDen])
  have hdiv :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.binary .div (.var "num") (.var "den")) =
          .ok (.int (Int.ofNat (endFlowFixVWord σ I out).toNat)) :=
    endEvalExpr_div_uint256_ok hnum hdenExpr hden rfl
  simpa [endFlowStoreFixV] using ExecStmt.letDecl hdiv

theorem endFlowStmtAssignFixV (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) :
    ExecStmt config { contract := contract, locals := endFlowStoreFixV σ I out } evm
      (.assign .storage (fixRef (.var "ilk")) (.var "fixV"))
      (.ok { contract := contract, locals := endFlowStoreFixV σ I out }
        (endFlowPostState evm I (endFlowFixVWord σ I out))) := by
  have hfixV :
      evalExpr? config { contract := contract, locals := endFlowStoreFixV σ I out } evm
        (.var "fixV") = .ok (.int (Int.ofNat (endFlowFixVWord σ I out).toNat)) := by
    simpa [endFlowStoreFixV] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreFixV σ I out)
        (name := "fixV") (value := endFlowFixVWord σ I out)
        (by simp [endFlowStoreFixV])
  have hassign :
      assignStorageRef? config { contract := contract, locals := endFlowStoreFixV σ I out }
        evm .storage (fixRef (.var "ilk"))
          (.int (Int.ofNat (endFlowFixVWord σ I out).toNat)) =
        .ok ({ contract := contract, locals := endFlowStoreFixV σ I out },
          endFlowPostState evm I (endFlowFixVWord σ I out)) := by
    apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endFlowFixSlot I))
      (hbase := by
        simp [fixRef, endFlowStoreFixV, endFlowStoreDen, endFlowStoreNum, endFlowStoreNum0,
          endFlowStoreWad, endFlowStoreWad0, endFlowStoreRate, endFlowStoreVatIlk,
          endFlowStore])
      (her := by
        have hget :
            (endFlowStoreFixV σ I out).get? "ilk" = some (endFlowIlkValue I) := by
          rw [endFlowStoreFixV, store_get_ne _ _ (by native_decide),
            endFlowStoreDen, store_get_ne _ _ (by native_decide),
            endFlowStoreNum, store_get_ne _ _ (by native_decide),
            endFlowStoreNum0, store_get_ne _ _ (by native_decide),
            endFlowStoreWad, store_get_ne _ _ (by native_decide),
            endFlowStoreWad0, store_get_ne _ _ (by native_decide),
            endFlowStoreRate, store_get_ne _ _ (by native_decide),
            endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
            endFlowStore, store_get_self]
        exact evalStorageRef_endFlow_fix_of_get evm I hget hsz36)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
    simpa [endFlowPostState] using
      endStorageLocStore_uint256 evm (endFlowFixSlot I) (endFlowFixVWord σ I out)
  exact ExecStmt.assign hfixV hassign

theorem endFlowTailReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hDebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ =
        endFlowDebtWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hfitWad :
      (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord σ I).toNat ≤ (endFlowWadWord σ I out).toNat)
    (hfitMul : (endFlowNum0Word σ I out).toNat * endRayWord.toNat < UInt256.size)
    (hden : endFlowDenWord σ I ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      (.ok { contract := contract, locals := endFlowStoreFixV σ I out }
        (endFlowPostState evm I (endFlowFixVWord σ I out))) := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWad0RmulReturns evm I σ out hsz36 hArtLoad hfitWad0) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWadRmulReturns evm I σ out hsz36 hTagLoad hfitWad) ?_
  refine ExecBlock.consNormal
    (endFlowStmtNum0SubReturns evm I σ out hsz36 hGapLoad hleSub) ?_
  refine ExecBlock.consNormal (endFlowStmtNumMulReturns evm I σ out hfitMul) ?_
  refine ExecBlock.consNormal (endFlowStmtDenLet evm I σ out hDebtLoad) ?_
  refine ExecBlock.consNormal (endFlowStmtFixVLet evm I σ out hden) ?_
  exact ExecBlock.consNormal (endFlowStmtAssignFixV evm I σ out hsz36) ExecBlock.nil

theorem endEvalExpr_div_uint256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int 0)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .revert := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]

theorem endFlowStmtWad0RmulReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hover :
      UInt256.size ≤ (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat) :
    ExecStmt config { contract := contract, locals := endFlowStoreRate I out } evm
      (.internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0")
      .reverted := by
  have hArt :
      evalExpr? config { contract := contract, locals := endFlowStoreRate I out } evm
        (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowArtWord σ I).toNat)) := by
    have hbase : (endFlowStoreRate I out).get? "Art" = none := by
      simp [endFlowStoreRate, endFlowStoreVatIlk, endFlowStore]
    have hget : (endFlowStoreRate I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget hsz36
    simpa [hArtLoad] using hstorage
  have hrate :
      evalExpr? config { contract := contract, locals := endFlowStoreRate I out } evm
        (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord out).toNat)) := by
    simpa [endFlowStoreRate] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreRate I out)
        (name := "rate") (value := endFlowVatIlkRateWord out)
        (by simp [endFlowStoreRate])
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreRate I out } evm
        [.storage (ArtRef (.var "ilk")), .var "rate"] =
          .ok [.int (Int.ofNat (endFlowArtWord σ I).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)] := by
    simp [evalExprs?, hArt, hrate, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFlowArtWord σ I).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)] =
        some (endUintBinaryLocals (endFlowArtWord σ I) (endFlowVatIlkRateWord out)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionRevertMul (evm := evm)
      (x := endFlowArtWord σ I) (y := endFlowVatIlkRateWord out) hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreRate I out })
    (evm := evm) (name := "rmul") (retVar := "wad0")
    (args := [.storage (ArtRef (.var "ilk")), .var "rate"])
    (argVals :=
      [.int (Int.ofNat (endFlowArtWord σ I).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord out).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFlowArtWord σ I) (endFlowVatIlkRateWord out))
    hargs (by rfl) hbind hbody

theorem endFlowStmtWadRmulReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hover :
      UInt256.size ≤ (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat) :
    ExecStmt config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
      (.internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad")
      .reverted := by
  have hwad0 :
      evalExpr? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        (.var "wad0") = .ok (.int (Int.ofNat (endFlowWad0Word σ I out).toNat)) := by
    simpa [endFlowStoreWad0] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreWad0 σ I out)
        (name := "wad0") (value := endFlowWad0Word σ I out)
        (by simp [endFlowStoreWad0])
  have htag :
      evalExpr? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowTagWord σ I).toNat)) := by
    have hbase : (endFlowStoreWad0 σ I out).get? "tag" = none := by
      simp [endFlowStoreWad0, endFlowStoreRate, endFlowStoreVatIlk, endFlowStore]
    have hget : (endFlowStoreWad0 σ I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreWad0, store_get_ne _ _ (by native_decide),
        endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_tag_of_get evm I hbase hget hsz36
    simpa [hTagLoad] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreWad0 σ I out } evm
        [.var "wad0", .storage (tagRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
            .int (Int.ofNat (endFlowTagWord σ I).toNat)] := by
    simp [evalExprs?, hwad0, htag, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
            .int (Int.ofNat (endFlowTagWord σ I).toNat)] =
        some (endUintBinaryLocals (endFlowWad0Word σ I out) (endFlowTagWord σ I)) := by
    simp [rmulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecRmulFunctionRevertMul (evm := evm)
      (x := endFlowWad0Word σ I out) (y := endFlowTagWord σ I) hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreWad0 σ I out })
    (evm := evm) (name := "rmul") (retVar := "wad")
    (args := [.var "wad0", .storage (tagRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endFlowWad0Word σ I out).toNat),
        .int (Int.ofNat (endFlowTagWord σ I).toNat)])
    (callee := rmulFunction)
    (locals := endUintBinaryLocals (endFlowWad0Word σ I out) (endFlowTagWord σ I))
    hargs (by rfl) hbind hbody

theorem endFlowStmtNum0SubReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hlt : (endFlowWadWord σ I out).toNat < (endFlowGapWord σ I).toNat) :
    ExecStmt config { contract := contract, locals := endFlowStoreWad σ I out } evm
      (.internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0")
      .reverted := by
  have hwad :
      evalExpr? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        (.var "wad") = .ok (.int (Int.ofNat (endFlowWadWord σ I out).toNat)) := by
    simpa [endFlowStoreWad] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreWad σ I out)
        (name := "wad") (value := endFlowWadWord σ I out)
        (by simp [endFlowStoreWad])
  have hgap :
      evalExpr? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        (.storage (gapRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endFlowGapWord σ I).toNat)) := by
    have hbase : (endFlowStoreWad σ I out).get? "gap" = none := by
      simp [endFlowStoreWad, endFlowStoreWad0, endFlowStoreRate, endFlowStoreVatIlk,
        endFlowStore]
    have hget : (endFlowStoreWad σ I out).get? "ilk" = some (endFlowIlkValue I) := by
      rw [endFlowStoreWad, store_get_ne _ _ (by native_decide),
        endFlowStoreWad0, store_get_ne _ _ (by native_decide),
        endFlowStoreRate, store_get_ne _ _ (by native_decide),
        endFlowStoreVatIlk, store_get_ne _ _ (by native_decide),
        endFlowStore, store_get_self]
    have hstorage := evalExpr_endFlow_gap_of_get evm I hbase hget hsz36
    simpa [hGapLoad] using hstorage
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreWad σ I out } evm
        [.var "wad", .storage (gapRef (.var "ilk"))] =
          .ok [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
            .int (Int.ofNat (endFlowGapWord σ I).toNat)] := by
    simp [evalExprs?, hwad, hgap, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
            .int (Int.ofNat (endFlowGapWord σ I).toNat)] =
        some (endUintBinaryLocals (endFlowWadWord σ I out) (endFlowGapWord σ I)) := by
    simp [subFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecSubFunctionRevert (evm := evm)
      (x := endFlowWadWord σ I out) (y := endFlowGapWord σ I) hlt
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreWad σ I out })
    (evm := evm) (name := "sub") (retVar := "num0")
    (args := [.var "wad", .storage (gapRef (.var "ilk"))])
    (argVals :=
      [.int (Int.ofNat (endFlowWadWord σ I out).toNat),
        .int (Int.ofNat (endFlowGapWord σ I).toNat)])
    (callee := subFunction)
    (locals := endUintBinaryLocals (endFlowWadWord σ I out) (endFlowGapWord σ I))
    hargs (by rfl) hbind hbody

theorem endFlowStmtNumMulReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hover : UInt256.size ≤ (endFlowNum0Word σ I out).toNat * endRayWord.toNat) :
    ExecStmt config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
      (.internalCall "mul" [.var "num0", .intLit RAY] "num")
      .reverted := by
  have hnum0 :
      evalExpr? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        (.var "num0") = .ok (.int (Int.ofNat (endFlowNum0Word σ I out).toNat)) := by
    simpa [endFlowStoreNum0] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreNum0 σ I out)
        (name := "num0") (value := endFlowNum0Word σ I out)
        (by simp [endFlowStoreNum0])
  have hRay :
      evalExpr? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        (.intLit RAY) = .ok (.int (Int.ofNat endRayWord.toNat)) := by
    have hRayEq : RAY = Int.ofNat endRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRayEq]
  have hargs :
      evalExprs? config { contract := contract, locals := endFlowStoreNum0 σ I out } evm
        [.var "num0", .intLit RAY] =
          .ok [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
            .int (Int.ofNat endRayWord.toNat)] := by
    simp [evalExprs?, hnum0, hRay, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
            .int (Int.ofNat endRayWord.toNat)] =
        some (endUintBinaryLocals (endFlowNum0Word σ I out) endRayWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecMulFunctionRevert (evm := evm)
      (x := endFlowNum0Word σ I out) (y := endRayWord) hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endFlowStoreNum0 σ I out })
    (evm := evm) (name := "mul") (retVar := "num")
    (args := [.var "num0", .intLit RAY])
    (argVals :=
      [.int (Int.ofNat (endFlowNum0Word σ I out).toNat),
        .int (Int.ofNat endRayWord.toNat)])
    (callee := mulFunction)
    (locals := endUintBinaryLocals (endFlowNum0Word σ I out) endRayWord)
    hargs (by rfl) hbind hbody

theorem endFlowStmtFixVLetReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hden : endFlowDenWord σ I = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endFlowStoreDen σ I out } evm
      (.letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")))
      .reverted := by
  have hnum :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.var "num") = .ok (.int (Int.ofNat (endFlowNumWord σ I out).toNat)) := by
    simpa [endFlowStoreDen, endFlowStoreNum] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreDen σ I out)
        (name := "num") (value := endFlowNumWord σ I out)
        (by
          rw [endFlowStoreDen, store_get_ne _ _ (by native_decide),
            endFlowStoreNum, store_get_self])
  have hdenExpr :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.var "den") = .ok (.int 0) := by
    simpa [endFlowStoreDen, hden] using
      endEvalExpr_varUInt256 (evm := evm) (locals := endFlowStoreDen σ I out)
        (name := "den") (value := endFlowDenWord σ I)
        (by simp [endFlowStoreDen])
  have hdiv :
      evalExpr? config { contract := contract, locals := endFlowStoreDen σ I out } evm
        (.binary .div (.var "num") (.var "den")) = .revert :=
    endEvalExpr_div_uint256_revert hnum hdenExpr
  exact ExecStmt.letDeclRevert hdiv

theorem endFlowTailReverts_wad0RmulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hover :
      UInt256.size ≤ (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  exact ExecBlock.consRevert
    (endFlowStmtWad0RmulReverts evm I σ out hsz36 hArtLoad hover)

theorem endFlowTailReverts_wadRmulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hover :
      UInt256.size ≤ (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWad0RmulReturns evm I σ out hsz36 hArtLoad hfitWad0) ?_
  exact ExecBlock.consRevert
    (endFlowStmtWadRmulReverts evm I σ out hsz36 hTagLoad hover)

theorem endFlowTailReverts_subUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hfitWad :
      (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size)
    (hlt : (endFlowWadWord σ I out).toNat < (endFlowGapWord σ I).toNat) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWad0RmulReturns evm I σ out hsz36 hArtLoad hfitWad0) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWadRmulReturns evm I σ out hsz36 hTagLoad hfitWad) ?_
  exact ExecBlock.consRevert
    (endFlowStmtNum0SubReverts evm I σ out hsz36 hGapLoad hlt)

theorem endFlowTailReverts_mulOverflow (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hfitWad :
      (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord σ I).toNat ≤ (endFlowWadWord σ I out).toNat)
    (hover : UInt256.size ≤ (endFlowNum0Word σ I out).toNat * endRayWord.toNat) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWad0RmulReturns evm I σ out hsz36 hArtLoad hfitWad0) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWadRmulReturns evm I σ out hsz36 hTagLoad hfitWad) ?_
  refine ExecBlock.consNormal
    (endFlowStmtNum0SubReturns evm I σ out hsz36 hGapLoad hleSub) ?_
  exact ExecBlock.consRevert
    (endFlowStmtNumMulReverts evm I σ out hover)

theorem endFlowTailReverts_denZero (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hDebtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ =
        endFlowDebtWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hfitWad :
      (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord σ I).toNat ≤ (endFlowWadWord σ I out).toNat)
    (hfitMul : (endFlowNum0Word σ I out).toNat * endRayWord.toNat < UInt256.size)
    (hden : endFlowDenWord σ I = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  refine ExecBlock.consNormal (endFlowStmtRate evm I out) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWad0RmulReturns evm I σ out hsz36 hArtLoad hfitWad0) ?_
  refine ExecBlock.consNormal
    (endFlowStmtWadRmulReturns evm I σ out hsz36 hTagLoad hfitWad) ?_
  refine ExecBlock.consNormal
    (endFlowStmtNum0SubReturns evm I σ out hsz36 hGapLoad hleSub) ?_
  refine ExecBlock.consNormal (endFlowStmtNumMulReturns evm I σ out hfitMul) ?_
  refine ExecBlock.consNormal (endFlowStmtDenLet evm I σ out hDebtLoad) ?_
  exact ExecBlock.consRevert (endFlowStmtFixVLetReverts evm I σ out hden)

theorem endFlowBodyReverts_debtZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endFlowDebtWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endFlow_debt_ne_false evm0 I hdebtLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endFlowStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage debtRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endFlowBodyReverts_fixNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hbad
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endFlowFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowFixWord, endSlotWord, solcSlotWord] using hbad
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_debt_ne_true evm0 I hdebtLoad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endFlow_fix_eq_false evm0 I hsz36 hfixLoad
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardFix)
  simpa [ExecTransitionBody, flowTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endFlowBodyReverts_vatIlksBlock {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hvatBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hbad
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endFlowFixSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowFixWord, endSlotWord, solcSlotWord] using hfix
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_debt_ne_true evm0 I hdebtLoad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_fix_eq_true evm0 I hsz36 hfixLoad
  have hvat :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted := by
    simpa [evm0] using hvatBlock
  have hvatWithTail :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
            .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
            .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
            .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
            .internalCall "mul" [.var "num0", .intLit RAY] "num",
            .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
            .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
            .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term
      (s2 :=
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      hvat (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body .reverted := by
    simp only [flowTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
    simpa using hvatWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFlowBodyReverts_vatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  exact endFlowBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz36 hdebt hfix
    (by
      simpa using
        (endFlowCheckedVatIlksNoCode
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcodeSize))

theorem endFlowBodyReverts_vatIlksCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  exact endFlowBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz36 hdebt hfix
    (by
      simpa using
        (endFlowCheckedVatIlksFailure
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
          hcodeSize hcall))

theorem endFlowBodyReverts_vatIlksDecodeShort {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hshort : out.size < 160) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  exact endFlowBodyReverts_vatIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz36 hdebt hfix
    (by
      simpa using
        (endFlowCheckedVatIlksDecodeRevert
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
          hcodeSize hcall hshort))

theorem endFlowPrefixVatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFlowStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
          .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
      (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hbad
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endFlowFixSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowFixWord, endSlotWord, solcSlotWord] using hfix
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_debt_ne_true evm0 I hdebtLoad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_fix_eq_true evm0 I hsz36 hfixLoad
  have hvat :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
        (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
    simpa [evm0] using
      endFlowCheckedVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hcodeSize hcall hlo
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardFix) ?_
  exact hvat

theorem endFlowBodyReverts_vatIlksOkTailReverted {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size)
    (htail :
      ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evmVat
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk")
        (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
    simpa [evm0] using
      endFlowPrefixVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hwv hsz36 hdebt hfix hcodeSize hcall hlo
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body .reverted := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      hprefix htail
    simpa [flowTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFlowBodyReturns_vatIlksOkTail {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat evmPost : EVM.State} {out : ByteArray} {fPost : Frame}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size)
    (htail :
      ExecBlock config { contract := contract, locals := endFlowStoreVatIlk I out } evmVat
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
        (.ok fPost evmPost)) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body
      (.returned fPost evmPost none) := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk")
        (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
    simpa [evm0] using
      endFlowPrefixVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hwv hsz36 hdebt hfix hcodeSize hcall hlo
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body (.ok fPost evmPost) := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      hprefix htail
    simpa [flowTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockOK hblock

theorem endFlowBodyReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, out) true)
    (hlo : 160 ≤ out.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner (endFlowArtSlot I) =
        endFlowArtWord σ I)
    (hTagLoad :
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner (endFlowTagSlot I) =
        endFlowTagWord σ I)
    (hGapLoad :
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner (endFlowGapSlot I) =
        endFlowGapWord σ I)
    (hDebtLoad :
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩ =
        endFlowDebtWord σ I)
    (hfitWad0 :
      (endFlowArtWord σ I).toNat * (endFlowVatIlkRateWord out).toNat < UInt256.size)
    (hfitWad :
      (endFlowWad0Word σ I out).toNat * (endFlowTagWord σ I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord σ I).toNat ≤ (endFlowWadWord σ I out).toNat)
    (hfitMul : (endFlowNum0Word σ I out).toNat * endRayWord.toNat < UInt256.size)
    (hden : endFlowDenWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body
      (.returned { contract := contract, locals := endFlowStoreFixV σ I out }
        (endFlowPostState evmVat I (endFlowFixVWord σ I out)) none) := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
            .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk")
        (.ok { contract := contract, locals := endFlowStoreVatIlk I out } evmVat) := by
    simpa [evm0] using
      endFlowPrefixVatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmVat := evmVat) (out := out)
        hwv hsz36 hdebt hfix hcodeSize hcall hlo
  have htail :=
    endFlowTailReturns evmVat I σ out hsz36 hArtLoad hTagLoad hGapLoad hDebtLoad
      hfitWad0 hfitWad hleSub hfitMul hden
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body
        (.ok { contract := contract, locals := endFlowStoreFixV σ I out }
          (endFlowPostState evmVat I (endFlowFixVWord σ I out))) := by
    have happ := Reasoning.Refinement.execBlock_append
      (s2 :=
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      hprefix htail
    simpa [flowTransition, List.append_assoc] using happ
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockOK hblock

theorem endFlowX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endFlowEntryPc) (ret := endFlowReturnPc)
    (decoded := endFlowDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endFlowBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some flowTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endFlowX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_flow_none_short hsz4 hshort)

theorem endFlowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf flowTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFlowConcreteSelector := by
    simpa [endFlowSelectorBytes, endFlowConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFlowConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some flowTransition :=
    endDispatchFlow hsel
  have hreach := endReachFlowBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_flow_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endFlowX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hdebtCouple : endFlowDebtWord σ_evm I = endFlowDebtWord σ_solm I := by
      simpa [endFlowDebtWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebt : endFlowDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : endFlowDebtWord σ_solm I = ⟨0⟩ := by
        rw [← hdebtCouple]
        exact hdebt
      have hbody :
          ExecTransitionBody config contract evmSolm (endFlowStore I)
            flowTransition.body .reverted := by
        simpa [evmSolm] using
          endFlowBodyReverts_debtZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hdebtSolm
      exact (endFlowX_debtZero (g := Sat256.ofUInt256 g) hdebt hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdebtSolm : endFlowDebtWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebt (by rw [hdebtCouple, hbad])
      have hfixCouple : endFlowFixWord σ_evm I = endFlowFixWord σ_solm I := by
        simpa [endFlowFixWord, endSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (endFlowFixSlot I) ⟨0⟩
      by_cases hfix : endFlowFixWord σ_evm I = ⟨0⟩
      · have hfixSolm : endFlowFixWord σ_solm I = ⟨0⟩ := by
          rw [← hfixCouple]
          exact hfix
        by_cases hvatCode :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (endPackVatWord σ_evm I) =
              ⟨0⟩
        · have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) = ⟨0⟩ :=
            endPackVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract evmSolm (endFlowStore I)
                flowTransition.body .reverted := by
            simpa [evmSolm] using
              endFlowBodyReverts_vatIlksNoCode
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hwv hsz36 hdebtSolm hfixSolm hvatCodeSolm
          exact
            (endFlowX_vatIlksNoCode
              (g := Sat256.ofUInt256 g) hsz36 hdebt hfix hbodyReach hvatCode)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hvatCodeNE :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                (endPackVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
          have hvatCodeSolmNE :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (endPackVatWord σ_solm I) ≠ ⟨0⟩ :=
            endPackVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
          obtain ⟨gasWord, _, _, hcallReady⟩ :=
            endFlowX_vatIlksCallReady
              (g := Sat256.ofUInt256 g) hsz36 hdebt hfix hbodyReach hvatCodeNE
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd2964, hout⟩ :=
              endFlowX_vatIlksPostCall hcallReady hdepthLt
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
                  (EVM.address (endPackVatAddr σ_evm I)) "vatIlks" 0
                  [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                  (z,
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'
                      substate := A'
                      createdAccounts := cA' },
                    out) true := by
              exact callCoincides
                (cfg := config)
                (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (name := "vatIlks")
                (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                (tgt := EVM.address (endPackVatAddr σ_evm I))
                (targetWord := endPackVatWord σ_evm I)
                (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
                (z := z) (o := out) (g'' := g'') (callGas := callGas)
                (mem := endFlowVatIlksCalldataMem I (endFlowFixHashMem I))
                (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                (callPerm := true)
                hdepthNe htgt
                (endFlowVatIlksEncode_eq I hsz36
                  (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size))
                (by simpa [initState, hperm] using hΘeq)
            obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hStateCall⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm)
                (by simp [initState]) hAccounts
            have hVatAddr : endPackVatAddr σ_evm I = endPackVatAddr σ_solm I := by
              simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccounts]
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endPackVatAddr σ_solm I)) "vatIlks" 0
                  [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                  (z,
                    { evmSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' },
                    out) true := by
              simpa [evmSolm, hVatAddr] using hcallSolmRaw
            cases z
            · have hbody :
                  ExecTransitionBody config contract evmSolm (endFlowStore I)
                    flowTransition.body .reverted := by
                simpa [evmSolm] using
                  endFlowBodyReverts_vatIlksCallFailed
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmVat :=
                      { evmSolm with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' })
                    (out := out)
                    hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                    (by simpa [evmSolm] using hcallSolm)
              exact (endFlowX_vatIlksCallFailed (g := Sat256.ofUInt256 g) rd2964 hout)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · let evmVatEvm :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ'
                  substate := A'
                  createdAccounts := cA' }
              let evmVatSolm :=
                { evmSolm with
                  accountMap := σ'_solm
                  substate := A'_solm
                  createdAccounts := cA' }
              obtain ⟨_, _, rd2982⟩ :=
                endFlowX_vatIlksCallSucceeded (g := Sat256.ofUInt256 g) rd2964
              by_cases hshortOut : out.size < 160
              · have hbody :
                    ExecTransitionBody config contract evmSolm (endFlowStore I)
                      flowTransition.body .reverted := by
                  simpa [evmVatSolm, evmSolm] using
                    endFlowBodyReverts_vatIlksDecodeShort
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g)
                      (evmVat := evmVatSolm) (out := out)
                      hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                      (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                      hshortOut
                exact (endFlowX_vatIlksReturnDecodeShort rd2982 hshortOut hout)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hlo : 160 ≤ out.size := Nat.le_of_not_gt hshortOut
                obtain ⟨_, _, rd3010⟩ :=
                  endFlowX_vatIlksReturnDecodeOk rd2982 hlo hout
                have hArtLoad :
                    Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                        (endFlowArtSlot I) =
                      endFlowArtWord σ' I := by
                  have hload := hStateCall.storageLoad_codeOwner (endFlowArtSlot I)
                  simpa [evmVatEvm, evmVatSolm, initState, Solm.EVM.storageLoad,
                    State.lookupAccount, endFlowArtWord, endSlotWord, solcSlotWord]
                    using hload.symm
                have hTagLoad :
                    Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                        (endFlowTagSlot I) =
                      endFlowTagWord σ' I := by
                  have hload := hStateCall.storageLoad_codeOwner (endFlowTagSlot I)
                  simpa [evmVatEvm, evmVatSolm, initState, Solm.EVM.storageLoad,
                    State.lookupAccount, endFlowTagWord, endSlotWord, solcSlotWord]
                    using hload.symm
                have hGapLoad :
                    Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                        (endFlowGapSlot I) =
                      endFlowGapWord σ' I := by
                  have hload := hStateCall.storageLoad_codeOwner (endFlowGapSlot I)
                  simpa [evmVatEvm, evmVatSolm, initState, Solm.EVM.storageLoad,
                    State.lookupAccount, endFlowGapWord, endSlotWord, solcSlotWord]
                    using hload.symm
                have hDebtLoad :
                    Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner ⟨11⟩ =
                      endFlowDebtWord σ' I := by
                  have hload := hStateCall.storageLoad_codeOwner ⟨11⟩
                  simpa [evmVatEvm, evmVatSolm, initState, Solm.EVM.storageLoad,
                    State.lookupAccount, endFlowDebtWord, endSlotWord, solcSlotWord]
                    using hload.symm
                obtain ⟨_, _, rdWad0Entry⟩ :=
                  endFlowX_wad0RmulEntry (g := Sat256.ofUInt256 g) hsz36 hlo rd3010
                by_cases hoverWad0 :
                    UInt256.size ≤
                      (endFlowArtWord σ' I).toNat * (endFlowVatIlkRateWord out).toNat
                · have htail :=
                    endFlowTailReverts_wad0RmulOverflow evmVatSolm I σ' out hsz36
                      hArtLoad hoverWad0
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endFlowStore I)
                        flowTransition.body .reverted := by
                    simpa [evmVatSolm, evmSolm] using
                      endFlowBodyReverts_vatIlksOkTailReverted
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g)
                        (evmVat := evmVatSolm) (out := out)
                        hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                        hlo htail
                  exact
                    (endFlowX_rmulOverflow
                      (x := endFlowArtWord σ' I) (y := endFlowVatIlkRateWord out)
                      (ret := ⟨3041⟩)
                      (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlkRateWord out, endFlowIlkWord I,
                        endFlowReturnPc, endSelWord I])
                      hoverWad0 rdWad0Entry
                      (by simp only [List.length_cons, List.length_nil]; omega))
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hfitWad0 :
                    (endFlowArtWord σ' I).toNat * (endFlowVatIlkRateWord out).toNat <
                      UInt256.size :=
                    Nat.lt_of_not_ge hoverWad0
                  obtain ⟨_, _, rd3041⟩ : ∃ k' C',
                      RD endBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3041⟩
                        (endFlowWad0Word σ' I out :: ⟨3061⟩ :: ⟨0⟩ ::
                          endFlowVatIlkRateWord out :: endFlowIlkWord I ::
                          endFlowReturnPc :: endSelWord I :: [])
                        (twoWordHashMem (endFlowIlkWord I) ⟨14⟩
                          (endFlowVatIlksPostCallMem I out))
                        (UInt256.ofNat 9) out (cA', σ') k' C' := by
                    by_cases hrateZero : endFlowVatIlkRateWord out = ⟨0⟩
                    · obtain ⟨_, _, rd3041raw⟩ :=
                        endFlowX_rmulReturnsZero
                          (x := endFlowArtWord σ' I) (y := endFlowVatIlkRateWord out)
                          (ret := ⟨3041⟩)
                          (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlkRateWord out,
                            endFlowIlkWord I, endFlowReturnPc, endSelWord I])
                          hrateZero rdWad0Entry (by jump_dest)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact ⟨_, _, by simpa [endFlowWad0Word] using rd3041raw⟩
                    · obtain ⟨_, _, rd3041raw⟩ :=
                        endFlowX_rmulReturns
                          (x := endFlowArtWord σ' I) (y := endFlowVatIlkRateWord out)
                          (ret := ⟨3041⟩)
                          (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlkRateWord out,
                            endFlowIlkWord I, endFlowReturnPc, endSelWord I])
                          hfitWad0 hrateZero rdWad0Entry (by jump_dest)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact ⟨_, _, by simpa [endFlowWad0Word] using rd3041raw⟩
                  obtain ⟨_, _, rdWadEntry⟩ :=
                    endFlowX_wadRmulEntry (g := Sat256.ofUInt256 g) hsz36 rd3041
                  by_cases hoverWad :
                      UInt256.size ≤
                        (endFlowWad0Word σ' I out).toNat * (endFlowTagWord σ' I).toNat
                  · have htail :=
                      endFlowTailReverts_wadRmulOverflow evmVatSolm I σ' out hsz36
                        hArtLoad hTagLoad hfitWad0 hoverWad
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endFlowStore I)
                          flowTransition.body .reverted := by
                      simpa [evmVatSolm, evmSolm] using
                        endFlowBodyReverts_vatIlksOkTailReverted
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := g)
                          (evmVat := evmVatSolm) (out := out)
                          hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                          (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                          hlo htail
                    exact
                      (endFlowX_rmulOverflow
                        (x := endFlowWad0Word σ' I out) (y := endFlowTagWord σ' I)
                        (ret := ⟨3061⟩)
                        (R := [⟨0⟩, endFlowVatIlkRateWord out, endFlowIlkWord I,
                          endFlowReturnPc, endSelWord I])
                        hoverWad rdWadEntry
                        (by simp only [List.length_cons, List.length_nil]; omega))
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hfitWad :
                      (endFlowWad0Word σ' I out).toNat * (endFlowTagWord σ' I).toNat <
                        UInt256.size :=
                      Nat.lt_of_not_ge hoverWad
                    obtain ⟨_, _, rd3061⟩ : ∃ k' C',
                        RD endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3061⟩
                          (endFlowWadWord σ' I out :: ⟨0⟩ ::
                            endFlowVatIlkRateWord out :: endFlowIlkWord I ::
                            endFlowReturnPc :: endSelWord I :: [])
                          (twoWordHashMem (endFlowIlkWord I) ⟨12⟩
                            (twoWordHashMem (endFlowIlkWord I) ⟨14⟩
                              (endFlowVatIlksPostCallMem I out)))
                          (UInt256.ofNat 9) out (cA', σ') k' C' := by
                      by_cases htagZero : endFlowTagWord σ' I = ⟨0⟩
                      · obtain ⟨_, _, rd3061raw⟩ :=
                          endFlowX_rmulReturnsZero
                            (x := endFlowWad0Word σ' I out)
                            (y := endFlowTagWord σ' I)
                            (ret := ⟨3061⟩)
                            (R := [⟨0⟩, endFlowVatIlkRateWord out, endFlowIlkWord I,
                              endFlowReturnPc, endSelWord I])
                            htagZero rdWadEntry (by jump_dest)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        exact ⟨_, _, by simpa [endFlowWadWord] using rd3061raw⟩
                      · obtain ⟨_, _, rd3061raw⟩ :=
                          endFlowX_rmulReturns
                            (x := endFlowWad0Word σ' I out)
                            (y := endFlowTagWord σ' I)
                            (ret := ⟨3061⟩)
                            (R := [⟨0⟩, endFlowVatIlkRateWord out, endFlowIlkWord I,
                              endFlowReturnPc, endSelWord I])
                            hfitWad htagZero rdWadEntry (by jump_dest)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        exact ⟨_, _, by simpa [endFlowWadWord] using rd3061raw⟩
                    by_cases hsubUnder :
                        (endFlowWadWord σ' I out).toNat < (endFlowGapWord σ' I).toNat
                    · have htail :=
                        endFlowTailReverts_subUnderflow evmVatSolm I σ' out hsz36
                          hArtLoad hTagLoad hGapLoad hfitWad0 hfitWad hsubUnder
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endFlowStore I)
                            flowTransition.body .reverted := by
                        simpa [evmVatSolm, evmSolm] using
                          endFlowBodyReverts_vatIlksOkTailReverted
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := g)
                            (evmVat := evmVatSolm) (out := out)
                            hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                            (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                            hlo htail
                      exact (endFlowX_tailSubUnderflow hsz36 hlo hsubUnder rd3061)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hleSub :
                        (endFlowGapWord σ' I).toNat ≤
                          (endFlowWadWord σ' I out).toNat :=
                        Nat.le_of_not_gt hsubUnder
                      by_cases hoverMul :
                          UInt256.size ≤
                            (endFlowNum0Word σ' I out).toNat * endRayWord.toNat
                      · have htail :=
                          endFlowTailReverts_mulOverflow evmVatSolm I σ' out hsz36
                            hArtLoad hTagLoad hGapLoad hfitWad0 hfitWad hleSub hoverMul
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endFlowStore I)
                              flowTransition.body .reverted := by
                          simpa [evmVatSolm, evmSolm] using
                            endFlowBodyReverts_vatIlksOkTailReverted
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                              (A := A) (I := I) (g := g)
                              (evmVat := evmVatSolm) (out := out)
                              hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                              (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                              hlo htail
                        exact (endFlowX_tailMulOverflow hsz36 hlo hleSub hoverMul rd3061)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitMul :
                          (endFlowNum0Word σ' I out).toNat * endRayWord.toNat <
                            UInt256.size :=
                          Nat.lt_of_not_ge hoverMul
                        by_cases hdenZero : endFlowDenWord σ' I = ⟨0⟩
                        · have htail :=
                            endFlowTailReverts_denZero evmVatSolm I σ' out hsz36
                              hArtLoad hTagLoad hGapLoad hDebtLoad hfitWad0 hfitWad hleSub
                              hfitMul hdenZero
                          have hbody :
                              ExecTransitionBody config contract evmSolm (endFlowStore I)
                                flowTransition.body .reverted := by
                            simpa [evmVatSolm, evmSolm] using
                              endFlowBodyReverts_vatIlksOkTailReverted
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmVat := evmVatSolm) (out := out)
                                hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                                (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                hlo htail
                          have hinvalidOr :=
                            endFlowX_tailDenInvalid
                              (g := Sat256.ofUInt256 g) hsz36 hlo hleSub hfitMul hdenZero
                              rd3061
                          rcases hinvalidOr with hoog | hinvalid
                          · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                              rw [← hcode] at hoog
                              simpa [initState, Sat256.ofUInt256] using hoog))
                          · have hxi :
                                Ξ cA gh bl σ_evm σ₀ g A I =
                                  .error .InvalidInstruction :=
                              Xi_error_of_X (g := g) (by
                                rw [← hcode] at hinvalid
                                simpa [initState, Sat256.ofUInt256] using hinvalid)
                            exact reEquiv_execution hdispatch hdecode hbody
                              (execResultsEquiv.invalidHalt hxi rfl)
                        · have htail :=
                            endFlowTailReturns evmVatSolm I σ' out hsz36
                              hArtLoad hTagLoad hGapLoad hDebtLoad hfitWad0 hfitWad
                              hleSub hfitMul hdenZero
                          have hbody :
                              ExecTransitionBody config contract evmSolm (endFlowStore I)
                                flowTransition.body
                                (.returned
                                  { contract := contract,
                                    locals := endFlowStoreFixV σ' I out }
                                  (endFlowPostState evmVatSolm I
                                    (endFlowFixVWord σ' I out)) none) := by
                            simpa [evmVatSolm, evmSolm] using
                              endFlowBodyReturns_vatIlksOkTail
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmVat := evmVatSolm) (out := out)
                                hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                                (by simpa [evmVatSolm, evmSolm] using hcallSolm)
                                hlo htail
                          have hret :=
                            endFlowX_tailReturns
                              (g := Sat256.ofUInt256 g) hperm hsz36 hlo hleSub hfitMul
                              hdenZero rd3061
                          have hStatePost :
                              EVMStateEquiv
                                (endFlowPostState evmVatEvm I (endFlowFixVWord σ' I out))
                                (endFlowPostState evmVatSolm I (endFlowFixVWord σ' I out)) := by
                            simpa [endFlowPostState] using
                              hStateCall.storageStore_codeOwner (endFlowFixSlot I)
                                (val₁ := endFlowFixVWord σ' I out)
                                (val₂ := endFlowFixVWord σ' I out) rfl
                          exact hret.reEquivExecutionGenEVMStateEquiv
                            (evm'_evm :=
                              endFlowPostState evmVatEvm I (endFlowFixVWord σ' I out))
                            (evm'_solm :=
                              endFlowPostState evmVatSolm I (endFlowFixVWord σ' I out))
                            hcode hdispatch hdecode hbody
                            (by
                              simp [evmVatEvm, endFlowPostState, initState,
                                storageStore_createdAccounts])
                            (by
                              simpa [evmVatEvm, endFlowPostState, initState,
                                storageStore_accountMap, endFlowPostAccountMap] using
                                accountMapEquiv.refl
                                  (endFlowPostAccountMap σ' I (endFlowFixVWord σ' I out)))
                            hStatePost
                            (by
                              simpa [flowTransition] using
                                (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                                  (t := []) (dvs := []) rfl (by native_decide)
                                  (by native_decide)))
          · rw [not_lt] at hdepthLt
            have hdepthEq : I.depth = 1024 :=
              Fin.ext (by have := I.depth.isLt; omega)
            obtain ⟨_, _, rd2964⟩ :=
              endFlowX_vatIlksCallDepthLimit
                (g := Sat256.ofUInt256 g) hcallReady hdepthEq
            let A_vat :=
              (evmSolm.addAccessedAccount (EVM.address (endPackVatAddr σ_solm I))).substate
            have hcallSolm :
                typedCallViaEVM config evmSolm
                  (EVM.address (endPackVatAddr σ_solm I)) "vatIlks" 0
                  [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                  (false, { evmSolm with substate := A_vat }, ByteArray.empty) true := by
              simpa [evmSolm, A_vat] using
                (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                  (tgt := EVM.address (endPackVatAddr σ_solm I)) (name := "vatIlks")
                  (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                  (callPerm := true)
                  (endFlowVatIlksEncode_eq I hsz36
                    (twoWordHashMem_size_96 (endFlowIlkWord I) ⟨15⟩ solcFreePtrMem_size))
                  (by simpa [evmSolm, initState] using hdepthEq))
            have hbody :
                ExecTransitionBody config contract evmSolm (endFlowStore I)
                  flowTransition.body .reverted := by
              simpa [evmSolm] using
                endFlowBodyReverts_vatIlksCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmVat := { evmSolm with substate := A_vat })
                  (out := ByteArray.empty)
                  hwv hsz36 hdebtSolm hfixSolm hvatCodeSolmNE
                  (by simpa [evmSolm] using hcallSolm)
            exact (endFlowX_vatIlksCallFailed (g := Sat256.ofUInt256 g) rd2964
              (by native_decide))
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hfixSolm : endFlowFixWord σ_solm I ≠ ⟨0⟩ := by
          intro hbad
          exact hfix (by rw [hfixCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endFlowStore I)
              flowTransition.body .reverted := by
          simpa [evmSolm] using
            endFlowBodyReverts_fixNonzero
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz36 hdebtSolm hfixSolm
        exact (endFlowX_fixNonzero (g := Sat256.ofUInt256 g) hsz36 hdebt hfix hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endFlowBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
