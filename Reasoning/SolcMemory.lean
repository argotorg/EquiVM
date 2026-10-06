import Reasoning.Solc
import Reasoning.MemoryShapes

/-!
# Compiler memory shapes and mapping hashes

Reusable facts for common scratch regions, independent of any contract or bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem solcErrorStringMem0_size_grown {mem : ByteArray} (hmem : 160 ≤ mem.size) :
    (solcErrorStringMem0 mem).size = mem.size := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  omega

theorem solcErrorStringMem1_size_grown {mem : ByteArray} (hmem : 164 ≤ mem.size) :
    (solcErrorStringMem1 mem).size = mem.size := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_grown (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_grown (show (160 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

theorem solcErrorStringMem2_size_grown (len : UInt256) {mem : ByteArray} (hmem : 196 ≤ mem.size) :
    (solcErrorStringMem2 len mem).size = mem.size := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_grown (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_grown (show (164 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

theorem solcErrorStringMem3_size_grown (len word : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size) :
    (solcErrorStringMem3 len word mem).size = mem.size := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_grown len (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_grown len (show (196 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

theorem solcErrorStringMem3_read64_grown (len word : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_grown len (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_grown (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_grown (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  exact hread64

/-- **Grown analogue of `solcErrorStringMem3_mload64`.** After the error-string is written into the
    grown memory, `MLOAD 0x40` still reads the free pointer `0x80` (the writes are all above `0x60`
    and the offset `0x40` is well within the grown active-words). -/
theorem solcErrorStringMem3_mload64_grown (len word : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [solcErrorStringMem3_size_grown len word hmem]; omega)
    (solcErrorStringMem3_read64_grown len word hmem hread64)


theorem twoWordHashMem_solcMappingSlot_of_ge (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem wordAt32TwoWordHashMem_solcMappingSlot {mem : ByteArray}
    (baseSlot key oldSlot : UInt256) (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((wordAt32Mem baseSlot (twoWordHashMem key oldSlot mem)).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [wordAt32TwoWordHashMem_read0_64 key oldSlot baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot


theorem twoWordHashMemAt_slot {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMemAt mem key slot).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  rw [twoWordHashMemAt_read0_64 key slot hmem]
  unfold solcMappingSlot
  rw [uInt256OfByteArray_eq]

theorem solcNestedMappingCallerHashMem_size_96 {mem : ByteArray}
    (baseSlot owner : UInt256) (I : ExecutionEnv) (hmem : mem.size = 96) :
    (solcNestedMappingCallerHashMem baseSlot owner I mem).size = 96 := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 (solcSourceWord I) (solcMappingSlot baseSlot owner)
    (twoWordHashMem_size_96 owner baseSlot hmem)

theorem solcNestedMappingCallerHashMem_read64_96 {mem : ByteArray}
    (baseSlot owner : UInt256) (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcNestedMappingCallerHashMem baseSlot owner I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 (solcSourceWord I) (solcMappingSlot baseSlot owner)
    (twoWordHashMem_size_96 owner baseSlot hmem)
    (twoWordHashMem_read64 owner baseSlot hmem hread64)

theorem wordAt0Mem_solcMappingSlot_of_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread32 : mem.readWithPadding 32 32 = UInt256.toByteArray slot) :
    UInt256.ofNat
        (fromByteArrayBigEndian (KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  have hread0 :
      (wordAt0Mem key mem).readWithPadding 0 32 = UInt256.toByteArray key :=
    wordAt0Mem_read0 key mem
  have hread32' :
      (wordAt0Mem key mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [hmem]; omega)
      (by omega)
      (by rw [hmem]; omega)]
    exact hread32
  have hread0_64 :
      (wordAt0Mem key mem).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray slot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [wordAt0Mem_size_96 key hmem]; omega)]
    have hleft :
        (wordAt0Mem key mem).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0
          (by rw [wordAt0Mem_size_96 key hmem]; omega),
        hread0]
    have hright :
        (wordAt0Mem key mem).extract 32 64 = UInt256.toByteArray slot := by
      rw [← readWithPadding_eq_extract _ 32
          (by rw [wordAt0Mem_size_96 key hmem]; omega),
        hread32']
    rw [show (wordAt0Mem key mem).extract 0 64 =
        (wordAt0Mem key mem).extract 0 32 ++
          (wordAt0Mem key mem).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key slot


theorem twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot


theorem twoWordHashMem_solcMappingSlot_any (baseSlot key : UInt256) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key :=
  by
    rw [twoWordHashMem_read0_64_any key baseSlot mem]
    unfold solcMappingSlot
    exact mappingSlot_single key baseSlot

theorem twoWordHashMem_solcMappingSlot_of_size_ge
    (baseSlot key : UInt256) {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_size_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot


set_option maxHeartbeats 1000000 in
theorem wordAt0Mem_twoWordHashMem_solcMappingSlot (baseSlot key oldKey : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  have hbase : (twoWordHashMem oldKey baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 oldKey baseSlot hmem
  have hread64 :
      (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
        (by rw [wordAt0Mem_size_96 key hbase]; omega)]
    have hleft :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 =
          UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0
          (by rw [wordAt0Mem_size_96 key hbase]; omega),
        wordAt0Mem_read0]
    have hright :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 =
          UInt256.toByteArray baseSlot := by
      rw [← readWithPadding_eq_extract _ 32
          (by rw [wordAt0Mem_size_96 key hbase]; omega)]
      unfold wordAt0Mem
      rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [hbase]; omega)
        (by omega) (by rw [hbase]; norm_num)]
      exact twoWordHashMem_read32 oldKey baseSlot hmem
    rw [show (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 64 =
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 ++
          (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread64]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

set_option maxHeartbeats 800000 in
theorem wordAt32Mem_solcMappingSlot_of_read0 {mem : ByteArray} (key baseSlot : UInt256)
    (hmem : mem.size = 96)
    (hread0 : mem.readWithPadding 0 32 = UInt256.toByteArray key) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((wordAt32Mem baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  have hmem32 : (wordAt32Mem baseSlot mem).size = 96 :=
    wordAt32Mem_size_96 baseSlot hmem
  have hread :
      (wordAt32Mem baseSlot mem).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hmem32]; omega)]
    have hleft :
        (wordAt32Mem baseSlot mem).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0 (by rw [hmem32]; omega)]
      unfold wordAt32Mem
      rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
        (by rw [hmem]; omega) (by omega)]
      rw [hread0]
    have hright :
        (wordAt32Mem baseSlot mem).extract 32 64 = UInt256.toByteArray baseSlot := by
      rw [← readWithPadding_eq_extract _ 32 (by rw [hmem32]; omega)]
      unfold wordAt32Mem
      rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray baseSlot).size ≤ 32
        rw [toByteArray_size])
    rw [show (wordAt32Mem baseSlot mem).extract 0 64 =
        (wordAt32Mem baseSlot mem).extract 0 32 ++
          (wordAt32Mem baseSlot mem).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

/-- Overwriting `mem[0]` with `key` (leaving `slot` at `mem[32]`) makes the first 64 scratch bytes
    hash to the mapping slot `keccak(key ‖ slot)`. -/
theorem wordAt0Mem_keccak {m : ByteArray} (key slot : UInt256) (hm : m.size = 96)
    (hread32 : m.readWithPadding 32 32 = UInt256.toByteArray slot) :
    UInt256.ofNat (fromByteArrayBigEndian (KEC ((wordAt0Mem key m).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  have hread0 : (wordAt0Mem key m).readWithPadding 0 32 = UInt256.toByteArray key :=
    wordAt0Mem_read0 key m
  have hread32' : (wordAt0Mem key m).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [hm]; omega) (by omega)
      (by rw [hm]; omega)]
    exact hread32
  have hread0_64 : (wordAt0Mem key m).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [wordAt0Mem_size_96 key hm]; omega)]
    have hleft : (wordAt0Mem key m).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0 (by rw [wordAt0Mem_size_96 key hm]; omega), hread0]
    have hright : (wordAt0Mem key m).extract 32 64 = UInt256.toByteArray slot := by
      rw [← readWithPadding_eq_extract _ 32 (by rw [wordAt0Mem_size_96 key hm]; omega), hread32']
    rw [show (wordAt0Mem key m).extract 0 64 =
        (wordAt0Mem key m).extract 0 32 ++ (wordAt0Mem key m).extract 32 64 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [hleft, hright]
  rw [hread0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

theorem twoWordHashMem_mapSlot_of_ge64 {mem : ByteArray} (key baseSlot : UInt256)
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  simpa [solcMappingSlot] using mappingSlot_single key baseSlot


end Reasoning.Theory
