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

theorem solcErrorStringMem0_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem0 mem).size = 196 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem1 mem).size = 196 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size196 hmem]

theorem solcErrorStringMem2_size_of_size196 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size196 hmem]

theorem solcErrorStringMem3_size_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size196 len hmem])]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size196 len hmem]

theorem solcErrorStringMem3_read64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size196 len word hmem]; decide)
    (solcErrorStringMem3_read64_of_size196 len word hmem hread64)

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

theorem twoWordHashMem_solcMappingSlot_160 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_160 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem solcErrorStringMem0_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem0 mem).size = 160 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem1 mem).size = 164 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size160 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size160 hmem])]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem3_size_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size160 len hmem])]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size160 len hmem,
    toByteArray_size]

theorem solcErrorStringMem3_read64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size160 len word hmem]; decide)
    (solcErrorStringMem3_read64_of_size160 len word hmem hread64)

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

theorem twoWordHashMem_solcMappingSlot_256 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_256 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem twoWordHashMem_solcMappingSlot_580 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 580) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_580 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem solcErrorStringMem0_size_260 {mem : ByteArray} (hmem : mem.size = 260) :
    (solcErrorStringMem0 mem).size = 260 := by
  unfold solcErrorStringMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 128 260 260
    hmem (by omega) (by omega)

theorem solcErrorStringMem1_size_260 {mem : ByteArray} (hmem : mem.size = 260) :
    (solcErrorStringMem1 mem).size = 260 := by
  unfold solcErrorStringMem1
  exact toByteArray_write32_size_of_le (solcErrorStringMem0 mem) ⟨32⟩ 132 260 260
    (solcErrorStringMem0_size_260 hmem)
    (by rw [solcErrorStringMem0_size_260 hmem]; omega) (by omega)

theorem solcErrorStringMem2_size_260 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem2 len mem).size = 260 := by
  unfold solcErrorStringMem2
  exact toByteArray_write32_size_of_le (solcErrorStringMem1 mem) len 164 260 260
    (solcErrorStringMem1_size_260 hmem)
    (by rw [solcErrorStringMem1_size_260 hmem]; omega) (by omega)

theorem solcErrorStringMem3_size_260 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (solcErrorStringMem3 len word mem).size = 260 := by
  unfold solcErrorStringMem3
  exact toByteArray_write32_size_of_le (solcErrorStringMem2 len mem) word 196 260 260
    (solcErrorStringMem2_size_260 len hmem)
    (by rw [solcErrorStringMem2_size_260 len hmem]; omega) (by omega)

theorem solcErrorStringMem3_read64_260 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_260 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_260 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_260 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_260 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_260 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem solcErrorStringMem0_size_of_size288 {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem0 mem).size = 288 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size288 {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem1 mem).size = 288 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem0_size_of_size288 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size288 hmem]

theorem solcErrorStringMem2_size_of_size288 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 288) :
    (solcErrorStringMem2 len mem).size = 288 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem1_size_of_size288 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size288 hmem]

theorem solcErrorStringMem3_size_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288) :
    (solcErrorStringMem3 len word mem).size = 288 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem2_size_of_size288 len hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size288 len hmem]

theorem solcErrorStringMem3_read64_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size288 len hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem2_size_of_size288 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size288 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem1_size_of_size288 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size288 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem0_size_of_size288 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size288 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [solcErrorStringMem3_size_of_size288 len word hmem]; decide)
      (solcErrorStringMem3_read64_of_size288 len word hmem hread64)

theorem solcErrorStringMem0_size_of_size384 {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem0 mem).size = 384 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size384 {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem1 mem).size = 384 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem0_size_of_size384 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size384 hmem]

theorem solcErrorStringMem2_size_of_size384 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem2 len mem).size = 384 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem1_size_of_size384 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size384 hmem]

theorem solcErrorStringMem3_size_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384) :
    (solcErrorStringMem3 len word mem).size = 384 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem2_size_of_size384 len hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size384 len hmem]

theorem solcErrorStringMem3_read64_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size384 len hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem2_size_of_size384 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size384 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem1_size_of_size384 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size384 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem0_size_of_size384 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [solcErrorStringMem3_size_of_size384 len word hmem]; decide)
      (solcErrorStringMem3_read64_of_size384 len word hmem hread64)

theorem solcErrorStringMem0_size_of_size320 {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem0 mem).size = 320 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size320 {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem1 mem).size = 320 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem0_size_of_size320 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size320 hmem]

theorem solcErrorStringMem2_size_of_size320 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem2 len mem).size = 320 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem1_size_of_size320 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size320 hmem]

theorem solcErrorStringMem3_size_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorStringMem3 len word mem).size = 320 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [solcErrorStringMem2_size_of_size320 len hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size320 len hmem]

theorem solcErrorStringMem3_read64_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size320 len hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem2_size_of_size320 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size320 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem1_size_of_size320 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size320 hmem]; omega) (by omega)
      (by
        rw [solcErrorStringMem0_size_of_size320 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [solcErrorStringMem3_size_of_size320 len word hmem]; decide)
      (solcErrorStringMem3_read64_of_size320 len word hmem hread64)

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

theorem solcErrorStringMem0_size_of_size228 {mem : ByteArray} (hmem : mem.size = 228) :
    (solcErrorStringMem0 mem).size = 228 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size228 {mem : ByteArray} (hmem : mem.size = 228) :
    (solcErrorStringMem1 mem).size = 228 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_of_size228 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size228 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (solcErrorStringMem2 len mem).size = 228 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_of_size228 hmem,
    toByteArray_size]

theorem solcErrorStringMem3_size_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_of_size228 len hmem,
    toByteArray_size]

theorem solcErrorStringMem3_read64_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size228 len word hmem]; decide)
    (solcErrorStringMem3_read64_of_size228 len word hmem hread64)

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

def solcErrorString320Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem 320 32

def solcErrorString320Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (solcErrorString320Mem0 mem) 324 32

def solcErrorString320Mem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray len).write 0 (solcErrorString320Mem1 mem) 356 32

def solcErrorString320Mem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 (solcErrorString320Mem2 len mem) 388 32

theorem solcErrorString320Mem0_size {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorString320Mem0 mem).size = 352 := by
  unfold solcErrorString320Mem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 320 320 352 hmem (by omega)
    (by omega)

theorem solcErrorString320Mem1_size {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorString320Mem1 mem).size = 356 := by
  unfold solcErrorString320Mem1
  exact toByteArray_write32_size_of_le (solcErrorString320Mem0 mem) (⟨32⟩ : UInt256) 324 352 356
    (solcErrorString320Mem0_size hmem) (by rw [solcErrorString320Mem0_size hmem]; omega) (by omega)

theorem solcErrorString320Mem2_size (len : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorString320Mem2 len mem).size = 388 := by
  unfold solcErrorString320Mem2
  exact toByteArray_write32_size_of_le (solcErrorString320Mem1 mem) len 356 356 388
    (solcErrorString320Mem1_size hmem) (Nat.le_of_eq (solcErrorString320Mem1_size hmem).symm)
      (by omega)

theorem solcErrorString320Mem3_size (len word : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorString320Mem3 len word mem).size = 420 := by
  unfold solcErrorString320Mem3
  exact toByteArray_write32_size_of_le (solcErrorString320Mem2 len mem) word 388 388 420
    (solcErrorString320Mem2_size len hmem)
      (Nat.le_of_eq (solcErrorString320Mem2_size len hmem).symm) (by omega)

/-- The free pointer `mem[0x40] = 320` survives all four error-string writes (offsets `≥ 320 > 96`). -/
theorem solcErrorString320Mem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩) :
    (solcErrorString320Mem3 len word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩ := by
  unfold solcErrorString320Mem3
  rw [toByteArray_write_read_below_of_gap word _ 388 64
      (by rw [solcErrorString320Mem2_size len hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorString320Mem2
  rw [toByteArray_write_read_below_of_gap len _ 356 64
      (by rw [solcErrorString320Mem1_size hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorString320Mem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
      (by rw [solcErrorString320Mem0_size hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorString320Mem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
      (by rw [hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  exact hread64

/-- `MLOAD 0x40` over the fully-written error-string memory pushes the free pointer `320`. -/
theorem solcErrorString320Mem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorString320Mem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorString320Mem3 len word mem).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨320⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [solcErrorString320Mem3_size len word hmem]; decide)
    (solcErrorString320Mem3_read64 len word hmem hread64)

abbrev solcErrorString384Mem0 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 solcErrorStringSelector

abbrev solcErrorString384Mem1 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (solcErrorString384Mem0 mem) 388 ⟨32⟩

abbrev solcErrorString384Mem2 (len : UInt256) (mem : ByteArray) :
    ByteArray :=
  Reasoning.Theory.writeWord (solcErrorString384Mem1 mem) 420 len

abbrev solcErrorString384Mem3
    (len word : UInt256) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (solcErrorString384Mem2 len mem) 452 word

theorem solcErrorString384Mem0_size {mem : ByteArray} (hmem : mem.size = 544) :
    (solcErrorString384Mem0 mem).size = 544 := by
  unfold solcErrorString384Mem0
  rw [Reasoning.Theory.writeWord_size mem 384 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos)]
  rw [hmem]
  norm_num

theorem solcErrorString384Mem1_size {mem : ByteArray} (hmem : mem.size = 544) :
    (solcErrorString384Mem1 mem).size = 544 := by
  unfold solcErrorString384Mem1
  rw [Reasoning.Theory.writeWord_size (solcErrorString384Mem0 mem) 388 ⟨32⟩
    (by rw [solcErrorString384Mem0_size hmem]; exact USize.size_pos)]
  rw [solcErrorString384Mem0_size hmem]
  norm_num

theorem solcErrorString384Mem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (solcErrorString384Mem2 len mem).size = 544 := by
  unfold solcErrorString384Mem2
  rw [Reasoning.Theory.writeWord_size (solcErrorString384Mem1 mem) 420 len
    (by rw [solcErrorString384Mem1_size hmem]; exact USize.size_pos)]
  rw [solcErrorString384Mem1_size hmem]
  norm_num

theorem solcErrorString384Mem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (solcErrorString384Mem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold solcErrorString384Mem2
  rw [Reasoning.Theory.writeWord_read_preserved
    (solcErrorString384Mem1 mem) 420 64 len
    (by rw [solcErrorString384Mem1_size hmem]; exact USize.size_pos)
    (by left; rw [solcErrorString384Mem1_size hmem]; omega)]
  unfold solcErrorString384Mem1
  rw [Reasoning.Theory.writeWord_read_preserved
    (solcErrorString384Mem0 mem) 388 64 (⟨32⟩ : UInt256)
    (by rw [solcErrorString384Mem0_size hmem]; exact USize.size_pos)
    (by left; rw [solcErrorString384Mem0_size hmem]; omega)]
  unfold solcErrorString384Mem0
  rw [Reasoning.Theory.writeWord_read_preserved mem 384 64 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos) (by left; rw [hmem]; omega)]
  exact hread64

theorem solcErrorString384Mem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (solcErrorString384Mem3 len word mem).size = 544 := by
  unfold solcErrorString384Mem3
  rw [Reasoning.Theory.writeWord_size (solcErrorString384Mem2 len mem) 452 word
    (by rw [solcErrorString384Mem2_size len hmem]; exact USize.size_pos)]
  rw [solcErrorString384Mem2_size len hmem]
  norm_num

theorem solcErrorString384Mem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (solcErrorString384Mem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold solcErrorString384Mem3
  rw [Reasoning.Theory.writeWord_read_preserved
    (solcErrorString384Mem2 len mem) 452 64 word
    (by rw [solcErrorString384Mem2_size len hmem]; exact USize.size_pos)
    (by left; rw [solcErrorString384Mem2_size len hmem]; omega)]
  unfold solcErrorString384Mem2
  rw [Reasoning.Theory.writeWord_read_preserved
    (solcErrorString384Mem1 mem) 420 64 len
    (by rw [solcErrorString384Mem1_size hmem]; exact USize.size_pos)
    (by left; rw [solcErrorString384Mem1_size hmem]; omega)]
  unfold solcErrorString384Mem1
  rw [Reasoning.Theory.writeWord_read_preserved
    (solcErrorString384Mem0 mem) 388 64 (⟨32⟩ : UInt256)
    (by rw [solcErrorString384Mem0_size hmem]; exact USize.size_pos)
    (by left; rw [solcErrorString384Mem0_size hmem]; omega)]
  unfold solcErrorString384Mem0
  rw [Reasoning.Theory.writeWord_read_preserved mem 384 64 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos) (by left; rw [hmem]; omega)]
  exact hread64

theorem solcErrorString384Mem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorString384Mem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorString384Mem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [solcErrorString384Mem3_size len word hmem]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using
        solcErrorString384Mem3_read64 len word hmem hread64)

def solcErrorString576Mem0 (mem : ByteArray) : ByteArray :=
  writeWordMem 576 solcErrorStringSelector mem

def solcErrorString576Mem1 (mem : ByteArray) : ByteArray :=
  writeWordMem 580 (⟨32⟩ : UInt256) (solcErrorString576Mem0 mem)

def solcErrorString576Mem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  writeWordMem 612 len (solcErrorString576Mem1 mem)

def solcErrorString576Mem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  writeWordMem 644 word (solcErrorString576Mem2 len mem)

theorem solcErrorString576Mem0_size {mem : ByteArray} (hmem : mem.size = 576) :
    (solcErrorString576Mem0 mem).size = 608 := by
  unfold solcErrorString576Mem0 writeWordMem
  rw [toByteArray_write32_size_of_ge mem solcErrorStringSelector 576 576 608
    hmem (by omega) (by exact USize.size_pos) (by omega)]

theorem solcErrorString576Mem1_size {mem : ByteArray} (hmem : mem.size = 576) :
    (solcErrorString576Mem1 mem).size = 612 := by
  unfold solcErrorString576Mem1 writeWordMem
  rw [toByteArray_write32_size_of_le (solcErrorString576Mem0 mem) (⟨32⟩ : UInt256)
    580 608 612 (solcErrorString576Mem0_size hmem)
    (by rw [solcErrorString576Mem0_size hmem]; omega) (by omega)]

theorem solcErrorString576Mem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576) :
    (solcErrorString576Mem2 len mem).size = 644 := by
  unfold solcErrorString576Mem2 writeWordMem
  rw [toByteArray_write32_size_of_ge (solcErrorString576Mem1 mem) len
    612 612 644 (solcErrorString576Mem1_size hmem) (by omega)
    (by exact USize.size_pos) (by omega)]

theorem solcErrorString576Mem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576) :
    (solcErrorString576Mem3 len word mem).size = 676 := by
  unfold solcErrorString576Mem3 writeWordMem
  rw [toByteArray_write32_size_of_ge (solcErrorString576Mem2 len mem) word
    644 644 676 (solcErrorString576Mem2_size len hmem) (by omega)
    (by exact USize.size_pos) (by omega)]

theorem solcErrorString576Mem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩) :
    (solcErrorString576Mem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  let err0 := solcErrorString576Mem0 mem
  let err1 := solcErrorString576Mem1 mem
  let err2 := solcErrorString576Mem2 len mem
  have herr0Size : err0.size = 608 := by
    unfold err0
    exact solcErrorString576Mem0_size hmem
  have herr1Size : err1.size = 612 := by
    unfold err1
    exact solcErrorString576Mem1_size hmem
  have herr2Size : err2.size = 644 := by
    unfold err2
    exact solcErrorString576Mem2_size len hmem
  have herr0Read : err0.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err0 solcErrorString576Mem0
    rw [writeWordMem_read64_below]
    · exact hread64
    · rw [hmem]; omega
    · omega
    · rw [hmem]; exact USize.size_pos
  have herr1Read : err1.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err1 solcErrorString576Mem1
    change (writeWordMem 580 (⟨32⟩ : UInt256) err0).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr0Read
    · rw [herr0Size]; omega
    · omega
    · rw [herr0Size]; exact USize.size_pos
  have herr2Read : err2.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩ := by
    unfold err2 solcErrorString576Mem2
    change (writeWordMem 612 len err1).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩
    rw [writeWordMem_read64_below]
    · exact herr1Read
    · rw [herr1Size]; omega
    · omega
    · rw [herr1Size]; exact USize.size_pos
  unfold solcErrorString576Mem3
  change (writeWordMem 644 word err2).readWithPadding 64 32 =
    UInt256.toByteArray ⟨576⟩
  rw [writeWordMem_read64_below]
  · exact herr2Read
  · rw [herr2Size]; omega
  · omega
  · rw [herr2Size]; exact USize.size_pos

end Reasoning.Theory
