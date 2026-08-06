import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.OutputReadback.Slot1216

/-!
# BLAKE2F fallback output-buffer readback at 1248
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem1_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem1 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem1 outputWord1Mem
  exact toByteArray_write_read_self_extract32 (outputWord1 (outputWordsMem0 mem))
    (outputWordsMem0 mem) 1248
    (by rw [outputWordsMem0_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem2_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem2 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem2 outputWord2Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord2 (outputWordsMem1 mem)) (outputWordsMem1 mem) 1280 1248
    (by rw [outputWordsMem1_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem1_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem1_read1248_32_extract hmem

theorem outputWordsMem3_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem3 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem3 outputWord3Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord3 (outputWordsMem2 mem)) (outputWordsMem2 mem) 1312 1248
    (by rw [outputWordsMem2_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem2_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem2_read1248_32_extract hmem

theorem outputWordsMem4_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem4 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem4 outputWord4Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord4 (outputWordsMem3 mem)) (outputWordsMem3 mem) 1344 1248
    (by rw [outputWordsMem3_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem3_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem3_read1248_32_extract hmem

theorem outputWordsMem5_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem5 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem5 outputWord5Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord5 (outputWordsMem4 mem)) (outputWordsMem4 mem) 1376 1248
    (by rw [outputWordsMem4_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem4_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem4_read1248_32_extract hmem

theorem outputWordsMem6_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem6 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem6 outputWord6Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord6 (outputWordsMem5 mem)) (outputWordsMem5 mem) 1408 1248
    (by rw [outputWordsMem5_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem5_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem5_read1248_32_extract hmem

theorem outputWordsMem7_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem7 outputWord7Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord7 (outputWordsMem6 mem)) (outputWordsMem6 mem) 1440 1248
    (by rw [outputWordsMem6_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem6_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem6_read1248_32_extract hmem

theorem outputWordsMem_read1248_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).readWithPadding 1248 32 =
      (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))).extract 0 32 := by
  unfold outputWordsMem
  exact outputWordsMem7_read1248_32_extract hmem


end Blake2f
