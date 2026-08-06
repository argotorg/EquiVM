import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.OutputReadback.Slot1280

/-!
# BLAKE2F fallback output-buffer readback at 1312
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem3_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem3 mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem3 outputWord3Mem
  exact toByteArray_write_read_self_extract32 (outputWord3 (outputWordsMem2 mem))
    (outputWordsMem2 mem) 1312
    (by rw [outputWordsMem2_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem4_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem4 mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem4 outputWord4Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord4 (outputWordsMem3 mem)) (outputWordsMem3 mem) 1344 1312
    (by rw [outputWordsMem3_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem3_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem3_read1312_32_extract hmem

theorem outputWordsMem5_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem5 mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem5 outputWord5Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord5 (outputWordsMem4 mem)) (outputWordsMem4 mem) 1376 1312
    (by rw [outputWordsMem4_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem4_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem4_read1312_32_extract hmem

theorem outputWordsMem6_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem6 mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem6 outputWord6Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord6 (outputWordsMem5 mem)) (outputWordsMem5 mem) 1408 1312
    (by rw [outputWordsMem5_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem5_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem5_read1312_32_extract hmem

theorem outputWordsMem7_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem7 outputWord7Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord7 (outputWordsMem6 mem)) (outputWordsMem6 mem) 1440 1312
    (by rw [outputWordsMem6_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem6_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem6_read1312_32_extract hmem

theorem outputWordsMem_read1312_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).readWithPadding 1312 32 =
      (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))).extract 0 32 := by
  unfold outputWordsMem
  exact outputWordsMem7_read1312_32_extract hmem


end Blake2f
