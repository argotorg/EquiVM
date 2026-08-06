import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.Core

/-!
# BLAKE2F fallback output-buffer readback at 1216
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem0_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem0 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem0 outputWord0Mem
  change ((UInt256.toByteArray (outputWord0 mem)).write 0 mem 1216 32).readWithPadding
      (1216 + 0) 32 =
    (UInt256.toByteArray (outputWord0 mem)).extract 0 (0 + 32)
  exact toByteArray_write_read_window_of_gap (outputWord0 mem) mem 1216 0 32
    (by decide) (by decide) (by decide)
    (by
      rw [hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem outputWordsMem1_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem1 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem1 outputWord1Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord1 (outputWordsMem0 mem)) (outputWordsMem0 mem) 1248 1216
    (by rw [outputWordsMem0_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem0_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem0_read1216_32_extract hmem

theorem outputWordsMem2_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem2 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem2 outputWord2Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord2 (outputWordsMem1 mem)) (outputWordsMem1 mem) 1280 1216
    (by rw [outputWordsMem1_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem1_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem1_read1216_32_extract hmem

theorem outputWordsMem3_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem3 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem3 outputWord3Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord3 (outputWordsMem2 mem)) (outputWordsMem2 mem) 1312 1216
    (by rw [outputWordsMem2_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem2_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem2_read1216_32_extract hmem

theorem outputWordsMem4_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem4 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem4 outputWord4Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord4 (outputWordsMem3 mem)) (outputWordsMem3 mem) 1344 1216
    (by rw [outputWordsMem3_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem3_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem3_read1216_32_extract hmem

theorem outputWordsMem5_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem5 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem5 outputWord5Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord5 (outputWordsMem4 mem)) (outputWordsMem4 mem) 1376 1216
    (by rw [outputWordsMem4_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem4_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem4_read1216_32_extract hmem

theorem outputWordsMem6_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem6 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem6 outputWord6Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord6 (outputWordsMem5 mem)) (outputWordsMem5 mem) 1408 1216
    (by rw [outputWordsMem5_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem5_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem5_read1216_32_extract hmem

theorem outputWordsMem7_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem7 outputWord7Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord7 (outputWordsMem6 mem)) (outputWordsMem6 mem) 1440 1216
    (by rw [outputWordsMem6_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem6_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem6_read1216_32_extract hmem

theorem outputWordsMem_read1216_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).readWithPadding 1216 32 =
      (UInt256.toByteArray (outputWord0 mem)).extract 0 32 := by
  unfold outputWordsMem
  exact outputWordsMem7_read1216_32_extract hmem


end Blake2f
