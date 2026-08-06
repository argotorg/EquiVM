import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.OutputReadback.Slot1376

/-!
# BLAKE2F fallback output-buffer readback at 1408
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem6_read1408_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem6 mem).readWithPadding 1408 32 =
      (UInt256.toByteArray (outputWord6 (outputWordsMem5 mem))).extract 0 32 := by
  unfold outputWordsMem6 outputWord6Mem
  exact toByteArray_write_read_self_extract32 (outputWord6 (outputWordsMem5 mem))
    (outputWordsMem5 mem) 1408
    (by rw [outputWordsMem5_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem7_read1408_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).readWithPadding 1408 32 =
      (UInt256.toByteArray (outputWord6 (outputWordsMem5 mem))).extract 0 32 := by
  unfold outputWordsMem7 outputWord7Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord7 (outputWordsMem6 mem)) (outputWordsMem6 mem) 1440 1408
    (by rw [outputWordsMem6_size hmem]; decide)
    (by decide)
    (by rw [outputWordsMem6_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem6_read1408_32_extract hmem

theorem outputWordsMem_read1408_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).readWithPadding 1408 32 =
      (UInt256.toByteArray (outputWord6 (outputWordsMem5 mem))).extract 0 32 := by
  unfold outputWordsMem
  exact outputWordsMem7_read1408_32_extract hmem


end Blake2f
