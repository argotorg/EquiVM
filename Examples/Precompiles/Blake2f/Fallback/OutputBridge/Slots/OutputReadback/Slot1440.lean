import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.OutputReadback.Slot1408

/-!
# BLAKE2F fallback output-buffer readback at 1440
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem7_read1440_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem7 mem).readWithPadding 1440 32 =
      (UInt256.toByteArray (outputWord7 (outputWordsMem6 mem))).extract 0 32 := by
  unfold outputWordsMem7 outputWord7Mem
  exact toByteArray_write_read_self_extract32 (outputWord7 (outputWordsMem6 mem))
    (outputWordsMem6 mem) 1440
    (by rw [outputWordsMem6_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem_read1440_32_extract {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).readWithPadding 1440 32 =
      (UInt256.toByteArray (outputWord7 (outputWordsMem6 mem))).extract 0 32 := by
  unfold outputWordsMem
  exact outputWordsMem7_read1440_32_extract hmem

end Blake2f
