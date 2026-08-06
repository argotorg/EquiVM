import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots

/-!
# BLAKE2F fallback return-slice word readback lemmas, words 0 through 3
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem returnLoopWord0Mem_read2016_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord0Mem I mem).readWithPadding 2016 8 =
      returnWordBytes (returnLoopWord0 I mem) := by
  unfold returnLoopWord0Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord0 I mem)).write 0
      (returnZeroPadMem I mem) 2016 32).readWithPadding (2016 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord0 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord0 I mem)
    (returnZeroPadMem I mem) 2016 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnZeroPadMem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord1Mem_read2024_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord1Mem I mem).readWithPadding 2024 8 =
      returnWordBytes (returnLoopWord1 I mem) := by
  unfold returnLoopWord1Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord1 I mem)).write 0
      (returnLoopWord0Mem I mem) 2024 32).readWithPadding (2024 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord1 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord1 I mem)
    (returnLoopWord0Mem I mem) 2024 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord0Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord1Mem_read2016_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord1Mem I mem).readWithPadding 2016 8 =
      returnWordBytes (returnLoopWord0 I mem) := by
  unfold returnLoopWord1Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord1 I mem) (returnLoopWord0Mem I mem) 2024 2016 8]
  · exact returnLoopWord0Mem_read2016_8 I hlen hmem
  · decide
  · decide
  · decide
  · rw [returnLoopWord0Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord1Mem_read2016_16
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord1Mem I mem).readWithPadding 2016 16 =
      returnWordBytes (returnLoopWord0 I mem) ++ returnWordBytes (returnLoopWord1 I mem) := by
  change (returnLoopWord1Mem I mem).readWithPadding 2016 (8 + 8) =
    returnWordBytes (returnLoopWord0 I mem) ++ returnWordBytes (returnLoopWord1 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord1Mem_read2016_8 I hlen hmem,
      show 2016 + 8 = 2024 by decide,
      returnLoopWord1Mem_read2024_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord1Mem_size I hlen hmem]
    decide

theorem returnLoopWord2Mem_read2032_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord2Mem I mem).readWithPadding 2032 8 =
      returnWordBytes (returnLoopWord2 I mem) := by
  unfold returnLoopWord2Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord2 I mem)).write 0
      (returnLoopWord1Mem I mem) 2032 32).readWithPadding (2032 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord2 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord2 I mem)
    (returnLoopWord1Mem I mem) 2032 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord1Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord2Mem_read2016_16
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord2Mem I mem).readWithPadding 2016 16 =
      (returnLoopWord1Mem I mem).readWithPadding 2016 16 := by
  unfold returnLoopWord2Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord2 I mem) (returnLoopWord1Mem I mem) 2032 2016 16]
  · decide
  · decide
  · decide
  · rw [returnLoopWord1Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord2Mem_read2016_24
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord2Mem I mem).readWithPadding 2016 24 =
      (returnLoopWord1Mem I mem).readWithPadding 2016 16 ++
        returnWordBytes (returnLoopWord2 I mem) := by
  change (returnLoopWord2Mem I mem).readWithPadding 2016 (16 + 8) =
    (returnLoopWord1Mem I mem).readWithPadding 2016 16 ++
      returnWordBytes (returnLoopWord2 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord2Mem_read2016_16 I hlen hmem,
      show 2016 + 16 = 2032 by decide,
      returnLoopWord2Mem_read2032_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord2Mem_size I hlen hmem]
    decide

theorem returnLoopWord3Mem_read2040_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord3Mem I mem).readWithPadding 2040 8 =
      returnWordBytes (returnLoopWord3 I mem) := by
  unfold returnLoopWord3Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord3 I mem)).write 0
      (returnLoopWord2Mem I mem) 2040 32).readWithPadding (2040 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord3 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord3 I mem)
    (returnLoopWord2Mem I mem) 2040 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord2Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord3Mem_read2016_24
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord3Mem I mem).readWithPadding 2016 24 =
      (returnLoopWord2Mem I mem).readWithPadding 2016 24 := by
  unfold returnLoopWord3Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord3 I mem) (returnLoopWord2Mem I mem) 2040 2016 24]
  · decide
  · decide
  · decide
  · rw [returnLoopWord2Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord3Mem_read2016_32
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord3Mem I mem).readWithPadding 2016 32 =
      (returnLoopWord2Mem I mem).readWithPadding 2016 24 ++
        returnWordBytes (returnLoopWord3 I mem) := by
  change (returnLoopWord3Mem I mem).readWithPadding 2016 (24 + 8) =
    (returnLoopWord2Mem I mem).readWithPadding 2016 24 ++
      returnWordBytes (returnLoopWord3 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord3Mem_read2016_24 I hlen hmem,
      show 2016 + 24 = 2040 by decide,
      returnLoopWord3Mem_read2040_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord3Mem_size I hlen hmem]
    decide


end Blake2f
