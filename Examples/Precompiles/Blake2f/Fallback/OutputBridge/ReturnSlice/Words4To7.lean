import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ReturnSlice.Words0To3

/-!
# BLAKE2F fallback return-slice word readback lemmas, words 4 through 7
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem returnLoopWord4Mem_read2048_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord4Mem I mem).readWithPadding 2048 8 =
      returnWordBytes (returnLoopWord4 I mem) := by
  unfold returnLoopWord4Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord4 I mem)).write 0
      (returnLoopWord3Mem I mem) 2048 32).readWithPadding (2048 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord4 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord4 I mem)
    (returnLoopWord3Mem I mem) 2048 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord3Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord4Mem_read2016_32
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord4Mem I mem).readWithPadding 2016 32 =
      (returnLoopWord3Mem I mem).readWithPadding 2016 32 := by
  unfold returnLoopWord4Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord4 I mem) (returnLoopWord3Mem I mem) 2048 2016 32]
  · decide
  · decide
  · decide
  · rw [returnLoopWord3Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord4Mem_read2016_40
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord4Mem I mem).readWithPadding 2016 40 =
      (returnLoopWord3Mem I mem).readWithPadding 2016 32 ++
        returnWordBytes (returnLoopWord4 I mem) := by
  change (returnLoopWord4Mem I mem).readWithPadding 2016 (32 + 8) =
    (returnLoopWord3Mem I mem).readWithPadding 2016 32 ++
      returnWordBytes (returnLoopWord4 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord4Mem_read2016_32 I hlen hmem,
      show 2016 + 32 = 2048 by decide,
      returnLoopWord4Mem_read2048_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord4Mem_size I hlen hmem]
    decide

theorem returnLoopWord5Mem_read2056_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord5Mem I mem).readWithPadding 2056 8 =
      returnWordBytes (returnLoopWord5 I mem) := by
  unfold returnLoopWord5Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord5 I mem)).write 0
      (returnLoopWord4Mem I mem) 2056 32).readWithPadding (2056 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord5 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord5 I mem)
    (returnLoopWord4Mem I mem) 2056 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord4Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord5Mem_read2016_40
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord5Mem I mem).readWithPadding 2016 40 =
      (returnLoopWord4Mem I mem).readWithPadding 2016 40 := by
  unfold returnLoopWord5Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord5 I mem) (returnLoopWord4Mem I mem) 2056 2016 40]
  · decide
  · decide
  · decide
  · rw [returnLoopWord4Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord5Mem_read2016_48
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord5Mem I mem).readWithPadding 2016 48 =
      (returnLoopWord4Mem I mem).readWithPadding 2016 40 ++
        returnWordBytes (returnLoopWord5 I mem) := by
  change (returnLoopWord5Mem I mem).readWithPadding 2016 (40 + 8) =
    (returnLoopWord4Mem I mem).readWithPadding 2016 40 ++
      returnWordBytes (returnLoopWord5 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord5Mem_read2016_40 I hlen hmem,
      show 2016 + 40 = 2056 by decide,
      returnLoopWord5Mem_read2056_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord5Mem_size I hlen hmem]
    decide

theorem returnLoopWord6Mem_read2064_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord6Mem I mem).readWithPadding 2064 8 =
      returnWordBytes (returnLoopWord6 I mem) := by
  unfold returnLoopWord6Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord6 I mem)).write 0
      (returnLoopWord5Mem I mem) 2064 32).readWithPadding (2064 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord6 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord6 I mem)
    (returnLoopWord5Mem I mem) 2064 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord5Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord6Mem_read2016_48
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord6Mem I mem).readWithPadding 2016 48 =
      (returnLoopWord5Mem I mem).readWithPadding 2016 48 := by
  unfold returnLoopWord6Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord6 I mem) (returnLoopWord5Mem I mem) 2064 2016 48]
  · decide
  · decide
  · decide
  · rw [returnLoopWord5Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord6Mem_read2016_56
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord6Mem I mem).readWithPadding 2016 56 =
      (returnLoopWord5Mem I mem).readWithPadding 2016 48 ++
        returnWordBytes (returnLoopWord6 I mem) := by
  change (returnLoopWord6Mem I mem).readWithPadding 2016 (48 + 8) =
    (returnLoopWord5Mem I mem).readWithPadding 2016 48 ++
      returnWordBytes (returnLoopWord6 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord6Mem_read2016_48 I hlen hmem,
      show 2016 + 48 = 2064 by decide,
      returnLoopWord6Mem_read2064_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord6Mem_size I hlen hmem]
    decide

theorem returnLoopWord7Mem_read2072_8
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).readWithPadding 2072 8 =
      returnWordBytes (returnLoopWord7 I mem) := by
  unfold returnLoopWord7Mem returnWordBytes
  change ((UInt256.toByteArray (returnLoopWord7 I mem)).write 0
      (returnLoopWord6Mem I mem) 2072 32).readWithPadding (2072 + 0) 8 =
    (UInt256.toByteArray (returnLoopWord7 I mem)).extract 0 (0 + 8)
  exact toByteArray_write_read_window_of_gap (returnLoopWord7 I mem)
    (returnLoopWord6Mem I mem) 2072 0 8
    (by decide) (by decide) (by decide)
    (by
      rw [returnLoopWord6Mem_size I hlen hmem]
      change 0 < USize.size
      exact lt_usize 0 (by norm_num))

theorem returnLoopWord7Mem_read2016_56
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).readWithPadding 2016 56 =
      (returnLoopWord6Mem I mem).readWithPadding 2016 56 := by
  unfold returnLoopWord7Mem
  rw [toByteArray_write_read_below_len_padded_of_gap
    (returnLoopWord7 I mem) (returnLoopWord6Mem I mem) 2072 2016 56]
  · decide
  · decide
  · decide
  · rw [returnLoopWord6Mem_size I hlen hmem]
    change 0 < USize.size
    exact lt_usize 0 (by norm_num)

theorem returnLoopWord7Mem_read2016_64
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).readWithPadding 2016 64 =
      (returnLoopWord6Mem I mem).readWithPadding 2016 56 ++
        returnWordBytes (returnLoopWord7 I mem) := by
  change (returnLoopWord7Mem I mem).readWithPadding 2016 (56 + 8) =
    (returnLoopWord6Mem I mem).readWithPadding 2016 56 ++
      returnWordBytes (returnLoopWord7 I mem)
  rw [byteArray_readWithPadding_split]
  · rw [returnLoopWord7Mem_read2016_56 I hlen hmem,
      show 2016 + 56 = 2072 by decide,
      returnLoopWord7Mem_read2072_8 I hlen hmem]
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [returnLoopWord7Mem_size I hlen hmem]
    decide

theorem returnLoopWord7Mem_read2016_64_flat
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).readWithPadding 2016 64 =
      returnWordBytes (returnLoopWord0 I mem) ++
      returnWordBytes (returnLoopWord1 I mem) ++
      returnWordBytes (returnLoopWord2 I mem) ++
      returnWordBytes (returnLoopWord3 I mem) ++
      returnWordBytes (returnLoopWord4 I mem) ++
      returnWordBytes (returnLoopWord5 I mem) ++
      returnWordBytes (returnLoopWord6 I mem) ++
      returnWordBytes (returnLoopWord7 I mem) := by
  rw [returnLoopWord7Mem_read2016_64 I hlen hmem,
    returnLoopWord6Mem_read2016_56 I hlen hmem,
    returnLoopWord5Mem_read2016_48 I hlen hmem,
    returnLoopWord4Mem_read2016_40 I hlen hmem,
    returnLoopWord3Mem_read2016_32 I hlen hmem,
    returnLoopWord2Mem_read2016_24 I hlen hmem,
    returnLoopWord1Mem_read2016_16 I hlen hmem]


end Blake2f
