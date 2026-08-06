import Examples.Precompiles.Blake2f.Fallback.OutputBridge.Slots.OutputReadback

/-!
# BLAKE2F fallback output-buffer bridge: return-loop readback

Facts connecting the Solidity return-buffer copy loop to the populated output-word slots.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem returnAllocMem_read1216_32 {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (returnAllocMem mem).readWithPadding 1216 32 =
      mem.readWithPadding 1216 32 := by
  unfold returnAllocMem
  exact write32_read_above (UInt256.toByteArray (UInt256.ofNat 2080)) mem 64 1216
    (by rw [toByteArray_size])
    (by rw [hmem]; decide)
    (by decide)
    (by rw [hmem]; decide)

theorem returnLengthMem_read1216_32 {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (returnLengthMem mem).readWithPadding 1216 32 =
      mem.readWithPadding 1216 32 := by
  unfold returnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (UInt256.ofNat 64) (returnAllocMem mem) 1984 1216
    (by rw [returnAllocMem_size hmem]; decide)
    (by decide)
    (by rw [returnAllocMem_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnAllocMem_read1216_32 hmem

theorem returnAllocMem_read_outputSlot {mem : ByteArray} {read : Nat}
    (hmem : mem.size = 1984) (habove : 96 ≤ read) (hin : read + 32 ≤ 1984) :
    (returnAllocMem mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold returnAllocMem
  exact write32_read_above (UInt256.toByteArray (UInt256.ofNat 2080)) mem 64 read
    (by rw [toByteArray_size])
    (by rw [hmem]; decide)
    (by omega)
    (by rw [hmem]; omega)

theorem returnLengthMem_read_outputSlot {mem : ByteArray} {read : Nat}
    (hmem : mem.size = 1984) (habove : 96 ≤ read) (hin : read + 32 ≤ 1984) :
    (returnLengthMem mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold returnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (UInt256.ofNat 64) (returnAllocMem mem) 1984 read
    (by rw [returnAllocMem_size hmem]; exact hin)
    (by omega)
    (by rw [returnAllocMem_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnAllocMem_read_outputSlot hmem habove hin

theorem returnZeroPadMem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray} {read : Nat}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hin : read + 32 ≤ 1984) :
    (returnZeroPadMem I mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hbase : (returnLengthMem mem).size = 2016 := returnLengthMem_size hmem
  unfold returnZeroPadMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hbase]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (returnLengthMem mem) 2016 0).readWithPadding
      read 32 = mem.readWithPadding read 32
  rw [copySlice_read_below_gen]
  · exact returnLengthMem_read_outputSlot hmem habove hin
  · omega
  · rw [hbase]
    omega
  · decide
  · decide

theorem returnZeroPadMem_read1216_32
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnZeroPadMem I mem).readWithPadding 1216 32 =
      mem.readWithPadding 1216 32 :=
  returnZeroPadMem_read_outputSlot I hlen hmem (by decide) (by decide)

theorem returnLoopLoadWord0_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord0 I (outputWordsMem mem) = outputWord0 mem := by
  unfold returnLoopLoadWord0
  rw [returnZeroPadMem_read1216_32 I hlen (outputWordsMem_size hmem),
    outputWordsMem_read1216_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopWord0Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord0Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord0Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord0 I (outputWordsMem mem)) (returnZeroPadMem I (outputWordsMem mem)) 2016 read
    (by rw [returnZeroPadMem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnZeroPadMem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnZeroPadMem_read_outputSlot I hlen (outputWordsMem_size hmem) habove hread

theorem returnLoopWord1Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord1Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord1Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord1 I (outputWordsMem mem)) (returnLoopWord0Mem I (outputWordsMem mem)) 2024 read
    (by rw [returnLoopWord0Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord0Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord0Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopWord2Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord2Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord2Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord2 I (outputWordsMem mem)) (returnLoopWord1Mem I (outputWordsMem mem)) 2032 read
    (by rw [returnLoopWord1Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord1Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord1Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopWord3Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord3Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord3Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord3 I (outputWordsMem mem)) (returnLoopWord2Mem I (outputWordsMem mem)) 2040 read
    (by rw [returnLoopWord2Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord2Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord2Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopWord4Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord4Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord4Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord4 I (outputWordsMem mem)) (returnLoopWord3Mem I (outputWordsMem mem)) 2048 read
    (by rw [returnLoopWord3Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord3Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord3Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopWord5Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord5Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord5Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord5 I (outputWordsMem mem)) (returnLoopWord4Mem I (outputWordsMem mem)) 2056 read
    (by rw [returnLoopWord4Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord4Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord4Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopWord6Mem_read_outputSlot
    (I : ExecutionEnv) {mem : ByteArray}
    {read : Nat} (hlen : I.calldata.size = 213) (hmem : mem.size = 1984)
    (habove : 96 ≤ read) (hread : read + 32 ≤ 1984) :
    (returnLoopWord6Mem I (outputWordsMem mem)).readWithPadding read 32 =
      (outputWordsMem mem).readWithPadding read 32 := by
  unfold returnLoopWord6Mem
  rw [toByteArray_write_read_below_of_gap
    (returnLoopWord6 I (outputWordsMem mem)) (returnLoopWord5Mem I (outputWordsMem mem)) 2064 read
    (by rw [returnLoopWord5Mem_size I hlen (outputWordsMem_size hmem)]; omega)
    (by omega)
    (by rw [returnLoopWord5Mem_size I hlen (outputWordsMem_size hmem)]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact returnLoopWord5Mem_read_outputSlot I hlen hmem habove hread

theorem returnLoopLoadWord1_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord1 I (outputWordsMem mem) = outputWord1 (outputWordsMem0 mem) := by
  unfold returnLoopLoadWord1
  rw [returnLoopWord0Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1248) (by decide : 1248 + 32 ≤ 1984),
    outputWordsMem_read1248_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord2_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord2 I (outputWordsMem mem) = outputWord2 (outputWordsMem1 mem) := by
  unfold returnLoopLoadWord2
  rw [returnLoopWord1Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1280) (by decide : 1280 + 32 ≤ 1984),
    outputWordsMem_read1280_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord3_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord3 I (outputWordsMem mem) = outputWord3 (outputWordsMem2 mem) := by
  unfold returnLoopLoadWord3
  rw [returnLoopWord2Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1312) (by decide : 1312 + 32 ≤ 1984),
    outputWordsMem_read1312_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord4_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord4 I (outputWordsMem mem) = outputWord4 (outputWordsMem3 mem) := by
  unfold returnLoopLoadWord4
  rw [returnLoopWord3Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1344) (by decide : 1344 + 32 ≤ 1984),
    outputWordsMem_read1344_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord5_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord5 I (outputWordsMem mem) = outputWord5 (outputWordsMem4 mem) := by
  unfold returnLoopLoadWord5
  rw [returnLoopWord4Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1376) (by decide : 1376 + 32 ≤ 1984),
    outputWordsMem_read1376_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord6_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord6 I (outputWordsMem mem) = outputWord6 (outputWordsMem5 mem) := by
  unfold returnLoopLoadWord6
  rw [returnLoopWord5Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1408) (by decide : 1408 + 32 ≤ 1984),
    outputWordsMem_read1408_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

theorem returnLoopLoadWord7_outputWordsMem
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    returnLoopLoadWord7 I (outputWordsMem mem) = outputWord7 (outputWordsMem6 mem) := by
  unfold returnLoopLoadWord7
  rw [returnLoopWord6Mem_read_outputSlot I hlen hmem (by decide : 96 ≤ 1440) (by decide : 1440 + 32 ≤ 1984),
    outputWordsMem_read1440_32_extract hmem,
    fromByteArrayBigEndian_toByteArray_extract0_32,
    u256_ofNat_toNat]

end Blake2f
