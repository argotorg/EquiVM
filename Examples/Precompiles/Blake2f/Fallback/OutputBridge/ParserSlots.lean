import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ByteOrder

/-!
# BLAKE2F zero-round parser-slot bridge facts

These lemmas identify the two `t` words after the bytecode setup memory has been rebuilt for the
compression loop.  They are intentionally kept local to the Blake2f example: the proof is specific
to the Solidity-compiled memory layout used by this bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem usize_pos0 : 0 < USize.size :=
  lt_usize 0 (by norm_num)

private theorem usize_pos256 : 256 < USize.size :=
  lt_usize 256 (by norm_num)

theorem v15InitMem_read1152
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v15InitMem I).readWithPadding 1152 32 = UInt256.toByteArray (t0ParsedWord I) := by
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809)
    (v14InitMem I) 1952 1152 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; exact usize_pos0)]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507)
    (v13InitMem I) 1920 1152 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; exact usize_pos0)]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703)
    (v12InitMem I) 1888 1152 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; exact usize_pos0)]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361)
    (v11InitMem I) 1856 1152 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; exact usize_pos0)]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681)
    (v10InitMem I) 1824 1152 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; exact usize_pos0)]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355)
    (v9InitMem I) 1792 1152 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; exact usize_pos0)]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587)
    (v8InitMem I) 1760 1152 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; exact usize_pos0)]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808)
    (v7InitMem I) 1728 1152 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; exact usize_pos0)]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I)
    (v6InitMem I) 1696 1152 (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; exact usize_pos0)]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I)
    (v5InitMem I) 1664 1152 (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; exact usize_pos0)]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I)
    (v4InitMem I) 1632 1152 (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; exact usize_pos0)]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I)
    (v3InitMem I) 1600 1152 (by rw [v3InitMem_size I hlen]; decide) (by decide)
    (by rw [v3InitMem_size I hlen]; exact usize_pos0)]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I)
    (v2InitMem I) 1568 1152 (by rw [v2InitMem_size I hlen]; decide) (by decide)
    (by rw [v2InitMem_size I hlen]; exact usize_pos0)]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_of_gap (v2StoredWord I)
    (v1InitMem I) 1536 1152 (by rw [v1InitMem_size I hlen]; decide) (by decide)
    (by rw [v1InitMem_size I hlen]; exact usize_pos0)]
  rw [v1InitMem]
  rw [toByteArray_write_read_below_of_gap (v1StoredWord I)
    (v0InitMem I) 1504 1152 (by rw [v0InitMem_size I hlen]; decide) (by decide)
    (by rw [v0InitMem_size I hlen]; exact usize_pos0)]
  rw [v0InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v0StoredWord I)
    (compressionVAllocMem I) 1472 1152 32 (by decide) (by decide) (by decide)
    (by rw [compressionVAllocMem_size I hlen]; exact usize_pos256)]
  unfold compressionVAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1984))
    (compressionScratchZeroMem I) 64 1152 32 (by rw [toByteArray_size])
    (by rw [compressionScratchZeroMem_size I hlen]; decide) (by decide)
    (by rw [compressionScratchZeroMem_size I hlen]; decide) (by decide) (by decide)]
  have hsize : (compressionScratchAllocMem I).size = 1216 := compressionScratchAllocMem_size I hlen
  unfold compressionScratchZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (compressionScratchAllocMem I) 1216 0).readWithPadding
    1152 32 = UInt256.toByteArray (t0ParsedWord I)
  rw [copySlice_read_below_gen]
  · unfold compressionScratchAllocMem
    rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1472))
      (t1StoredMem I) 64 1152 32 (by rw [toByteArray_size])
      (by rw [t1StoredMem_size I hlen]; decide) (by decide)
      (by rw [t1StoredMem_size I hlen]; decide) (by decide) (by decide)]
    rw [t1StoredMem]
    rw [toByteArray_write_read_below_of_gap (t1ParsedWord I) (t0StoredMem I) 1184 1152
      (by rw [t0StoredMem_size I hlen]) (by decide)
      (by rw [t0StoredMem_size I hlen]; exact usize_pos0)]
    unfold t0StoredMem
    exact toByteArray_write_read_back_of_gap (t0ParsedWord I) (m15StoredMem I) 1152
      (by rw [m15StoredMem_size I hlen]; exact usize_pos0)
  · decide
  · rw [hsize]; decide
  · decide
  · decide

theorem v15InitMem_read1184
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v15InitMem I).readWithPadding 1184 32 = UInt256.toByteArray (t1ParsedWord I) := by
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809)
    (v14InitMem I) 1952 1184 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; exact usize_pos0)]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507)
    (v13InitMem I) 1920 1184 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; exact usize_pos0)]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703)
    (v12InitMem I) 1888 1184 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; exact usize_pos0)]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361)
    (v11InitMem I) 1856 1184 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; exact usize_pos0)]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681)
    (v10InitMem I) 1824 1184 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; exact usize_pos0)]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355)
    (v9InitMem I) 1792 1184 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; exact usize_pos0)]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587)
    (v8InitMem I) 1760 1184 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; exact usize_pos0)]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808)
    (v7InitMem I) 1728 1184 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; exact usize_pos0)]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I)
    (v6InitMem I) 1696 1184 (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; exact usize_pos0)]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I)
    (v5InitMem I) 1664 1184 (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; exact usize_pos0)]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I)
    (v4InitMem I) 1632 1184 (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; exact usize_pos0)]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I)
    (v3InitMem I) 1600 1184 (by rw [v3InitMem_size I hlen]; decide) (by decide)
    (by rw [v3InitMem_size I hlen]; exact usize_pos0)]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I)
    (v2InitMem I) 1568 1184 (by rw [v2InitMem_size I hlen]; decide) (by decide)
    (by rw [v2InitMem_size I hlen]; exact usize_pos0)]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_of_gap (v2StoredWord I)
    (v1InitMem I) 1536 1184 (by rw [v1InitMem_size I hlen]; decide) (by decide)
    (by rw [v1InitMem_size I hlen]; exact usize_pos0)]
  rw [v1InitMem]
  rw [toByteArray_write_read_below_of_gap (v1StoredWord I)
    (v0InitMem I) 1504 1184 (by rw [v0InitMem_size I hlen]; decide) (by decide)
    (by rw [v0InitMem_size I hlen]; exact usize_pos0)]
  rw [v0InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v0StoredWord I)
    (compressionVAllocMem I) 1472 1184 32 (by decide) (by decide) (by decide)
    (by rw [compressionVAllocMem_size I hlen]; exact usize_pos256)]
  unfold compressionVAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1984))
    (compressionScratchZeroMem I) 64 1184 32 (by rw [toByteArray_size])
    (by rw [compressionScratchZeroMem_size I hlen]; decide) (by decide)
    (by rw [compressionScratchZeroMem_size I hlen]) (by decide) (by decide)]
  have hsize : (compressionScratchAllocMem I).size = 1216 := compressionScratchAllocMem_size I hlen
  unfold compressionScratchZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (compressionScratchAllocMem I) 1216 0).readWithPadding
    1184 32 = UInt256.toByteArray (t1ParsedWord I)
  rw [copySlice_read_below_gen]
  · unfold compressionScratchAllocMem
    rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1472))
      (t1StoredMem I) 64 1184 32 (by rw [toByteArray_size])
      (by rw [t1StoredMem_size I hlen]; decide) (by decide)
      (by rw [t1StoredMem_size I hlen]) (by decide) (by decide)]
    unfold t1StoredMem
    exact toByteArray_write_read_back_of_gap (t1ParsedWord I) (t0StoredMem I) 1184
      (by rw [t0StoredMem_size I hlen]; exact usize_pos0)
  · decide
  · rw [hsize]
  · decide
  · decide

end Blake2f
