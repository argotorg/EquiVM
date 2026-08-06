import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.OutputSizes

/-!
# BLAKE2F compression memory lemmas: free-memory-pointer readback
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v15InitMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v15InitMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  rw [v15InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 6620516959819538809)
    (v14InitMem I) 1952 1952 (v14InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v14InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 2270897969802886507)
    (v13InitMem I) 1920 1920 (v13InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v13InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 11170449401992604703)
    (v12InitMem I) 1888 1888 (v12InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v12InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 5840696475078001361)
    (v11InitMem I) 1856 1856 (v11InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v11InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 11912009170470909681)
    (v10InitMem I) 1824 1824 (v10InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v10InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 4354685564936845355)
    (v9InitMem I) 1792 1792 (v9InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v9InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 13503953896175478587)
    (v8InitMem I) 1760 1760 (v8InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v8InitMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 7640891576956012808)
    (v7InitMem I) 1728 1728 (v7InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v7InitMem]
  rw [toByteArray_write_preserves_read64_gap (v7StoredWord I)
    (v6InitMem I) 1696 1696 (v6InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_preserves_read64_gap (v6StoredWord I)
    (v5InitMem I) 1664 1664 (v5InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_preserves_read64_gap (v5StoredWord I)
    (v4InitMem I) 1632 1632 (v4InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_preserves_read64_gap (v4StoredWord I)
    (v3InitMem I) 1600 1600 (v3InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_preserves_read64_gap (v3StoredWord I)
    (v2InitMem I) 1568 1568 (v2InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  rw [toByteArray_write_preserves_read64_gap (v2StoredWord I)
    (v1InitMem I) 1536 1536 (v1InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v1InitMem]
  rw [toByteArray_write_preserves_read64_gap (v1StoredWord I)
    (v0InitMem I) 1504 1504 (v0InitMem_size I hlen)
    (by decide) (by decide) (by change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v0InitMem]
  rw [toByteArray_write_preserves_read64_gap (v0StoredWord I)
    (compressionVAllocMem I) 1472 1216 (compressionVAllocMem_size I hlen)
    (by decide) (by decide) (by change 256 < USize.size; exact lt_usize 256 (by norm_num))]
  exact compressionVAllocMem_read64 I hlen

theorem v13MixedMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  rw [v13MixedMem]
  rw [toByteArray_write_preserves_read64 (v13MixedWord I)
    (v12MixedMem I) 1888 1984 (v12MixedMem_size I hlen)
    (by decide) (by decide) (by decide)]
  rw [v12MixedMem]
  rw [toByteArray_write_preserves_read64 (v12MixedWord I)
    (v15InitMem I) 1856 1984 (v15InitMem_size I hlen)
    (by decide) (by decide) (by decide)]
  exact v15InitMem_read64 I hlen

theorem v14FinalFlagMem_read64
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_preserves_read64 (UInt256.ofNat 16175846103906665108)
    (v13MixedMem I) 1920 1984 (v13MixedMem_size I hlen)
    (by decide) (by decide) (by decide)]
  exact v13MixedMem_read64 I hlen

theorem outputWord0Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord0Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord0Mem
  rw [toByteArray_write_preserves_read64 (outputWord0 mem) mem 1216 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord1Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord1Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord1Mem
  rw [toByteArray_write_preserves_read64 (outputWord1 mem) mem 1248 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord2Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord2Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord2Mem
  rw [toByteArray_write_preserves_read64 (outputWord2 mem) mem 1280 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord3Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord3Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord3Mem
  rw [toByteArray_write_preserves_read64 (outputWord3 mem) mem 1312 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord4Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord4Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord4Mem
  rw [toByteArray_write_preserves_read64 (outputWord4 mem) mem 1344 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord5Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord5Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord5Mem
  rw [toByteArray_write_preserves_read64 (outputWord5 mem) mem 1376 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord6Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord6Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord6Mem
  rw [toByteArray_write_preserves_read64 (outputWord6 mem) mem 1408 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWord7Mem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWord7Mem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWord7Mem
  rw [toByteArray_write_preserves_read64 (outputWord7 mem) mem 1440 1984 hmem
    (by decide) (by decide) (by decide)]
  exact hread

theorem outputWordsMem_read64 {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)) :
    (outputWordsMem mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 1984) := by
  unfold outputWordsMem
  apply outputWord7Mem_read64
  · exact outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem))))))
  apply outputWord6Mem_read64
  · exact outputWord5Mem_size
      (outputWord4Mem_size
        (outputWord3Mem_size
          (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem)))))
  apply outputWord5Mem_read64
  · exact outputWord4Mem_size
      (outputWord3Mem_size
        (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem))))
  apply outputWord4Mem_read64
  · exact outputWord3Mem_size
      (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem)))
  apply outputWord3Mem_read64
  · exact outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem))
  apply outputWord2Mem_read64
  · exact outputWord1Mem_size (outputWord0Mem_size hmem)
  apply outputWord1Mem_read64
  · exact outputWord0Mem_size hmem
  exact outputWord0Mem_read64 hmem hread

end Blake2f
