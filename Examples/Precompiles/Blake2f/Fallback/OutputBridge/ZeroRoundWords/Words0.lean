import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Common

/-!
# BLAKE2F zero-round output-word bridge: word 0

This file contains only the readback/output proof for zero-round output word 0.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v13MixedMem_read384_eq_compressionVAllocMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 384 32 =
      (compressionVAllocMem I).readWithPadding 384 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 384
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 384
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I)
    1952 384 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I)
    1920 384 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I)
    1888 384 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I)
    1856 384 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I)
    1824 384 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I)
    1792 384 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I)
    1760 384 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I)
    1728 384 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 384
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 384
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 384
    (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 384
    (by rw [v3InitMem_size I hlen]; decide) (by decide)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I) (v2InitMem I) 1568 384
    (by rw [v2InitMem_size I hlen]; decide) (by decide)
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_of_gap (v2StoredWord I) (v1InitMem I) 1536 384
    (by rw [v1InitMem_size I hlen]; decide) (by decide)
    (by rw [v1InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v1InitMem]
  rw [toByteArray_write_read_below_of_gap (v1StoredWord I) (v0InitMem I) 1504 384
    (by rw [v0InitMem_size I hlen]; decide) (by decide)
    (by rw [v0InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v0InitMem]
  rw [toByteArray_write_read_below_of_gap (v0StoredWord I) (compressionVAllocMem I) 1472 384
    (by rw [compressionVAllocMem_size I hlen]; decide) (by decide)
    (by rw [compressionVAllocMem_size I hlen]; change 256 < USize.size; exact lt_usize 256 (by norm_num))]

theorem outputH0LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH0LoadWord (v13MixedMem I) = v0LoadWord I := by
  unfold outputH0LoadWord v0LoadWord
  rw [v13MixedMem_read384_eq_compressionVAllocMem I hlen]


theorem v13MixedMem_read1472_eq_v0StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1472 32 =
      (UInt256.toByteArray (v0StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1472
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1472
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1472
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1472
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1472
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1472
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1472
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1472
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1472
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 1472
    (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1472
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 1472
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 1472
    (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 1472
    (by rw [v3InitMem_size I hlen]; decide) (by decide)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I) (v2InitMem I) 1568 1472
    (by rw [v2InitMem_size I hlen]; decide) (by decide)
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_of_gap (v2StoredWord I) (v1InitMem I) 1536 1472
    (by rw [v1InitMem_size I hlen]; decide) (by decide)
    (by rw [v1InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v1InitMem]
  rw [toByteArray_write_read_below_of_gap (v1StoredWord I) (v0InitMem I) 1504 1472
    (by rw [v0InitMem_size I hlen]) (by decide)
    (by rw [v0InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v0InitMem]
  exact toByteArray_write_read_self_extract32 (v0StoredWord I) (compressionVAllocMem I) 1472
    (by rw [compressionVAllocMem_size I hlen]; change 256 < USize.size; exact lt_usize 256 (by norm_num))

theorem outputV0LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV0LoadWord (v13MixedMem I) = v0StoredWord I := by
  unfold outputV0LoadWord
  rw [v13MixedMem_read1472_eq_v0StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v0StoredWord I)

theorem v13MixedMem_read1728_eq_iv0
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1728 32 =
      (UInt256.toByteArray (UInt256.ofNat 7640891576956012808)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1728
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1728
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1728
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1728
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1728
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1728
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1728
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1728
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1728
    (by rw [v8InitMem_size I hlen]) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV8LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV8LoadWord (v13MixedMem I) = UInt256.ofNat 7640891576956012808 := by
  unfold outputV8LoadWord
  rw [v13MixedMem_read1728_eq_iv0 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 7640891576956012808)

theorem outputWord0_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord0 (v13MixedMem I) = UInt256.ofNat 7640891576956012808 := by
  unfold outputWord0
  rw [outputH0LoadWord_v13MixedMem I hlen, outputV0LoadWord_v13MixedMem I hlen,
    outputV8LoadWord_v13MixedMem I hlen]
  unfold v0StoredWord
  rw [outputWord_xor_cancel]
  native_decide

end Blake2f
