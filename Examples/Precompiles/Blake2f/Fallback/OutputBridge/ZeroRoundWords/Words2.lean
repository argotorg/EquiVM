import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Common

/-!
# BLAKE2F zero-round output-word bridge: word 2

This file contains only the readback/output proof for zero-round output word 2.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v13MixedMem_read448_eq_v1InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 448 32 =
      (v1InitMem I).readWithPadding 448 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 448
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 448
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 448
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 448
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 448
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 448
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 448
    (by have hs := v10InitMem_size I hlen; omega) (by omega)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 448
    (by have hs := v9InitMem_size I hlen; omega) (by omega)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 448
    (by have hs := v8InitMem_size I hlen; omega) (by omega)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 448
    (by have hs := v7InitMem_size I hlen; omega) (by omega)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 448
    (by have hs := v6InitMem_size I hlen; omega) (by omega)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 448
    (by have hs := v5InitMem_size I hlen; omega) (by omega)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 448
    (by have hs := v4InitMem_size I hlen; omega) (by omega)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 448
    (by have hs := v3InitMem_size I hlen; omega) (by omega)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I) (v2InitMem I) 1568 448
    (by have hs := v2InitMem_size I hlen; omega) (by omega)
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_of_gap (v2StoredWord I) (v1InitMem I) 1536 448
    (by have hs := v1InitMem_size I hlen; omega) (by omega)
    (by rw [v1InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]


theorem outputH2LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH2LoadWord (v13MixedMem I) = v2LoadWord I := by
  unfold outputH2LoadWord v2LoadWord
  rw [v13MixedMem_read448_eq_v1InitMem I hlen]

theorem v13MixedMem_read1536_eq_v2StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1536 32 =
      (UInt256.toByteArray (v2StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1536
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1536
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1536
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1536
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1536
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1536
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1536
    (by have hs := v10InitMem_size I hlen; omega) (by omega)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1536
    (by have hs := v9InitMem_size I hlen; omega) (by omega)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1536
    (by have hs := v8InitMem_size I hlen; omega) (by omega)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 1536
    (by have hs := v7InitMem_size I hlen; omega) (by omega)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1536
    (by have hs := v6InitMem_size I hlen; omega) (by omega)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 1536
    (by have hs := v5InitMem_size I hlen; omega) (by omega)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 1536
    (by have hs := v4InitMem_size I hlen; omega) (by omega)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 1536
    (by have hs := v3InitMem_size I hlen; omega) (by omega)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I) (v2InitMem I) 1568 1536
    (by have hs := v2InitMem_size I hlen; omega) (by omega)
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  exact toByteArray_write_read_self_extract32 (v2StoredWord I) (v1InitMem I) 1536
    (by rw [v1InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV2LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV2LoadWord (v13MixedMem I) = v2StoredWord I := by
  unfold outputV2LoadWord
  rw [v13MixedMem_read1536_eq_v2StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v2StoredWord I)

theorem v13MixedMem_read1792_eq_iv2
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1792 32 =
      (UInt256.toByteArray (UInt256.ofNat 4354685564936845355)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1792
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1792
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1792
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1792
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1792
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1792
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1792
    (by have hs := v10InitMem_size I hlen; omega) (by omega)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV10LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV10LoadWord (v13MixedMem I) = UInt256.ofNat 4354685564936845355 := by
  unfold outputV10LoadWord
  rw [v13MixedMem_read1792_eq_iv2 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 4354685564936845355)

theorem outputWord2_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord2 (v13MixedMem I) = UInt256.ofNat 4354685564936845355 := by
  unfold outputWord2
  rw [outputH2LoadWord_v13MixedMem I hlen, outputV2LoadWord_v13MixedMem I hlen,
    outputV10LoadWord_v13MixedMem I hlen]
  unfold v2StoredWord
  rw [outputWord_xor_cancel]
  native_decide

end Blake2f
