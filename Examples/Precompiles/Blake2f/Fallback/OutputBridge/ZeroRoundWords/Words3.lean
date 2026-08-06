import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Common

/-!
# BLAKE2F zero-round output-word bridge: word 3

This file contains only the readback/output proof for zero-round output word 3.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem v13MixedMem_read480_eq_v2InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 480 32 =
      (v2InitMem I).readWithPadding 480 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 480
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 480
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 480
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 480
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 480
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 480
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 480
    (by have hs := v10InitMem_size I hlen; omega) (by omega)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 480
    (by have hs := v9InitMem_size I hlen; omega) (by omega)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 480
    (by have hs := v8InitMem_size I hlen; omega) (by omega)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 480
    (by have hs := v7InitMem_size I hlen; omega) (by omega)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 480
    (by have hs := v6InitMem_size I hlen; omega) (by omega)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 480
    (by have hs := v5InitMem_size I hlen; omega) (by omega)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 480
    (by have hs := v4InitMem_size I hlen; omega) (by omega)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 480
    (by have hs := v3InitMem_size I hlen; omega) (by omega)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_of_gap (v3StoredWord I) (v2InitMem I) 1568 480
    (by have hs := v2InitMem_size I hlen; omega) (by omega)
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]


theorem outputH3LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH3LoadWord (v13MixedMem I) = v3LoadWord I := by
  unfold outputH3LoadWord v3LoadWord
  rw [v13MixedMem_read480_eq_v2InitMem I hlen]

theorem v13MixedMem_read1568_eq_v3StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1568 32 =
      (UInt256.toByteArray (v3StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1568
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1568
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1568
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1568
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1568
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1568
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1568
    (by have hs := v10InitMem_size I hlen; omega) (by omega)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1568
    (by have hs := v9InitMem_size I hlen; omega) (by omega)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1568
    (by have hs := v8InitMem_size I hlen; omega) (by omega)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 1568
    (by have hs := v7InitMem_size I hlen; omega) (by omega)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1568
    (by have hs := v6InitMem_size I hlen; omega) (by omega)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 1568
    (by have hs := v5InitMem_size I hlen; omega) (by omega)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 1568
    (by have hs := v4InitMem_size I hlen; omega) (by omega)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 1568
    (by have hs := v3InitMem_size I hlen; omega) (by omega)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  exact toByteArray_write_read_self_extract32 (v3StoredWord I) (v2InitMem I) 1568
    (by rw [v2InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV3LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV3LoadWord (v13MixedMem I) = v3StoredWord I := by
  unfold outputV3LoadWord
  rw [v13MixedMem_read1568_eq_v3StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v3StoredWord I)

theorem v13MixedMem_read1824_eq_iv3
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1824 32 =
      (UInt256.toByteArray (UInt256.ofNat 11912009170470909681)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1824
    (by have hs := v12MixedMem_size I hlen; omega) (by omega)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1824
    (by have hs := v15InitMem_size I hlen; omega) (by omega)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1824
    (by have hs := v14InitMem_size I hlen; omega) (by omega)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1824
    (by have hs := v13InitMem_size I hlen; omega) (by omega)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1824
    (by have hs := v12InitMem_size I hlen; omega) (by omega)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1824
    (by have hs := v11InitMem_size I hlen; omega) (by omega)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV11LoadWord_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV11LoadWord (v13MixedMem I) = UInt256.ofNat 11912009170470909681 := by
  unfold outputV11LoadWord
  rw [v13MixedMem_read1824_eq_iv3 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 11912009170470909681)

theorem outputWord3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord3 (v13MixedMem I) = UInt256.ofNat 11912009170470909681 := by
  unfold outputWord3
  rw [outputH3LoadWord_v13MixedMem I hlen, outputV3LoadWord_v13MixedMem I hlen,
    outputV11LoadWord_v13MixedMem I hlen]
  unfold v3StoredWord
  rw [outputWord_xor_cancel]
  native_decide

end Blake2f
