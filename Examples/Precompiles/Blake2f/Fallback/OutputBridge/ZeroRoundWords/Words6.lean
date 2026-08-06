import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words5

/-!
# BLAKE2F zero-round output-word bridge: word 6

This file bridges zero-round output word 6.  This is the final-flag-sensitive word:
for flag `0` the bytecode reads IV[6], and for flag `1` it reads the final-flag-mixed word.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem5_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem5 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem5 outputWord5Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord5 (outputWordsMem4 mem)) (outputWordsMem4 mem) 1376 read
    (by rw [outputWordsMem4_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem4_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem4_read_below_output_slots hmem hread hbelow

theorem outputWordsMem5_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1376 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem5 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem5 outputWord5Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord5 (outputWordsMem4 mem))) (outputWordsMem4 mem)
    1376 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem4_size hmem]; decide)
    habove
    (by rw [outputWordsMem4_size hmem]; exact hin)
    (by decide) (by decide)]
  exact outputWordsMem4_read_above_output_slots hmem (by omega) hin

theorem outputWordsMem5_v13MixedMem_read576
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v13MixedMem I)).readWithPadding 576 32 =
      (v13MixedMem I).readWithPadding 576 32 := by
  exact outputWordsMem5_read_below_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem5_v13MixedMem_read1664
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v13MixedMem I)).readWithPadding 1664 32 =
      (v13MixedMem I).readWithPadding 1664 32 := by
  exact outputWordsMem5_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem5_v13MixedMem_read1920
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v13MixedMem I)).readWithPadding 1920 32 =
      (v13MixedMem I).readWithPadding 1920 32 := by
  exact outputWordsMem5_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem5_v14FinalFlagMem_read576
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v14FinalFlagMem I)).readWithPadding 576 32 =
      (v14FinalFlagMem I).readWithPadding 576 32 := by
  exact outputWordsMem5_read_below_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem5_v14FinalFlagMem_read1664
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v14FinalFlagMem I)).readWithPadding 1664 32 =
      (v14FinalFlagMem I).readWithPadding 1664 32 := by
  exact outputWordsMem5_read_above_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem5_v14FinalFlagMem_read1920
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem5 (v14FinalFlagMem I)).readWithPadding 1920 32 =
      (v14FinalFlagMem I).readWithPadding 1920 32 := by
  exact outputWordsMem5_read_above_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem v13MixedMem_read576_eq_v5InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 576 32 =
      (v5InitMem I).readWithPadding 576 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 576
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 576
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 576
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 576
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 576
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 576
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 576
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 576
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 576
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 576
    (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 576
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 576
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]

theorem v14FinalFlagMem_read576_eq_v5InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 576 32 =
      (v5InitMem I).readWithPadding 576 32 := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 576
    (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read576_eq_v5InitMem I hlen

theorem outputH6LoadWord_outputWordsMem5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH6LoadWord (outputWordsMem5 (v13MixedMem I)) = v6LoadWord I := by
  unfold outputH6LoadWord v6LoadWord
  rw [outputWordsMem5_v13MixedMem_read576 I hlen, v13MixedMem_read576_eq_v5InitMem I hlen]

theorem outputH6LoadWord_outputWordsMem5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH6LoadWord (outputWordsMem5 (v14FinalFlagMem I)) = v6LoadWord I := by
  unfold outputH6LoadWord v6LoadWord
  rw [outputWordsMem5_v14FinalFlagMem_read576 I hlen, v14FinalFlagMem_read576_eq_v5InitMem I hlen]

theorem v13MixedMem_read1664_eq_v6StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1664 32 =
      (UInt256.toByteArray (v6StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1664
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1664
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1664
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1664
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1664
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1664
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1664
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1664
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1664
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 1664
    (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1664
    (by rw [v6InitMem_size I hlen]) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  exact toByteArray_write_read_self_extract32 (v6StoredWord I) (v5InitMem I) 1664
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem v14FinalFlagMem_read1664_eq_v6StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1664 32 =
      (UInt256.toByteArray (v6StoredWord I)).extract 0 32 := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 1664
    (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read1664_eq_v6StoredWord I hlen

theorem outputV6LoadWord_outputWordsMem5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV6LoadWord (outputWordsMem5 (v13MixedMem I)) = v6StoredWord I := by
  unfold outputV6LoadWord
  rw [outputWordsMem5_v13MixedMem_read1664 I hlen, v13MixedMem_read1664_eq_v6StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v6StoredWord I)

theorem outputV6LoadWord_outputWordsMem5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV6LoadWord (outputWordsMem5 (v14FinalFlagMem I)) = v6StoredWord I := by
  unfold outputV6LoadWord
  rw [outputWordsMem5_v14FinalFlagMem_read1664 I hlen, v14FinalFlagMem_read1664_eq_v6StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v6StoredWord I)

theorem v13MixedMem_read1920_eq_iv6
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1920 32 =
      (UInt256.toByteArray (UInt256.ofNat 2270897969802886507)).extract 0 32 := by
  rw [v13MixedMem]
  rw [write32_read_above_len (UInt256.toByteArray (v13MixedWord I)) (v12MixedMem I)
    1888 1920 32
    (by rw [toByteArray_size])
    (by rw [v12MixedMem_size I hlen]; decide)
    (by decide)
    (by rw [v12MixedMem_size I hlen]; decide)
    (by decide) (by decide)]
  rw [v12MixedMem]
  rw [write32_read_above_len (UInt256.toByteArray (v12MixedWord I)) (v15InitMem I)
    1856 1920 32
    (by rw [toByteArray_size])
    (by rw [v15InitMem_size I hlen]; decide)
    (by decide)
    (by rw [v15InitMem_size I hlen]; decide)
    (by decide) (by decide)]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1920
    (by rw [v14InitMem_size I hlen]) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem v14FinalFlagMem_read1920_eq_finalFlagWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1920 32 =
      (UInt256.toByteArray (UInt256.ofNat 16175846103906665108)).extract 0 32 := by
  rw [v14FinalFlagMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV14LoadWord_outputWordsMem5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV14LoadWord (outputWordsMem5 (v13MixedMem I)) = UInt256.ofNat 2270897969802886507 := by
  unfold outputV14LoadWord
  rw [outputWordsMem5_v13MixedMem_read1920 I hlen, v13MixedMem_read1920_eq_iv6 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 2270897969802886507)

theorem outputV14LoadWord_outputWordsMem5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV14LoadWord (outputWordsMem5 (v14FinalFlagMem I)) =
      UInt256.ofNat 16175846103906665108 := by
  unfold outputV14LoadWord
  rw [outputWordsMem5_v14FinalFlagMem_read1920 I hlen, v14FinalFlagMem_read1920_eq_finalFlagWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 16175846103906665108)

theorem outputWord6_outputWordsMem5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord6 (outputWordsMem5 (v13MixedMem I)) = UInt256.ofNat 2270897969802886507 := by
  unfold outputWord6
  rw [outputH6LoadWord_outputWordsMem5_v13MixedMem I hlen,
    outputV6LoadWord_outputWordsMem5_v13MixedMem I hlen,
    outputV14LoadWord_outputWordsMem5_v13MixedMem I hlen]
  unfold v6StoredWord
  rw [outputWord_xor_cancel]
  native_decide

theorem outputWord6_outputWordsMem5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord6 (outputWordsMem5 (v14FinalFlagMem I)) = UInt256.ofNat 16175846103906665108 := by
  unfold outputWord6
  rw [outputH6LoadWord_outputWordsMem5_v14FinalFlagMem I hlen,
    outputV6LoadWord_outputWordsMem5_v14FinalFlagMem I hlen,
    outputV14LoadWord_outputWordsMem5_v14FinalFlagMem I hlen]
  unfold v6StoredWord
  rw [outputWord_xor_cancel]
  native_decide

end Blake2f
