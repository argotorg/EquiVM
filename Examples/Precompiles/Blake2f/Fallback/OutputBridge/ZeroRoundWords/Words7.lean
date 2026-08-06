import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words6

/-!
# BLAKE2F zero-round output-word bridge: word 7

This file bridges zero-round output word 7.  The final-flag write ends at the start of the
`v[15]` slot, so both zero-round terminal memories reduce to IV[7].
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem6_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem6 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem6 outputWord6Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord6 (outputWordsMem5 mem)) (outputWordsMem5 mem) 1408 read
    (by rw [outputWordsMem5_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem5_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem5_read_below_output_slots hmem hread hbelow

theorem outputWordsMem6_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1408 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem6 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem6 outputWord6Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord6 (outputWordsMem5 mem))) (outputWordsMem5 mem)
    1408 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem5_size hmem]; decide)
    habove
    (by rw [outputWordsMem5_size hmem]; exact hin)
    (by decide) (by decide)]
  exact outputWordsMem5_read_above_output_slots hmem (by omega) hin

theorem outputWordsMem6_v13MixedMem_read608
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v13MixedMem I)).readWithPadding 608 32 =
      (v13MixedMem I).readWithPadding 608 32 := by
  exact outputWordsMem6_read_below_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem6_v13MixedMem_read1696
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v13MixedMem I)).readWithPadding 1696 32 =
      (v13MixedMem I).readWithPadding 1696 32 := by
  exact outputWordsMem6_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem6_v13MixedMem_read1952
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v13MixedMem I)).readWithPadding 1952 32 =
      (v13MixedMem I).readWithPadding 1952 32 := by
  exact outputWordsMem6_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem6_v14FinalFlagMem_read608
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v14FinalFlagMem I)).readWithPadding 608 32 =
      (v14FinalFlagMem I).readWithPadding 608 32 := by
  exact outputWordsMem6_read_below_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem6_v14FinalFlagMem_read1696
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v14FinalFlagMem I)).readWithPadding 1696 32 =
      (v14FinalFlagMem I).readWithPadding 1696 32 := by
  exact outputWordsMem6_read_above_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem6_v14FinalFlagMem_read1952
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem6 (v14FinalFlagMem I)).readWithPadding 1952 32 =
      (v14FinalFlagMem I).readWithPadding 1952 32 := by
  exact outputWordsMem6_read_above_output_slots (v14FinalFlagMem_size I hlen)
    (by decide) (by decide)

theorem v13MixedMem_read608_eq_v6InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 608 32 =
      (v6InitMem I).readWithPadding 608 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 608
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 608
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 608
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 608
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 608
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 608
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 608
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 608
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 608
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 608
    (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 608
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]

theorem v14FinalFlagMem_read608_eq_v6InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 608 32 =
      (v6InitMem I).readWithPadding 608 32 := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 608
    (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read608_eq_v6InitMem I hlen

theorem outputH7LoadWord_outputWordsMem6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH7LoadWord (outputWordsMem6 (v13MixedMem I)) = v7LoadWord I := by
  unfold outputH7LoadWord v7LoadWord
  rw [outputWordsMem6_v13MixedMem_read608 I hlen, v13MixedMem_read608_eq_v6InitMem I hlen]

theorem outputH7LoadWord_outputWordsMem6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH7LoadWord (outputWordsMem6 (v14FinalFlagMem I)) = v7LoadWord I := by
  unfold outputH7LoadWord v7LoadWord
  rw [outputWordsMem6_v14FinalFlagMem_read608 I hlen, v14FinalFlagMem_read608_eq_v6InitMem I hlen]

theorem v13MixedMem_read1696_eq_v7StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1696 32 =
      (UInt256.toByteArray (v7StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1696
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1696
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952 1696
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I) 1920 1696
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I) 1888 1696
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I) 1856 1696
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I) 1824 1696
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I) 1792 1696
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I) 1760 1696
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I) 1728 1696
    (by rw [v7InitMem_size I hlen]) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  exact toByteArray_write_read_self_extract32 (v7StoredWord I) (v6InitMem I) 1696
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem v14FinalFlagMem_read1696_eq_v7StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1696 32 =
      (UInt256.toByteArray (v7StoredWord I)).extract 0 32 := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 1696
    (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read1696_eq_v7StoredWord I hlen

theorem outputV7LoadWord_outputWordsMem6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV7LoadWord (outputWordsMem6 (v13MixedMem I)) = v7StoredWord I := by
  unfold outputV7LoadWord
  rw [outputWordsMem6_v13MixedMem_read1696 I hlen, v13MixedMem_read1696_eq_v7StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v7StoredWord I)

theorem outputV7LoadWord_outputWordsMem6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV7LoadWord (outputWordsMem6 (v14FinalFlagMem I)) = v7StoredWord I := by
  unfold outputV7LoadWord
  rw [outputWordsMem6_v14FinalFlagMem_read1696 I hlen, v14FinalFlagMem_read1696_eq_v7StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v7StoredWord I)

theorem v13MixedMem_read1952_eq_iv7
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1952 32 =
      (UInt256.toByteArray (UInt256.ofNat 6620516959819538809)).extract 0 32 := by
  rw [v13MixedMem]
  rw [write32_read_above_len (UInt256.toByteArray (v13MixedWord I)) (v12MixedMem I)
    1888 1952 32
    (by rw [toByteArray_size])
    (by rw [v12MixedMem_size I hlen]; decide)
    (by decide)
    (by rw [v12MixedMem_size I hlen])
    (by decide) (by decide)]
  rw [v12MixedMem]
  rw [write32_read_above_len (UInt256.toByteArray (v12MixedWord I)) (v15InitMem I)
    1856 1952 32
    (by rw [toByteArray_size])
    (by rw [v15InitMem_size I hlen]; decide)
    (by decide)
    (by rw [v15InitMem_size I hlen])
    (by decide) (by decide)]
  rw [v15InitMem]
  exact toByteArray_write_read_self_extract32 (UInt256.ofNat 6620516959819538809) (v14InitMem I) 1952
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem v14FinalFlagMem_read1952_eq_iv7
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1952 32 =
      (UInt256.toByteArray (UInt256.ofNat 6620516959819538809)).extract 0 32 := by
  rw [v14FinalFlagMem]
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 16175846103906665108))
    (v13MixedMem I) 1920 1952 32
    (by rw [toByteArray_size])
    (by rw [v13MixedMem_size I hlen]; decide)
    (by decide)
    (by rw [v13MixedMem_size I hlen])
    (by decide) (by decide)]
  exact v13MixedMem_read1952_eq_iv7 I hlen

theorem outputV15LoadWord_outputWordsMem6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV15LoadWord (outputWordsMem6 (v13MixedMem I)) = UInt256.ofNat 6620516959819538809 := by
  unfold outputV15LoadWord
  rw [outputWordsMem6_v13MixedMem_read1952 I hlen, v13MixedMem_read1952_eq_iv7 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 6620516959819538809)

theorem outputV15LoadWord_outputWordsMem6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV15LoadWord (outputWordsMem6 (v14FinalFlagMem I)) = UInt256.ofNat 6620516959819538809 := by
  unfold outputV15LoadWord
  rw [outputWordsMem6_v14FinalFlagMem_read1952 I hlen, v14FinalFlagMem_read1952_eq_iv7 I hlen]
  exact readWord_of_toByteArray_extract0_32 (UInt256.ofNat 6620516959819538809)

theorem outputWord7_outputWordsMem6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord7 (outputWordsMem6 (v13MixedMem I)) = UInt256.ofNat 6620516959819538809 := by
  unfold outputWord7
  rw [outputH7LoadWord_outputWordsMem6_v13MixedMem I hlen,
    outputV7LoadWord_outputWordsMem6_v13MixedMem I hlen,
    outputV15LoadWord_outputWordsMem6_v13MixedMem I hlen]
  unfold v7StoredWord
  rw [outputWord_xor_cancel]
  native_decide

theorem outputWord7_outputWordsMem6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord7 (outputWordsMem6 (v14FinalFlagMem I)) = UInt256.ofNat 6620516959819538809 := by
  unfold outputWord7
  rw [outputH7LoadWord_outputWordsMem6_v14FinalFlagMem I hlen,
    outputV7LoadWord_outputWordsMem6_v14FinalFlagMem I hlen,
    outputV15LoadWord_outputWordsMem6_v14FinalFlagMem I hlen]
  unfold v7StoredWord
  rw [outputWord_xor_cancel]
  native_decide

end Blake2f
