import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words4

/-!
# BLAKE2F zero-round output-word bridge: word 5

This file bridges zero-round output word 5.  In the zero-round state, `v[5] = h[5]`,
so the bytecode output expression reduces to the mixed `v[13]` word, i.e. the IV[5] word
xored with the parsed `t1` word.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem4_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem4 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem4 outputWord4Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord4 (outputWordsMem3 mem)) (outputWordsMem3 mem) 1344 read
    (by rw [outputWordsMem3_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem3_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem3_read_below_output_slots hmem hread hbelow

theorem outputWordsMem4_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1344 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem4 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem4 outputWord4Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord4 (outputWordsMem3 mem))) (outputWordsMem3 mem)
    1344 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem3_size hmem]; decide)
    habove
    (by rw [outputWordsMem3_size hmem]; exact hin)
    (by decide) (by decide)]
  exact outputWordsMem3_read_above_output_slots hmem (by omega) hin

theorem outputWordsMem4_v13MixedMem_read544
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem4 (v13MixedMem I)).readWithPadding 544 32 =
      (v13MixedMem I).readWithPadding 544 32 := by
  exact outputWordsMem4_read_below_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem4_v13MixedMem_read1632
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem4 (v13MixedMem I)).readWithPadding 1632 32 =
      (v13MixedMem I).readWithPadding 1632 32 := by
  exact outputWordsMem4_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem4_v13MixedMem_read1888
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem4 (v13MixedMem I)).readWithPadding 1888 32 =
      (v13MixedMem I).readWithPadding 1888 32 := by
  exact outputWordsMem4_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem v13MixedMem_read544_eq_v4InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 544 32 =
      (v4InitMem I).readWithPadding 544 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 544
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 544
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I)
    1952 544 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I)
    1920 544 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I)
    1888 544 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I)
    1856 544 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I)
    1824 544 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I)
    1792 544 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I)
    1760 544 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I)
    1728 544 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 544
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 544
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 544
    (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]

theorem outputH5LoadWord_outputWordsMem4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH5LoadWord (outputWordsMem4 (v13MixedMem I)) = v5LoadWord I := by
  unfold outputH5LoadWord v5LoadWord
  rw [outputWordsMem4_v13MixedMem_read544 I hlen, v13MixedMem_read544_eq_v4InitMem I hlen]

theorem v13MixedMem_read1632_eq_v5StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1632 32 =
      (UInt256.toByteArray (v5StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1632
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1632
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I)
    1952 1632 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I)
    1920 1632 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I)
    1888 1632 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I)
    1856 1632 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I)
    1824 1632 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I)
    1792 1632 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I)
    1760 1632 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I)
    1728 1632 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1632
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 1632
    (by rw [v5InitMem_size I hlen]) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  exact toByteArray_write_read_self_extract32 (v5StoredWord I) (v4InitMem I) 1632
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV5LoadWord_outputWordsMem4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV5LoadWord (outputWordsMem4 (v13MixedMem I)) = v5StoredWord I := by
  unfold outputV5LoadWord
  rw [outputWordsMem4_v13MixedMem_read1632 I hlen, v13MixedMem_read1632_eq_v5StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v5StoredWord I)

theorem v13MixedMem_read1888_eq_v13MixedWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1888 32 =
      (UInt256.toByteArray (v13MixedWord I)).extract 0 32 := by
  rw [v13MixedMem]
  exact toByteArray_write_read_self_extract32 (v13MixedWord I) (v12MixedMem I) 1888
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV13LoadWord_outputWordsMem4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV13LoadWord (outputWordsMem4 (v13MixedMem I)) = v13MixedWord I := by
  unfold outputV13LoadWord
  rw [outputWordsMem4_v13MixedMem_read1888 I hlen, v13MixedMem_read1888_eq_v13MixedWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v13MixedWord I)

theorem outputWord5_outputWordsMem4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord5 (outputWordsMem4 (v13MixedMem I)) =
      UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩ := by
  unfold outputWord5
  rw [outputH5LoadWord_outputWordsMem4_v13MixedMem I hlen,
    outputV5LoadWord_outputWordsMem4_v13MixedMem I hlen,
    outputV13LoadWord_outputWordsMem4_v13MixedMem I hlen]
  unfold v5StoredWord
  exact outputWord_xor_cancel (UInt256.land (v5LoadWord I) ⟨18446744073709551615⟩)
    (v13MixedWord I) ⟨18446744073709551615⟩

end Blake2f
