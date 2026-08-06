import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words3

/-!
# BLAKE2F zero-round output-word bridge: word 4

This file bridges zero-round output word 4.  In the zero-round state, `v[4] = h[4]`,
so the bytecode output expression reduces to the mixed `v[12]` word, i.e. the IV[4] word
xored with the parsed `t0` word.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem3_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem3 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem3 outputWord3Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord3 (outputWordsMem2 mem)) (outputWordsMem2 mem) 1312 read
    (by rw [outputWordsMem2_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem2_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  unfold outputWordsMem2 outputWord2Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord2 (outputWordsMem1 mem)) (outputWordsMem1 mem) 1280 read
    (by rw [outputWordsMem1_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem1_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  unfold outputWordsMem1 outputWord1Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord1 (outputWordsMem0 mem)) (outputWordsMem0 mem) 1248 read
    (by rw [outputWordsMem0_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem0_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  unfold outputWordsMem0 outputWord0Mem
  exact toByteArray_write_read_below_of_gap
    (outputWord0 mem) mem 1216 read
    (by rw [hmem]; exact hread)
    hbelow
    (by rw [hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem3_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1312 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem3 mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold outputWordsMem3 outputWord3Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord3 (outputWordsMem2 mem))) (outputWordsMem2 mem)
    1312 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem2_size hmem]; decide)
    habove
    (by rw [outputWordsMem2_size hmem]; exact hin)
    (by decide) (by decide)]
  unfold outputWordsMem2 outputWord2Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord2 (outputWordsMem1 mem))) (outputWordsMem1 mem)
    1280 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem1_size hmem]; decide)
    (by omega)
    (by rw [outputWordsMem1_size hmem]; exact hin)
    (by decide) (by decide)]
  unfold outputWordsMem1 outputWord1Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))) (outputWordsMem0 mem)
    1248 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem0_size hmem]; decide)
    (by omega)
    (by rw [outputWordsMem0_size hmem]; exact hin)
    (by decide) (by decide)]
  unfold outputWordsMem0 outputWord0Mem
  exact write32_read_above_len
    (UInt256.toByteArray (outputWord0 mem)) mem 1216 read 32
    (by rw [toByteArray_size])
    (by rw [hmem]; decide)
    (by omega)
    (by rw [hmem]; exact hin)
    (by decide) (by decide)

theorem outputWordsMem3_v13MixedMem_read512
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem3 (v13MixedMem I)).readWithPadding 512 32 =
      (v13MixedMem I).readWithPadding 512 32 := by
  exact outputWordsMem3_read_below_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem3_v13MixedMem_read1600
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem3 (v13MixedMem I)).readWithPadding 1600 32 =
      (v13MixedMem I).readWithPadding 1600 32 := by
  exact outputWordsMem3_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem outputWordsMem3_v13MixedMem_read1856
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem3 (v13MixedMem I)).readWithPadding 1856 32 =
      (v13MixedMem I).readWithPadding 1856 32 := by
  exact outputWordsMem3_read_above_output_slots (v13MixedMem_size I hlen)
    (by decide) (by decide)

theorem v13MixedMem_read512_eq_v3InitMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 512 32 =
      (v3InitMem I).readWithPadding 512 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 512
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 512
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I)
    1952 512 (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I)
    1920 512 (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I)
    1888 512 (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I)
    1856 512 (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I)
    1824 512 (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I)
    1792 512 (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I)
    1760 512 (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I)
    1728 512 (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 512
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 512
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 512
    (by rw [v4InitMem_size I hlen]; decide) (by decide)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_of_gap (v4StoredWord I) (v3InitMem I) 1600 512
    (by rw [v3InitMem_size I hlen]; decide) (by decide)
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]

theorem outputH4LoadWord_outputWordsMem3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputH4LoadWord (outputWordsMem3 (v13MixedMem I)) = v4LoadWord I := by
  unfold outputH4LoadWord v4LoadWord
  rw [outputWordsMem3_v13MixedMem_read512 I hlen, v13MixedMem_read512_eq_v3InitMem I hlen]

theorem v13MixedMem_read1600_eq_v4StoredWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1600 32 =
      (UInt256.toByteArray (v4StoredWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1600
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I) (v15InitMem I) 1856 1600
    (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 6620516959819538809) (v14InitMem I)
    1952 1600
    (by rw [v14InitMem_size I hlen]; decide) (by decide)
    (by rw [v14InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 2270897969802886507) (v13InitMem I)
    1920 1600
    (by rw [v13InitMem_size I hlen]; decide) (by decide)
    (by rw [v13InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11170449401992604703) (v12InitMem I)
    1888 1600
    (by rw [v12InitMem_size I hlen]; decide) (by decide)
    (by rw [v12InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 5840696475078001361) (v11InitMem I)
    1856 1600
    (by rw [v11InitMem_size I hlen]; decide) (by decide)
    (by rw [v11InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 11912009170470909681) (v10InitMem I)
    1824 1600
    (by rw [v10InitMem_size I hlen]; decide) (by decide)
    (by rw [v10InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 4354685564936845355) (v9InitMem I)
    1792 1600
    (by rw [v9InitMem_size I hlen]; decide) (by decide)
    (by rw [v9InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 13503953896175478587) (v8InitMem I)
    1760 1600
    (by rw [v8InitMem_size I hlen]; decide) (by decide)
    (by rw [v8InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 7640891576956012808) (v7InitMem I)
    1728 1600
    (by rw [v7InitMem_size I hlen]; decide) (by decide)
    (by rw [v7InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_of_gap (v7StoredWord I) (v6InitMem I) 1696 1600
    (by rw [v6InitMem_size I hlen]; decide) (by decide)
    (by rw [v6InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_of_gap (v6StoredWord I) (v5InitMem I) 1664 1600
    (by rw [v5InitMem_size I hlen]; decide) (by decide)
    (by rw [v5InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_of_gap (v5StoredWord I) (v4InitMem I) 1632 1600
    (by rw [v4InitMem_size I hlen]) (by decide)
    (by rw [v4InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  exact toByteArray_write_read_self_extract32 (v4StoredWord I) (v3InitMem I) 1600
    (by rw [v3InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV4LoadWord_outputWordsMem3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV4LoadWord (outputWordsMem3 (v13MixedMem I)) = v4StoredWord I := by
  unfold outputV4LoadWord
  rw [outputWordsMem3_v13MixedMem_read1600 I hlen, v13MixedMem_read1600_eq_v4StoredWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v4StoredWord I)

theorem v13MixedMem_read1856_eq_v12MixedWord
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1856 32 =
      (UInt256.toByteArray (v12MixedWord I)).extract 0 32 := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I) (v12MixedMem I) 1888 1856
    (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  exact toByteArray_write_read_self_extract32 (v12MixedWord I) (v15InitMem I) 1856
    (by rw [v15InitMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputV12LoadWord_outputWordsMem3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputV12LoadWord (outputWordsMem3 (v13MixedMem I)) = v12MixedWord I := by
  unfold outputV12LoadWord
  rw [outputWordsMem3_v13MixedMem_read1856 I hlen, v13MixedMem_read1856_eq_v12MixedWord I hlen]
  exact readWord_of_toByteArray_extract0_32 (v12MixedWord I)

theorem outputWord4_outputWordsMem3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord4 (outputWordsMem3 (v13MixedMem I)) =
      UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩ := by
  unfold outputWord4
  rw [outputH4LoadWord_outputWordsMem3_v13MixedMem I hlen,
    outputV4LoadWord_outputWordsMem3_v13MixedMem I hlen,
    outputV12LoadWord_outputWordsMem3_v13MixedMem I hlen]
  unfold v4StoredWord
  exact outputWord_xor_cancel (UInt256.land (v4LoadWord I) ⟨18446744073709551615⟩)
    (v12MixedWord I) ⟨18446744073709551615⟩

end Blake2f
