import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserSlots

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem usize_pos0 : 0 < USize.size :=
  lt_usize 0 (by norm_num)

theorem solcBytesSetPaddedMem_read_payload_window
    (cd : ByteArray) (hlen : cd.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (solcBytesSetPaddedMem cd (UInt256.ofNat 213) ⟨0⟩).readWithPadding (160 + off) len =
      cd.extract off (off + len) := by
  let base := solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩
  have hlenWord : (UInt256.ofNat 213).toNat ≠ 0 := by decide
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ cd.size := by
    rw [hlen]
    decide
  have hbaseSize : base.size = 373 := by
    change (solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩).size = 373
    rw [solcBytesSetCalldataMem_size cd (UInt256.ofNat 213) ⟨0⟩ hlenWord hsrc]
    decide
  have hpayload :
      base.extract 160 (160 + (UInt256.ofNat 213).toNat) =
        cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat) := by
    change
      (solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩).extract
          160 (160 + (UInt256.ofNat 213).toNat) =
        cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat)
    exact solcBytesSetCalldataMem_extract_payload cd (UInt256.ofNat 213) ⟨0⟩ hlenWord hsrc
  have hpayloadTail :
      base.extract (160 + off) (160 + off + len) = cd.extract off (off + len) := by
    have h := congrArg (fun b : ByteArray => b.extract off (off + len)) hpayload
    change
      (base.extract 160 (160 + (UInt256.ofNat 213).toNat)).extract off (off + len) =
        (cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat)).extract off (off + len) at h
    rw [extract_extract_BA] at h
    rw [extract_extract_BA] at h
    rw [show (UInt256.ofNat 213).toNat = 213 by decide] at h
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide] at h
    rw [show min (0 + (off + len)) (0 + 213) = off + len by omega] at h
    rw [show min (160 + (off + len)) (160 + 213) = 160 + off + len by omega] at h
    simpa using h
  unfold solcBytesSetPaddedMem
  change
    ((⟨0⟩ : UInt256).toByteArray.write 0 base
        (((⟨160⟩ : UInt256) + UInt256.ofNat 213).toNat) 32).readWithPadding (160 + off) len =
      cd.extract off (off + len)
  have hend : (((⟨160⟩ : UInt256) + UInt256.ofNat 213).toNat) = 373 := by
    native_decide
  rw [hend]
  rw [write_read_below_gen_from_extend (UInt256.toByteArray (⟨0⟩ : UInt256)) base
    0 373 32 (160 + off) len
    (by decide) (by rw [toByteArray_size]) (by omega)
    (by omega) (by omega) hpos hlen64]
  rw [readWithPadding_eq_extract' base (160 + off) len hpos hlen64 (by omega)]
  exact hpayloadTail

theorem hArrayAllocMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (hArrayAllocMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold hArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 640))
    (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩)
    64 (160 + off) len
    (by rw [toByteArray_size])
    (by
      have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
        rw [hlen]
        decide
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)
    (by omega)
    (by
      have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
        rw [hlen]
        decide
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      rw [show (UInt256.ofNat 213).toNat = 213 by decide]
      omega)
    hpos hlen64]
  exact solcBytesSetPaddedMem_read_payload_window I.calldata hlen off len hwin hpos hlen64

theorem hArrayZeroMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (hArrayZeroMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  have hsize : (hArrayAllocMem I).size = 405 := hArrayAllocMem_size I hlen
  unfold hArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 21).copySlice 0 (hArrayAllocMem I) 384 21).readWithPadding
    (160 + off) len = I.calldata.extract off (off + len)
  rw [copySlice_read_below_gen]
  exact hArrayAllocMem_read_payload_window I hlen off len hwin hpos hlen64
  · omega
  · rw [hsize]
    omega
  · exact hpos
  · exact hlen64

theorem mArrayAllocMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (mArrayAllocMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold mArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1152))
    (hArrayZeroMem I) 64 (160 + off) len
    (by rw [toByteArray_size])
    (by rw [hArrayZeroMem_size I hlen]; decide)
    (by omega)
    (by rw [hArrayZeroMem_size I hlen]; omega)
    hpos hlen64]
  exact hArrayZeroMem_read_payload_window I hlen off len hwin hpos hlen64

theorem mArrayZeroMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (mArrayZeroMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  have hsize : (mArrayAllocMem I).size = 405 := mArrayAllocMem_size I hlen
  unfold mArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 512 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (mArrayAllocMem I) 405 0).readWithPadding
    (160 + off) len = I.calldata.extract off (off + len)
  rw [copySlice_read_below_gen]
  exact mArrayAllocMem_read_payload_window I hlen off len hwin hpos hlen64
  · omega
  · rw [hsize]
    omega
  · exact hpos
  · exact hlen64

theorem tArrayAllocMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (tArrayAllocMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold tArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1216))
    (mArrayZeroMem I) 64 (160 + off) len
    (by rw [toByteArray_size])
    (by rw [mArrayZeroMem_size I hlen]; decide)
    (by omega)
    (by rw [mArrayZeroMem_size I hlen]; omega)
    hpos hlen64]
  exact mArrayZeroMem_read_payload_window I hlen off len hwin hpos hlen64

theorem tArrayZeroMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (tArrayZeroMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  have hsize : (tArrayAllocMem I).size = 405 := tArrayAllocMem_size I hlen
  unfold tArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (tArrayAllocMem I) 405 0).readWithPadding
    (160 + off) len = I.calldata.extract off (off + len)
  rw [copySlice_read_below_gen]
  exact tArrayAllocMem_read_payload_window I hlen off len hwin hpos hlen64
  · omega
  · rw [hsize]
    omega
  · exact hpos
  · exact hlen64

theorem m15StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m15StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m15StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 (160 + off) len (by omega) hpos hlen64
    (by rw [m14StoredMem_size I hlen]; exact usize_pos0)]
  unfold m14StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 (160 + off) len (by omega) hpos hlen64
    (by rw [m13StoredMem_size I hlen]; exact usize_pos0)]
  unfold m13StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 (160 + off) len (by omega) hpos hlen64
    (by rw [m12StoredMem_size I hlen]; exact usize_pos0)]
  unfold m12StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 (160 + off) len (by omega) hpos hlen64
    (by rw [m11StoredMem_size I hlen]; exact usize_pos0)]
  unfold m11StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 (160 + off) len (by omega) hpos hlen64
    (by rw [m10StoredMem_size I hlen]; exact usize_pos0)]
  unfold m10StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 (160 + off) len (by omega) hpos hlen64
    (by rw [m9StoredMem_size I hlen]; exact usize_pos0)]
  unfold m9StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 (160 + off) len (by omega) hpos hlen64
    (by rw [m8StoredMem_size I hlen]; exact usize_pos0)]
  unfold m8StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 (160 + off) len (by omega) hpos hlen64
    (by rw [m7StoredMem_size I hlen]; exact usize_pos0)]
  unfold m7StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 (160 + off) len (by omega) hpos hlen64
    (by rw [m6StoredMem_size I hlen]; exact usize_pos0)]
  unfold m6StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 (160 + off) len (by omega) hpos hlen64
    (by rw [m5StoredMem_size I hlen]; exact usize_pos0)]
  unfold m5StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 (160 + off) len (by omega) hpos hlen64
    (by rw [m4StoredMem_size I hlen]; exact usize_pos0)]
  unfold m4StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 (160 + off) len (by omega) hpos hlen64
    (by rw [m3StoredMem_size I hlen]; exact usize_pos0)]
  unfold m3StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 (160 + off) len (by omega) hpos hlen64
    (by rw [m2StoredMem_size I hlen]; exact usize_pos0)]
  unfold m2StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 (160 + off) len (by omega) hpos hlen64
    (by rw [m1StoredMem_size I hlen]; exact usize_pos0)]
  unfold m1StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 (160 + off) len (by omega) hpos hlen64
    (by rw [m0StoredMem_size I hlen]; exact usize_pos0)]
  unfold m0StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 (160 + off) len (by omega) hpos hlen64
    (by rw [h7StoredMem_size I hlen]; exact usize_pos0)]
  unfold h7StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 (160 + off) len (by omega) hpos hlen64
    (by rw [h6StoredMem_size I hlen]; exact usize_pos0)]
  unfold h6StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h6ParsedWord I)
    (h5StoredMem I) 576 (160 + off) len (by omega) hpos hlen64
    (by rw [h5StoredMem_size I hlen]; exact usize_pos0)]
  unfold h5StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h5ParsedWord I)
    (h4StoredMem I) 544 (160 + off) len (by omega) hpos hlen64
    (by rw [h4StoredMem_size I hlen]; exact usize_pos0)]
  unfold h4StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h4ParsedWord I)
    (h3StoredMem I) 512 (160 + off) len (by omega) hpos hlen64
    (by rw [h3StoredMem_size I hlen]; exact usize_pos0)]
  unfold h3StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h3ParsedWord I)
    (h2StoredMem I) 480 (160 + off) len (by omega) hpos hlen64
    (by rw [h2StoredMem_size I hlen]; exact usize_pos0)]
  unfold h2StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h2ParsedWord I)
    (h1StoredMem I) 448 (160 + off) len (by omega) hpos hlen64
    (by rw [h1StoredMem_size I hlen]; exact usize_pos0)]
  unfold h1StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h1ParsedWord I)
    (h0StoredMem I) 416 (160 + off) len (by omega) hpos hlen64
    (by rw [h0StoredMem_size I hlen]; exact usize_pos0)]
  unfold h0StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (h0ParsedWord I)
    (tArrayZeroMem I) 384 (160 + off) len (by omega) hpos hlen64
    (by rw [tArrayZeroMem_size I hlen]; exact usize_pos0)]
  exact tArrayZeroMem_read_payload_window I hlen off len hwin hpos hlen64

theorem m15StoredMem_read356_8 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m15StoredMem I).readWithPadding 356 8 =
      I.calldata.extract 196 204 := by
  simpa using m15StoredMem_read_payload_window I hlen 196 8
    (by decide) (by decide) (by decide)

theorem m15StoredMem_read364_8 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (m15StoredMem I).readWithPadding 364 8 =
      I.calldata.extract 204 212 := by
  simpa using m15StoredMem_read_payload_window I hlen 204 8
    (by decide) (by decide) (by decide)

end Blake2f
