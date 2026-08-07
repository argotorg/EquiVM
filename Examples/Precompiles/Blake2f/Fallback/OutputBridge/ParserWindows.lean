import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserSlots

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem usize_pos0 : 0 < USize.size :=
  lt_usize 0 (by norm_num)

theorem parserSlotWrite_read_payload_window
    (I : ExecutionEnv) (word : UInt256) {base : ByteArray} {off len storeOff : Nat}
    (hbelow : 160 + off + len ≤ storeOff)
    (hbase : base.readWithPadding (160 + off) len = I.calldata.extract off (off + len))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : storeOff - base.size < USize.size) :
    ((UInt256.toByteArray word).write 0 base storeOff 32).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  rw [toByteArray_write_read_below_len_padded_of_gap word base storeOff (160 + off) len
    (by omega) hpos hlen64 hgap]
  exact hbase

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

theorem h0StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h0StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h0StoredMem
  exact parserSlotWrite_read_payload_window I (h0ParsedWord I)
    (storeOff := 384) (by omega)
    (tArrayZeroMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [tArrayZeroMem_size I hlen]; exact usize_pos0)

theorem h1StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h1StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h1StoredMem
  exact parserSlotWrite_read_payload_window I (h1ParsedWord I)
    (storeOff := 416) (by omega)
    (h0StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h0StoredMem_size I hlen]; exact usize_pos0)

theorem h2StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h2StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h2StoredMem
  exact parserSlotWrite_read_payload_window I (h2ParsedWord I)
    (storeOff := 448) (by omega)
    (h1StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h1StoredMem_size I hlen]; exact usize_pos0)

theorem h3StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h3StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h3StoredMem
  exact parserSlotWrite_read_payload_window I (h3ParsedWord I)
    (storeOff := 480) (by omega)
    (h2StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h2StoredMem_size I hlen]; exact usize_pos0)

theorem h4StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h4StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h4StoredMem
  exact parserSlotWrite_read_payload_window I (h4ParsedWord I)
    (storeOff := 512) (by omega)
    (h3StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h3StoredMem_size I hlen]; exact usize_pos0)

theorem h5StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h5StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h5StoredMem
  exact parserSlotWrite_read_payload_window I (h5ParsedWord I)
    (storeOff := 544) (by omega)
    (h4StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h4StoredMem_size I hlen]; exact usize_pos0)

theorem h6StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h6StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h6StoredMem
  exact parserSlotWrite_read_payload_window I (h6ParsedWord I)
    (storeOff := 576) (by omega)
    (h5StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h5StoredMem_size I hlen]; exact usize_pos0)

theorem h7StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (h7StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold h7StoredMem
  exact parserSlotWrite_read_payload_window I (h7ParsedWord I)
    (storeOff := 608) (by omega)
    (h6StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h6StoredMem_size I hlen]; exact usize_pos0)

theorem m0StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m0StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m0StoredMem
  exact parserSlotWrite_read_payload_window I (m0ParsedWord I)
    (storeOff := 640) (by omega)
    (h7StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [h7StoredMem_size I hlen]; exact usize_pos0)

theorem m1StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m1StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m1StoredMem
  exact parserSlotWrite_read_payload_window I (m1ParsedWord I)
    (storeOff := 672) (by omega)
    (m0StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m0StoredMem_size I hlen]; exact usize_pos0)

theorem m2StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m2StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m2StoredMem
  exact parserSlotWrite_read_payload_window I (m2ParsedWord I)
    (storeOff := 704) (by omega)
    (m1StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m1StoredMem_size I hlen]; exact usize_pos0)

theorem m3StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m3StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m3StoredMem
  exact parserSlotWrite_read_payload_window I (m3ParsedWord I)
    (storeOff := 736) (by omega)
    (m2StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m2StoredMem_size I hlen]; exact usize_pos0)

theorem m4StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m4StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m4StoredMem
  exact parserSlotWrite_read_payload_window I (m4ParsedWord I)
    (storeOff := 768) (by omega)
    (m3StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m3StoredMem_size I hlen]; exact usize_pos0)

theorem m5StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m5StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m5StoredMem
  exact parserSlotWrite_read_payload_window I (m5ParsedWord I)
    (storeOff := 800) (by omega)
    (m4StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m4StoredMem_size I hlen]; exact usize_pos0)

theorem m6StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m6StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m6StoredMem
  exact parserSlotWrite_read_payload_window I (m6ParsedWord I)
    (storeOff := 832) (by omega)
    (m5StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m5StoredMem_size I hlen]; exact usize_pos0)

theorem m7StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m7StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m7StoredMem
  exact parserSlotWrite_read_payload_window I (m7ParsedWord I)
    (storeOff := 864) (by omega)
    (m6StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m6StoredMem_size I hlen]; exact usize_pos0)

theorem m8StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m8StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m8StoredMem
  exact parserSlotWrite_read_payload_window I (m8ParsedWord I)
    (storeOff := 896) (by omega)
    (m7StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m7StoredMem_size I hlen]; exact usize_pos0)

theorem m9StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m9StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m9StoredMem
  exact parserSlotWrite_read_payload_window I (m9ParsedWord I)
    (storeOff := 928) (by omega)
    (m8StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m8StoredMem_size I hlen]; exact usize_pos0)

theorem m10StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m10StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m10StoredMem
  exact parserSlotWrite_read_payload_window I (m10ParsedWord I)
    (storeOff := 960) (by omega)
    (m9StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m9StoredMem_size I hlen]; exact usize_pos0)

theorem m11StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m11StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m11StoredMem
  exact parserSlotWrite_read_payload_window I (m11ParsedWord I)
    (storeOff := 992) (by omega)
    (m10StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m10StoredMem_size I hlen]; exact usize_pos0)

theorem m12StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m12StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m12StoredMem
  exact parserSlotWrite_read_payload_window I (m12ParsedWord I)
    (storeOff := 1024) (by omega)
    (m11StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m11StoredMem_size I hlen]; exact usize_pos0)

theorem m13StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m13StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m13StoredMem
  exact parserSlotWrite_read_payload_window I (m13ParsedWord I)
    (storeOff := 1056) (by omega)
    (m12StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m12StoredMem_size I hlen]; exact usize_pos0)

theorem m14StoredMem_read_payload_window
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) (off len : Nat)
    (hwin : off + len ≤ 213) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (m14StoredMem I).readWithPadding (160 + off) len =
      I.calldata.extract off (off + len) := by
  unfold m14StoredMem
  exact parserSlotWrite_read_payload_window I (m14ParsedWord I)
    (storeOff := 1088) (by omega)
    (m13StoredMem_read_payload_window I hlen off len hwin hpos hlen64)
    hpos hlen64
    (by rw [m13StoredMem_size I hlen]; exact usize_pos0)

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
