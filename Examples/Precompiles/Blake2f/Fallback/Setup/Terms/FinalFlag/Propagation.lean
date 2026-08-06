import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.FinalFlag.Calldata
import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem hArrayAllocMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayAllocMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  unfold hArrayAllocMem
  exact write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 640))
    (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩) 64 372 1
    (by rw [toByteArray_size])
    (by
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)
    (by decide)
    (by
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)
    (by decide)
    (by decide)

theorem hArrayZeroMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayZeroMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  have hsize : (hArrayAllocMem I).size = 405 := hArrayAllocMem_size I hlen
  unfold hArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 21).copySlice 0 (hArrayAllocMem I) 384 21).readWithPadding
    372 1 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1
  rw [copySlice_read_below_gen]
  exact hArrayAllocMem_read372_one I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem mArrayAllocMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayAllocMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  unfold mArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1152))
    (hArrayZeroMem I) 64 372 1
    (by rw [toByteArray_size])
    (by rw [hArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by rw [hArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by decide)]
  exact hArrayZeroMem_read372_one I hlen

theorem mArrayZeroMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayZeroMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  have hsize : (mArrayAllocMem I).size = 405 := mArrayAllocMem_size I hlen
  unfold mArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 512 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (mArrayAllocMem I) 405 0).readWithPadding
    372 1 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1
  rw [copySlice_read_below_gen]
  exact mArrayAllocMem_read372_one I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem tArrayAllocMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayAllocMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  unfold tArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1216))
    (mArrayZeroMem I) 64 372 1
    (by rw [toByteArray_size])
    (by rw [mArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by rw [mArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by decide)]
  exact mArrayZeroMem_read372_one I hlen

theorem tArrayZeroMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayZeroMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  have hsize : (tArrayAllocMem I).size = 405 := tArrayAllocMem_size I hlen
  unfold tArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (tArrayAllocMem I) 405 0).readWithPadding
    372 1 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1
  rw [copySlice_read_below_gen]
  exact tArrayAllocMem_read372_one I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem toByteArray_write_preserves_read372_one
    (w : UInt256) (mem : ByteArray) (off size : Nat)
    (hsize : mem.size = size) (hin : 373 ≤ size) (hbelow : 373 ≤ off) (hoff : off ≤ size) :
    ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding 372 1 =
      mem.readWithPadding 372 1 := by
  exact toByteArray_write_read_below_len_of_gap w mem off 372 1
    (by rw [hsize]; omega)
    (by omega)
    (by decide)
    (by decide)
    (by
      rw [hsize]
      have hsub : off - size = 0 := by omega
      rw [hsub]
      exact lt_usize 0 (by norm_num))

theorem t1StoredMem_read372_one (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 372 1 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 1 := by
  rw [t1StoredMem]
  rw [toByteArray_write_preserves_read372_one (t1ParsedWord I) (t0StoredMem I) 1184 1184
    (t0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [t0StoredMem]
  rw [toByteArray_write_preserves_read372_one (t0ParsedWord I) (m15StoredMem I) 1152 1152
    (m15StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m15StoredMem]
  rw [toByteArray_write_preserves_read372_one (m15ParsedWord I) (m14StoredMem I) 1120 1120
    (m14StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m14StoredMem]
  rw [toByteArray_write_preserves_read372_one (m14ParsedWord I) (m13StoredMem I) 1088 1088
    (m13StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m13StoredMem]
  rw [toByteArray_write_preserves_read372_one (m13ParsedWord I) (m12StoredMem I) 1056 1056
    (m12StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m12StoredMem]
  rw [toByteArray_write_preserves_read372_one (m12ParsedWord I) (m11StoredMem I) 1024 1024
    (m11StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m11StoredMem]
  rw [toByteArray_write_preserves_read372_one (m11ParsedWord I) (m10StoredMem I) 992 992
    (m10StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m10StoredMem]
  rw [toByteArray_write_preserves_read372_one (m10ParsedWord I) (m9StoredMem I) 960 960
    (m9StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m9StoredMem]
  rw [toByteArray_write_preserves_read372_one (m9ParsedWord I) (m8StoredMem I) 928 928
    (m8StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m8StoredMem]
  rw [toByteArray_write_preserves_read372_one (m8ParsedWord I) (m7StoredMem I) 896 896
    (m7StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m7StoredMem]
  rw [toByteArray_write_preserves_read372_one (m7ParsedWord I) (m6StoredMem I) 864 864
    (m6StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m6StoredMem]
  rw [toByteArray_write_preserves_read372_one (m6ParsedWord I) (m5StoredMem I) 832 832
    (m5StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m5StoredMem]
  rw [toByteArray_write_preserves_read372_one (m5ParsedWord I) (m4StoredMem I) 800 800
    (m4StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m4StoredMem]
  rw [toByteArray_write_preserves_read372_one (m4ParsedWord I) (m3StoredMem I) 768 768
    (m3StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m3StoredMem]
  rw [toByteArray_write_preserves_read372_one (m3ParsedWord I) (m2StoredMem I) 736 736
    (m2StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m2StoredMem]
  rw [toByteArray_write_preserves_read372_one (m2ParsedWord I) (m1StoredMem I) 704 704
    (m1StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m1StoredMem]
  rw [toByteArray_write_preserves_read372_one (m1ParsedWord I) (m0StoredMem I) 672 672
    (m0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m0StoredMem]
  rw [toByteArray_write_preserves_read372_one (m0ParsedWord I) (h7StoredMem I) 640 640
    (h7StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h7StoredMem]
  rw [toByteArray_write_preserves_read372_one (h7ParsedWord I) (h6StoredMem I) 608 608
    (h6StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h6StoredMem]
  rw [toByteArray_write_preserves_read372_one (h6ParsedWord I) (h5StoredMem I) 576 576
    (h5StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h5StoredMem]
  rw [toByteArray_write_preserves_read372_one (h5ParsedWord I) (h4StoredMem I) 544 544
    (h4StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h4StoredMem]
  rw [toByteArray_write_preserves_read372_one (h4ParsedWord I) (h3StoredMem I) 512 512
    (h3StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h3StoredMem]
  rw [toByteArray_write_preserves_read372_one (h3ParsedWord I) (h2StoredMem I) 480 480
    (h2StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h2StoredMem]
  rw [toByteArray_write_preserves_read372_one (h2ParsedWord I) (h1StoredMem I) 448 448
    (h1StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h1StoredMem]
  rw [toByteArray_write_preserves_read372_one (h1ParsedWord I) (h0StoredMem I) 416 416
    (h0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h0StoredMem]
  rw [toByteArray_write_preserves_read372_one (h0ParsedWord I) (tArrayZeroMem I) 384 405
    (tArrayZeroMem_size I hlen) (by decide) (by decide) (by decide)]
  exact tArrayZeroMem_read372_one I hlen

theorem t1StoredMem_read372_first (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    ((t1StoredMem I).readWithPadding 372 32).extract 0 1 =
      ⟨#[I.calldata[212]!]⟩ := by
  rw [readWithPadding_extract_first_of_in_bounds (t1StoredMem I) 372
    (by rw [t1StoredMem_size I hlen]; decide)]
  rw [t1StoredMem_read372_one I hlen]
  rw [← readWithPadding_extract_first_of_in_bounds
    (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩) 372 (by
      have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
        rw [hlen]
        decide
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)]
  exact solcBytesSetPaddedMem_read372_first I.calldata hlen

end Blake2f
