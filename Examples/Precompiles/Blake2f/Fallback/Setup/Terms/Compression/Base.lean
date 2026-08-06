import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Parser

/-!
# BLAKE2F compression memory lemmas: base readback preservation
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem toByteArray_write_preserves_read64
    (w : UInt256) (mem : ByteArray) (off size : Nat)
    (hsize : mem.size = size) (hin : 96 ≤ size) (hbelow : 96 ≤ off) (hoff : off ≤ size) :
    ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  exact toByteArray_write_read_below_of_gap w mem off 64
    (by rw [hsize]; omega)
    (by omega)
    (by
      rw [hsize]
      have hsub : off - size = 0 := by omega
      rw [hsub]
      exact lt_usize 0 (by norm_num))

theorem toByteArray_write_preserves_read64_gap
    (w : UInt256) (mem : ByteArray) (off size : Nat)
    (hsize : mem.size = size) (hin : 96 ≤ size) (hbelow : 96 ≤ off)
    (hgap : off - size < USize.size) :
    ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  exact toByteArray_write_read_below_of_gap w mem off 64
    (by rw [hsize]; omega) hbelow (by rwa [hsize])

theorem t1StoredMem_read64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1216) := by
  rw [t1StoredMem]
  rw [toByteArray_write_preserves_read64 (t1ParsedWord I) (t0StoredMem I) 1184 1184
    (t0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [t0StoredMem]
  rw [toByteArray_write_preserves_read64 (t0ParsedWord I) (m15StoredMem I) 1152 1152
    (m15StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m15StoredMem]
  rw [toByteArray_write_preserves_read64 (m15ParsedWord I) (m14StoredMem I) 1120 1120
    (m14StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m14StoredMem]
  rw [toByteArray_write_preserves_read64 (m14ParsedWord I) (m13StoredMem I) 1088 1088
    (m13StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m13StoredMem]
  rw [toByteArray_write_preserves_read64 (m13ParsedWord I) (m12StoredMem I) 1056 1056
    (m12StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m12StoredMem]
  rw [toByteArray_write_preserves_read64 (m12ParsedWord I) (m11StoredMem I) 1024 1024
    (m11StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m11StoredMem]
  rw [toByteArray_write_preserves_read64 (m11ParsedWord I) (m10StoredMem I) 992 992
    (m10StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m10StoredMem]
  rw [toByteArray_write_preserves_read64 (m10ParsedWord I) (m9StoredMem I) 960 960
    (m9StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m9StoredMem]
  rw [toByteArray_write_preserves_read64 (m9ParsedWord I) (m8StoredMem I) 928 928
    (m8StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m8StoredMem]
  rw [toByteArray_write_preserves_read64 (m8ParsedWord I) (m7StoredMem I) 896 896
    (m7StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m7StoredMem]
  rw [toByteArray_write_preserves_read64 (m7ParsedWord I) (m6StoredMem I) 864 864
    (m6StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m6StoredMem]
  rw [toByteArray_write_preserves_read64 (m6ParsedWord I) (m5StoredMem I) 832 832
    (m5StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m5StoredMem]
  rw [toByteArray_write_preserves_read64 (m5ParsedWord I) (m4StoredMem I) 800 800
    (m4StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m4StoredMem]
  rw [toByteArray_write_preserves_read64 (m4ParsedWord I) (m3StoredMem I) 768 768
    (m3StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m3StoredMem]
  rw [toByteArray_write_preserves_read64 (m3ParsedWord I) (m2StoredMem I) 736 736
    (m2StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m2StoredMem]
  rw [toByteArray_write_preserves_read64 (m2ParsedWord I) (m1StoredMem I) 704 704
    (m1StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m1StoredMem]
  rw [toByteArray_write_preserves_read64 (m1ParsedWord I) (m0StoredMem I) 672 672
    (m0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [m0StoredMem]
  rw [toByteArray_write_preserves_read64 (m0ParsedWord I) (h7StoredMem I) 640 640
    (h7StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h7StoredMem]
  rw [toByteArray_write_preserves_read64 (h7ParsedWord I) (h6StoredMem I) 608 608
    (h6StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h6StoredMem]
  rw [toByteArray_write_preserves_read64 (h6ParsedWord I) (h5StoredMem I) 576 576
    (h5StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h5StoredMem]
  rw [toByteArray_write_preserves_read64 (h5ParsedWord I) (h4StoredMem I) 544 544
    (h4StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h4StoredMem]
  rw [toByteArray_write_preserves_read64 (h4ParsedWord I) (h3StoredMem I) 512 512
    (h3StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h3StoredMem]
  rw [toByteArray_write_preserves_read64 (h3ParsedWord I) (h2StoredMem I) 480 480
    (h2StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h2StoredMem]
  rw [toByteArray_write_preserves_read64 (h2ParsedWord I) (h1StoredMem I) 448 448
    (h1StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h1StoredMem]
  rw [toByteArray_write_preserves_read64 (h1ParsedWord I) (h0StoredMem I) 416 416
    (h0StoredMem_size I hlen) (by decide) (by decide) (by decide)]
  rw [h0StoredMem]
  rw [toByteArray_write_preserves_read64 (h0ParsedWord I) (tArrayZeroMem I) 384 405
    (tArrayZeroMem_size I hlen) (by decide) (by decide) (by decide)]
  exact tArrayZeroMem_read64 I hlen

end Blake2f
