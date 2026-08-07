import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopInit
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserValues
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords

/-!
# BLAKE2F positive-round initial memory facts

This file discharges concrete pieces of the initial `positiveRoundHeaderInvariant` for the two
setup memories.  The full initialization theorem still also needs the `h`, `m`, and `v` slot
relations, but the parsed `t0`/`t1` component is now proved for both final-flag cases.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem memorySlotStoresU64_of_readWithPadding_toByteArray
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (UInt256.ofNat w.toNat)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

theorem u256_land_u64_mask (w : UInt64) :
    UInt256.land (UInt256.ofNat w.toNat) (UInt256.ofNat 18446744073709551615) =
      UInt256.ofNat w.toNat := by
  cases w with | ofBitVec wb =>
  apply u256bv_inj
  rw [u256bv_land, u256bv_ofNat, u256bv_ofNat]
  simp
  bv_decide

theorem u256_xor_u64 (a b : UInt64) :
    UInt256.xor (UInt256.ofNat a.toNat) (UInt256.ofNat b.toNat) =
      UInt256.ofNat (a ^^^ b).toNat := by
  cases a with | ofBitVec ab =>
  cases b with | ofBitVec bb =>
  apply u256bv_inj
  rw [u256bv_xor, u256bv_ofNat, u256bv_ofNat, u256bv_ofNat]
  simp

theorem parsedFinalFlag_eq_false_of_byte_zero
    (I : ExecutionEnv) (hbyte : I.calldata[212]! = 0) :
    Model.parsedFinalFlag I.calldata = false := by
  unfold Model.parsedFinalFlag
  rw [hbyte]
  native_decide

theorem parsedFinalFlag_eq_true_of_byte_one
    (I : ExecutionEnv) (hbyte : I.calldata[212]! = 1) :
    Model.parsedFinalFlag I.calldata = true := by
  unfold Model.parsedFinalFlag
  rw [hbyte]
  native_decide

theorem toByteArray_write_preserves_readWithPadding32_below
    (word target : UInt256) (base : ByteArray) (writeOff readOff : Nat)
    (hbelow : readOff + 32 ≤ writeOff)
    (hgap : writeOff - base.size < USize.size)
    (hread : base.readWithPadding readOff 32 = UInt256.toByteArray target) :
    ((UInt256.toByteArray word).write 0 base writeOff 32).readWithPadding readOff 32 =
      UInt256.toByteArray target := by
  rw [toByteArray_write_read_below_len_padded_of_gap word base writeOff readOff 32
    hbelow (by decide) (by decide) hgap]
  exact hread

/-- The final-flag setup write is at byte offset `1920`; slots strictly below it are unchanged.

This is deliberately stated for arbitrary ranges, because the positive-round initialization should
not depend on a fixed-round unrolling. -/
theorem v14FinalFlagMem_readWithPadding_eq_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    {off len : Nat} (hoff : off + len ≤ 1920)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (v14FinalFlagMem I).readWithPadding off len =
      (v13MixedMem I).readWithPadding off len := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_len_padded_of_gap
    (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 off len
    (by omega) hpos hlen64
    (by rw [v13MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]

theorem memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    {off : Nat} (hoff : off + 32 ≤ 1920) {w : UInt64}
    (h : memorySlotStoresU64 (v13MixedMem I) off w) :
    memorySlotStoresU64 (v14FinalFlagMem I) off w := by
  unfold memorySlotStoresU64 memoryWord at *
  rw [v14FinalFlagMem_readWithPadding_eq_v13MixedMem I hlen hoff (by decide) (by decide)]
  exact h

theorem memoryRepresentsH_v14FinalFlagMem_of_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (h : memoryRepresentsH (v13MixedMem I) (Model.parsedH I.calldata)) :
    memoryRepresentsH (v14FinalFlagMem I) (Model.parsedH I.calldata) := by
  rcases h with ⟨hsize, hslots⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset i)
    (by unfold hSlotOffset hBaseOffset wordBytes; omega)
    (hslots i hi)

theorem memoryRepresentsM_v14FinalFlagMem_of_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (h : memoryRepresentsM (v13MixedMem I) (Model.parsedM I.calldata)) :
    memoryRepresentsM (v14FinalFlagMem I) (Model.parsedM I.calldata) := by
  rcases h with ⟨hsize, hslots⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset i)
    (by unfold mSlotOffset mBaseOffset wordBytes; omega)
    (hslots i hi)

theorem memoryRepresentsT_v14FinalFlagMem_of_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (h : memoryRepresentsT (v13MixedMem I) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata)) :
    memoryRepresentsT (v14FinalFlagMem I) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata) := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
      (off := tSlotOffset 0)
      (by unfold tSlotOffset tBaseOffset wordBytes; omega)
      h0
  · exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
      (off := tSlotOffset 1)
      (by unfold tSlotOffset tBaseOffset wordBytes; omega)
      h1

/-- The compression scratch/vector setup preserves every parser slot in `[384, 1216)`.

This covers all `h`, `m`, and `t` words needed for the initial positive-round invariant. -/
theorem v13MixedMem_readWithPadding_eq_t1StoredMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    {off len : Nat} (hoffLow : 96 ≤ off) (hoffHigh : off + len ≤ 1216)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (v13MixedMem I).readWithPadding off len =
      (t1StoredMem I).readWithPadding off len := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v13MixedWord I)
    (v12MixedMem I) 1888 off len (by omega) hpos hlen64
    (by rw [v12MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v12MixedWord I)
    (v15InitMem I) 1856 off len (by omega) hpos hlen64
    (by rw [v15InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v15InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 6620516959819538809)
    (v14InitMem I) 1952 off len (by omega) hpos hlen64
    (by rw [v14InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v14InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 2270897969802886507)
    (v13InitMem I) 1920 off len (by omega) hpos hlen64
    (by rw [v13InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v13InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 11170449401992604703)
    (v12InitMem I) 1888 off len (by omega) hpos hlen64
    (by rw [v12InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v12InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 5840696475078001361)
    (v11InitMem I) 1856 off len (by omega) hpos hlen64
    (by rw [v11InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v11InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 11912009170470909681)
    (v10InitMem I) 1824 off len (by omega) hpos hlen64
    (by rw [v10InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v10InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 4354685564936845355)
    (v9InitMem I) 1792 off len (by omega) hpos hlen64
    (by rw [v9InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v9InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 13503953896175478587)
    (v8InitMem I) 1760 off len (by omega) hpos hlen64
    (by rw [v8InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v8InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (UInt256.ofNat 7640891576956012808)
    (v7InitMem I) 1728 off len (by omega) hpos hlen64
    (by rw [v7InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v7InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v7StoredWord I)
    (v6InitMem I) 1696 off len (by omega) hpos hlen64
    (by rw [v6InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v6InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v6StoredWord I)
    (v5InitMem I) 1664 off len (by omega) hpos hlen64
    (by rw [v5InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v5InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v5StoredWord I)
    (v4InitMem I) 1632 off len (by omega) hpos hlen64
    (by rw [v4InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v4InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v4StoredWord I)
    (v3InitMem I) 1600 off len (by omega) hpos hlen64
    (by rw [v3InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v3InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v3StoredWord I)
    (v2InitMem I) 1568 off len (by omega) hpos hlen64
    (by rw [v2InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v2InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v2StoredWord I)
    (v1InitMem I) 1536 off len (by omega) hpos hlen64
    (by rw [v1InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v1InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v1StoredWord I)
    (v0InitMem I) 1504 off len (by omega) hpos hlen64
    (by rw [v0InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v0InitMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (v0StoredWord I)
    (compressionVAllocMem I) 1472 off len (by omega) hpos hlen64
    (by rw [compressionVAllocMem_size I hlen]; exact lt_usize 256 (by norm_num))]
  unfold compressionVAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1984))
    (compressionScratchZeroMem I) 64 off len
    (by rw [toByteArray_size])
    (by rw [compressionScratchZeroMem_size I hlen]; decide)
    (by omega)
    (by rw [compressionScratchZeroMem_size I hlen]; omega)
    hpos hlen64]
  have hsize : (compressionScratchAllocMem I).size = 1216 :=
    compressionScratchAllocMem_size I hlen
  unfold compressionScratchZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change (((ffi.ByteArray.zeroes 0).copySlice 0 (compressionScratchAllocMem I) 1216 0).readWithPadding
      off len =
    (t1StoredMem I).readWithPadding off len)
  rw [copySlice_read_below_gen]
  · unfold compressionScratchAllocMem
    rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1472))
      (t1StoredMem I) 64 off len
      (by rw [toByteArray_size])
      (by rw [t1StoredMem_size I hlen]; decide)
      (by omega)
      (by rw [t1StoredMem_size I hlen]; omega)
      hpos hlen64]
  · omega
  · rw [hsize]
    omega
  · exact hpos
  · exact hlen64

theorem t1StoredMem_read384
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 384 32 =
      UInt256.toByteArray (h0ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 384 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 384 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 384 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 384 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 384 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 384 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 384 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 384 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 384 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 384 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 384 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 384 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 384 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 384 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 384 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 384 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 384 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 384 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 384 32 (by decide) (by decide) (by decide)
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h6ParsedWord I)
    (h5StoredMem I) 576 384 32 (by decide) (by decide) (by decide)
    (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h5ParsedWord I)
    (h4StoredMem I) 544 384 32 (by decide) (by decide) (by decide)
    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h4ParsedWord I)
    (h3StoredMem I) 512 384 32 (by decide) (by decide) (by decide)
    (by rw [h3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h3ParsedWord I)
    (h2StoredMem I) 480 384 32 (by decide) (by decide) (by decide)
    (by rw [h2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h2ParsedWord I)
    (h1StoredMem I) 448 384 32 (by decide) (by decide) (by decide)
    (by rw [h1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h1ParsedWord I)
    (h0StoredMem I) 416 384 32 (by decide) (by decide) (by decide)
    (by rw [h0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h0StoredMem
  exact toByteArray_write_read_back_of_gap (h0ParsedWord I) (tArrayZeroMem I) 384
    (by rw [tArrayZeroMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read384
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 384 32 =
      UInt256.toByteArray (h0ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 384) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read384 I hlen

theorem memorySlotStoresH0_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 0)
      (Model.parsedH I.calldata)[0]! := by
  have hread := v13MixedMem_read384 I hlen
  rw [h0ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)] 
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH0_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 0)
      (Model.parsedH I.calldata)[0]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 0)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH0_v13MixedMem I hlen)

theorem t1StoredMem_read416
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 416 32 =
      UInt256.toByteArray (h1ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 416 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 416 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 416 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 416 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 416 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 416 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 416 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 416 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 416 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 416 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 416 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 416 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 416 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 416 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 416 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 416 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 416 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 416 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 416 32 (by decide) (by decide) (by decide)
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h6ParsedWord I)
    (h5StoredMem I) 576 416 32 (by decide) (by decide) (by decide)
    (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h5ParsedWord I)
    (h4StoredMem I) 544 416 32 (by decide) (by decide) (by decide)
    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h4ParsedWord I)
    (h3StoredMem I) 512 416 32 (by decide) (by decide) (by decide)
    (by rw [h3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h3ParsedWord I)
    (h2StoredMem I) 480 416 32 (by decide) (by decide) (by decide)
    (by rw [h2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h2ParsedWord I)
    (h1StoredMem I) 448 416 32 (by decide) (by decide) (by decide)
    (by rw [h1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h1StoredMem
  exact toByteArray_write_read_back_of_gap (h1ParsedWord I) (h0StoredMem I) 416
    (by rw [h0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read416
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 416 32 =
      UInt256.toByteArray (h1ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 416) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read416 I hlen

theorem memorySlotStoresH1_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 1)
      (Model.parsedH I.calldata)[1]! := by
  have hread := v13MixedMem_read416 I hlen
  rw [h1ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH1_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 1)
      (Model.parsedH I.calldata)[1]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 1)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH1_v13MixedMem I hlen)

theorem t1StoredMem_read448
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 448 32 =
      UInt256.toByteArray (h2ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 448 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 448 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 448 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 448 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 448 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 448 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 448 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 448 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 448 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 448 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 448 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 448 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 448 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 448 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 448 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 448 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 448 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 448 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 448 32 (by decide) (by decide) (by decide)
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h6ParsedWord I)
    (h5StoredMem I) 576 448 32 (by decide) (by decide) (by decide)
    (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h5ParsedWord I)
    (h4StoredMem I) 544 448 32 (by decide) (by decide) (by decide)
    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h4ParsedWord I)
    (h3StoredMem I) 512 448 32 (by decide) (by decide) (by decide)
    (by rw [h3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h3ParsedWord I)
    (h2StoredMem I) 480 448 32 (by decide) (by decide) (by decide)
    (by rw [h2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h2StoredMem
  exact toByteArray_write_read_back_of_gap (h2ParsedWord I) (h1StoredMem I) 448
    (by rw [h1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read448
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 448 32 =
      UInt256.toByteArray (h2ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 448) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read448 I hlen

theorem memorySlotStoresH2_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 2)
      (Model.parsedH I.calldata)[2]! := by
  have hread := v13MixedMem_read448 I hlen
  rw [h2ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH2_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 2)
      (Model.parsedH I.calldata)[2]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 2)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH2_v13MixedMem I hlen)

theorem t1StoredMem_read480
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 480 32 =
      UInt256.toByteArray (h3ParsedWord I) := by
  unfold t1StoredMem
  exact toByteArray_write_preserves_readWithPadding32_below
    (t1ParsedWord I) (h3ParsedWord I) (t0StoredMem I) 1184 480
    (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
    (by
      unfold t0StoredMem
      exact toByteArray_write_preserves_readWithPadding32_below
        (t0ParsedWord I) (h3ParsedWord I) (m15StoredMem I) 1152 480
        (by decide)
        (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
        (by
          unfold m15StoredMem
          exact toByteArray_write_preserves_readWithPadding32_below
            (m15ParsedWord I) (h3ParsedWord I) (m14StoredMem I) 1120 480
            (by decide)
            (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
            (by
              unfold m14StoredMem
              exact toByteArray_write_preserves_readWithPadding32_below
                (m14ParsedWord I) (h3ParsedWord I) (m13StoredMem I) 1088 480
                (by decide)
                (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                (by
                  unfold m13StoredMem
                  exact toByteArray_write_preserves_readWithPadding32_below
                    (m13ParsedWord I) (h3ParsedWord I) (m12StoredMem I) 1056 480
                    (by decide)
                    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                    (by
                      unfold m12StoredMem
                      exact toByteArray_write_preserves_readWithPadding32_below
                        (m12ParsedWord I) (h3ParsedWord I) (m11StoredMem I) 1024 480
                        (by decide)
                        (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                        (by
                          unfold m11StoredMem
                          exact toByteArray_write_preserves_readWithPadding32_below
                            (m11ParsedWord I) (h3ParsedWord I) (m10StoredMem I) 992 480
                            (by decide)
                            (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                            (by
                              unfold m10StoredMem
                              exact toByteArray_write_preserves_readWithPadding32_below
                                (m10ParsedWord I) (h3ParsedWord I) (m9StoredMem I) 960 480
                                (by decide)
                                (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                (by
                                  unfold m9StoredMem
                                  exact toByteArray_write_preserves_readWithPadding32_below
                                    (m9ParsedWord I) (h3ParsedWord I) (m8StoredMem I) 928 480
                                    (by decide)
                                    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                    (by
                                      unfold m8StoredMem
                                      exact toByteArray_write_preserves_readWithPadding32_below
                                        (m8ParsedWord I) (h3ParsedWord I) (m7StoredMem I) 896 480
                                        (by decide)
                                        (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                        (by
                                          unfold m7StoredMem
                                          exact toByteArray_write_preserves_readWithPadding32_below
                                            (m7ParsedWord I) (h3ParsedWord I) (m6StoredMem I) 864 480
                                            (by decide)
                                            (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                            (by
                                              unfold m6StoredMem
                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                (m6ParsedWord I) (h3ParsedWord I) (m5StoredMem I) 832 480
                                                (by decide)
                                                (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                (by
                                                  unfold m5StoredMem
                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                    (m5ParsedWord I) (h3ParsedWord I) (m4StoredMem I) 800 480
                                                    (by decide)
                                                    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                    (by
                                                      unfold m4StoredMem
                                                      exact toByteArray_write_preserves_readWithPadding32_below
                                                        (m4ParsedWord I) (h3ParsedWord I) (m3StoredMem I) 768 480
                                                        (by decide)
                                                        (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                        (by
                                                          unfold m3StoredMem
                                                          exact toByteArray_write_preserves_readWithPadding32_below
                                                            (m3ParsedWord I) (h3ParsedWord I) (m2StoredMem I) 736 480
                                                            (by decide)
                                                            (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                            (by
                                                              unfold m2StoredMem
                                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                                (m2ParsedWord I) (h3ParsedWord I) (m1StoredMem I) 704 480
                                                                (by decide)
                                                                (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                (by
                                                                  unfold m1StoredMem
                                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                                    (m1ParsedWord I) (h3ParsedWord I) (m0StoredMem I) 672 480
                                                                    (by decide)
                                                                    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                    (by
                                                                      unfold m0StoredMem
                                                                      exact toByteArray_write_preserves_readWithPadding32_below
                                                                        (m0ParsedWord I) (h3ParsedWord I) (h7StoredMem I) 640 480
                                                                        (by decide)
                                                                        (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                        (by
                                                                          unfold h7StoredMem
                                                                          exact toByteArray_write_preserves_readWithPadding32_below
                                                                            (h7ParsedWord I) (h3ParsedWord I) (h6StoredMem I) 608 480
                                                                            (by decide)
                                                                            (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                            (by
                                                                              unfold h6StoredMem
                                                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                                                (h6ParsedWord I) (h3ParsedWord I) (h5StoredMem I) 576 480
                                                                                (by decide)
                                                                                (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                                (by
                                                                                  unfold h5StoredMem
                                                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                                                    (h5ParsedWord I) (h3ParsedWord I) (h4StoredMem I) 544 480
                                                                                    (by decide)
                                                                                    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                                    (by
                                                                                      unfold h4StoredMem
                                                                                      exact toByteArray_write_preserves_readWithPadding32_below
                                                                                        (h4ParsedWord I) (h3ParsedWord I) (h3StoredMem I) 512 480
                                                                                        (by decide)
                                                                                        (by rw [h3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                                        (by
                                                                                          unfold h3StoredMem
                                                                                          exact toByteArray_write_read_back_of_gap (h3ParsedWord I) (h2StoredMem I) 480
                                                                                            (by rw [h2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))))))))))))))))))))))))

theorem v13MixedMem_read480
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 480 32 =
      UInt256.toByteArray (h3ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 480) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read480 I hlen

theorem memorySlotStoresH3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 3)
      (Model.parsedH I.calldata)[3]! := by
  have hread := v13MixedMem_read480 I hlen
  rw [h3ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH3_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 3)
      (Model.parsedH I.calldata)[3]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 3)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH3_v13MixedMem I hlen)

theorem t1StoredMem_read512
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 512 32 =
      UInt256.toByteArray (h4ParsedWord I) := by
  unfold t1StoredMem
  exact toByteArray_write_preserves_readWithPadding32_below
    (t1ParsedWord I) (h4ParsedWord I) (t0StoredMem I) 1184 512
    (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
    (by
      unfold t0StoredMem
      exact toByteArray_write_preserves_readWithPadding32_below
        (t0ParsedWord I) (h4ParsedWord I) (m15StoredMem I) 1152 512
        (by decide)
        (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
        (by
          unfold m15StoredMem
          exact toByteArray_write_preserves_readWithPadding32_below
            (m15ParsedWord I) (h4ParsedWord I) (m14StoredMem I) 1120 512
            (by decide)
            (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
            (by
              unfold m14StoredMem
              exact toByteArray_write_preserves_readWithPadding32_below
                (m14ParsedWord I) (h4ParsedWord I) (m13StoredMem I) 1088 512
                (by decide)
                (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                (by
                  unfold m13StoredMem
                  exact toByteArray_write_preserves_readWithPadding32_below
                    (m13ParsedWord I) (h4ParsedWord I) (m12StoredMem I) 1056 512
                    (by decide)
                    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                    (by
                      unfold m12StoredMem
                      exact toByteArray_write_preserves_readWithPadding32_below
                        (m12ParsedWord I) (h4ParsedWord I) (m11StoredMem I) 1024 512
                        (by decide)
                        (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                        (by
                          unfold m11StoredMem
                          exact toByteArray_write_preserves_readWithPadding32_below
                            (m11ParsedWord I) (h4ParsedWord I) (m10StoredMem I) 992 512
                            (by decide)
                            (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                            (by
                              unfold m10StoredMem
                              exact toByteArray_write_preserves_readWithPadding32_below
                                (m10ParsedWord I) (h4ParsedWord I) (m9StoredMem I) 960 512
                                (by decide)
                                (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                (by
                                  unfold m9StoredMem
                                  exact toByteArray_write_preserves_readWithPadding32_below
                                    (m9ParsedWord I) (h4ParsedWord I) (m8StoredMem I) 928 512
                                    (by decide)
                                    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                    (by
                                      unfold m8StoredMem
                                      exact toByteArray_write_preserves_readWithPadding32_below
                                        (m8ParsedWord I) (h4ParsedWord I) (m7StoredMem I) 896 512
                                        (by decide)
                                        (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                        (by
                                          unfold m7StoredMem
                                          exact toByteArray_write_preserves_readWithPadding32_below
                                            (m7ParsedWord I) (h4ParsedWord I) (m6StoredMem I) 864 512
                                            (by decide)
                                            (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                            (by
                                              unfold m6StoredMem
                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                (m6ParsedWord I) (h4ParsedWord I) (m5StoredMem I) 832 512
                                                (by decide)
                                                (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                (by
                                                  unfold m5StoredMem
                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                    (m5ParsedWord I) (h4ParsedWord I) (m4StoredMem I) 800 512
                                                    (by decide)
                                                    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                    (by
                                                      unfold m4StoredMem
                                                      exact toByteArray_write_preserves_readWithPadding32_below
                                                        (m4ParsedWord I) (h4ParsedWord I) (m3StoredMem I) 768 512
                                                        (by decide)
                                                        (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                        (by
                                                          unfold m3StoredMem
                                                          exact toByteArray_write_preserves_readWithPadding32_below
                                                            (m3ParsedWord I) (h4ParsedWord I) (m2StoredMem I) 736 512
                                                            (by decide)
                                                            (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                            (by
                                                              unfold m2StoredMem
                                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                                (m2ParsedWord I) (h4ParsedWord I) (m1StoredMem I) 704 512
                                                                (by decide)
                                                                (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                (by
                                                                  unfold m1StoredMem
                                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                                    (m1ParsedWord I) (h4ParsedWord I) (m0StoredMem I) 672 512
                                                                    (by decide)
                                                                    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                    (by
                                                                      unfold m0StoredMem
                                                                      exact toByteArray_write_preserves_readWithPadding32_below
                                                                        (m0ParsedWord I) (h4ParsedWord I) (h7StoredMem I) 640 512
                                                                        (by decide)
                                                                        (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                        (by
                                                                          unfold h7StoredMem
                                                                          exact toByteArray_write_preserves_readWithPadding32_below
                                                                            (h7ParsedWord I) (h4ParsedWord I) (h6StoredMem I) 608 512
                                                                            (by decide)
                                                                            (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                            (by
                                                                              unfold h6StoredMem
                                                                              exact toByteArray_write_preserves_readWithPadding32_below
                                                                                (h6ParsedWord I) (h4ParsedWord I) (h5StoredMem I) 576 512
                                                                                (by decide)
                                                                                (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                                (by
                                                                                  unfold h5StoredMem
                                                                                  exact toByteArray_write_preserves_readWithPadding32_below
                                                                                    (h5ParsedWord I) (h4ParsedWord I) (h4StoredMem I) 544 512
                                                                                    (by decide)
                                                                                    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))
                                                                                    (by
                                                                                      unfold h4StoredMem
                                                                                      exact toByteArray_write_read_back_of_gap (h4ParsedWord I) (h3StoredMem I) 512
                                                                                        (by rw [h3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num)))))))))))))))))))))))

theorem v13MixedMem_read512
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 512 32 =
      UInt256.toByteArray (h4ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 512) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read512 I hlen

theorem memorySlotStoresH4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 4)
      (Model.parsedH I.calldata)[4]! := by
  have hread := v13MixedMem_read512 I hlen
  rw [h4ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH4_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 4)
      (Model.parsedH I.calldata)[4]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 4)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH4_v13MixedMem I hlen)

theorem t1StoredMem_read544
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 544 32 =
      UInt256.toByteArray (h5ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 544 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 544 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 544 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 544 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 544 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 544 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 544 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 544 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 544 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 544 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 544 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 544 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 544 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 544 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 544 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 544 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 544 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 544 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 544 32 (by decide) (by decide) (by decide)
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h6ParsedWord I)
    (h5StoredMem I) 576 544 32 (by decide) (by decide) (by decide)
    (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h5StoredMem
  exact toByteArray_write_read_back_of_gap (h5ParsedWord I) (h4StoredMem I) 544
    (by rw [h4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read544
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 544 32 =
      UInt256.toByteArray (h5ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 544) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read544 I hlen

theorem memorySlotStoresH5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 5)
      (Model.parsedH I.calldata)[5]! := by
  have hread := v13MixedMem_read544 I hlen
  rw [h5ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 5)
      (Model.parsedH I.calldata)[5]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 5)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH5_v13MixedMem I hlen)

theorem t1StoredMem_read576
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 576 32 =
      UInt256.toByteArray (h6ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 576 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 576 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 576 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 576 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 576 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 576 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 576 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 576 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 576 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 576 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 576 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 576 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 576 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 576 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 576 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 576 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 576 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 576 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [h7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (h7ParsedWord I)
    (h6StoredMem I) 608 576 32 (by decide) (by decide) (by decide)
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h6StoredMem
  exact toByteArray_write_read_back_of_gap (h6ParsedWord I) (h5StoredMem I) 576
    (by rw [h5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read576
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 576 32 =
      UInt256.toByteArray (h6ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 576) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read576 I hlen

theorem memorySlotStoresH6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 6)
      (Model.parsedH I.calldata)[6]! := by
  have hread := v13MixedMem_read576 I hlen
  rw [h6ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 6)
      (Model.parsedH I.calldata)[6]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 6)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH6_v13MixedMem I hlen)

theorem t1StoredMem_read608
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 608 32 =
      UInt256.toByteArray (h7ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 608 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 608 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 608 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 608 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 608 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 608 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 608 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 608 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 608 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 608 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 608 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 608 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 608 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 608 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 608 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 608 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 608 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m0ParsedWord I)
    (h7StoredMem I) 640 608 32 (by decide) (by decide) (by decide)
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold h7StoredMem
  exact toByteArray_write_read_back_of_gap (h7ParsedWord I) (h6StoredMem I) 608
    (by rw [h6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read608
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 608 32 =
      UInt256.toByteArray (h7ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 608) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read608 I hlen

theorem memorySlotStoresH7_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (hSlotOffset 7)
      (Model.parsedH I.calldata)[7]! := by
  have hread := v13MixedMem_read608 I hlen
  rw [h7ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedH_getElem! I.calldata (by decide)]
  unfold hSlotOffset hBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresH7_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (hSlotOffset 7)
      (Model.parsedH I.calldata)[7]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := hSlotOffset 7)
    (by unfold hSlotOffset hBaseOffset wordBytes; decide)
    (memorySlotStoresH7_v13MixedMem I hlen)

theorem memoryRepresentsH_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsH (v13MixedMem I) (Model.parsedH I.calldata) := by
  constructor
  · exact Model.parsedH_size I.calldata
  · intro i hi
    interval_cases i
    · exact memorySlotStoresH0_v13MixedMem I hlen
    · exact memorySlotStoresH1_v13MixedMem I hlen
    · exact memorySlotStoresH2_v13MixedMem I hlen
    · exact memorySlotStoresH3_v13MixedMem I hlen
    · exact memorySlotStoresH4_v13MixedMem I hlen
    · exact memorySlotStoresH5_v13MixedMem I hlen
    · exact memorySlotStoresH6_v13MixedMem I hlen
    · exact memorySlotStoresH7_v13MixedMem I hlen

theorem memoryRepresentsH_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsH (v14FinalFlagMem I) (Model.parsedH I.calldata) :=
  memoryRepresentsH_v14FinalFlagMem_of_v13MixedMem I hlen
    (memoryRepresentsH_v13MixedMem I hlen)

theorem t1StoredMem_read1120
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 1120 32 =
      UInt256.toByteArray (m15ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 1120 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 1120 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m15StoredMem
  exact toByteArray_write_read_back_of_gap (m15ParsedWord I) (m14StoredMem I) 1120
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read1120
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1120 32 =
      UInt256.toByteArray (m15ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 1120) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read1120 I hlen

theorem memorySlotStoresM15_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 15)
      (Model.parsedM I.calldata)[15]! := by
  have hread := v13MixedMem_read1120 I hlen
  rw [m15ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM15_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 15)
      (Model.parsedM I.calldata)[15]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 15)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM15_v13MixedMem I hlen)

theorem t1StoredMem_read1088
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 1088 32 =
      UInt256.toByteArray (m14ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 1088 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 1088 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 1088 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m14StoredMem
  exact toByteArray_write_read_back_of_gap (m14ParsedWord I) (m13StoredMem I) 1088
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read1088
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1088 32 =
      UInt256.toByteArray (m14ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 1088) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read1088 I hlen

theorem memorySlotStoresM14_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 14)
      (Model.parsedM I.calldata)[14]! := by
  have hread := v13MixedMem_read1088 I hlen
  rw [m14ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM14_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 14)
      (Model.parsedM I.calldata)[14]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 14)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM14_v13MixedMem I hlen)

theorem t1StoredMem_read1056
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 1056 32 =
      UInt256.toByteArray (m13ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 1056 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 1056 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 1056 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 1056 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m13StoredMem
  exact toByteArray_write_read_back_of_gap (m13ParsedWord I) (m12StoredMem I) 1056
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read1056
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1056 32 =
      UInt256.toByteArray (m13ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 1056) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read1056 I hlen

theorem memorySlotStoresM13_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 13)
      (Model.parsedM I.calldata)[13]! := by
  have hread := v13MixedMem_read1056 I hlen
  rw [m13ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM13_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 13)
      (Model.parsedM I.calldata)[13]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 13)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM13_v13MixedMem I hlen)

theorem t1StoredMem_read1024
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 1024 32 =
      UInt256.toByteArray (m12ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 1024 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 1024 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 1024 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 1024 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 1024 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m12StoredMem
  exact toByteArray_write_read_back_of_gap (m12ParsedWord I) (m11StoredMem I) 1024
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read1024
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1024 32 =
      UInt256.toByteArray (m12ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 1024) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read1024 I hlen

theorem memorySlotStoresM12_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 12)
      (Model.parsedM I.calldata)[12]! := by
  have hread := v13MixedMem_read1024 I hlen
  rw [m12ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM12_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 12)
      (Model.parsedM I.calldata)[12]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 12)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM12_v13MixedMem I hlen)

theorem t1StoredMem_read992
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 992 32 =
      UInt256.toByteArray (m11ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 992 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 992 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 992 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 992 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 992 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 992 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m11StoredMem
  exact toByteArray_write_read_back_of_gap (m11ParsedWord I) (m10StoredMem I) 992
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read992
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 992 32 =
      UInt256.toByteArray (m11ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 992) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read992 I hlen

theorem memorySlotStoresM11_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 11)
      (Model.parsedM I.calldata)[11]! := by
  have hread := v13MixedMem_read992 I hlen
  rw [m11ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM11_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 11)
      (Model.parsedM I.calldata)[11]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 11)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM11_v13MixedMem I hlen)

theorem t1StoredMem_read960
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 960 32 =
      UInt256.toByteArray (m10ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 960 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 960 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 960 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 960 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 960 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 960 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 960 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m10StoredMem
  exact toByteArray_write_read_back_of_gap (m10ParsedWord I) (m9StoredMem I) 960
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read960
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 960 32 =
      UInt256.toByteArray (m10ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 960) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read960 I hlen

theorem memorySlotStoresM10_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 10)
      (Model.parsedM I.calldata)[10]! := by
  have hread := v13MixedMem_read960 I hlen
  rw [m10ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM10_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 10)
      (Model.parsedM I.calldata)[10]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 10)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM10_v13MixedMem I hlen)

theorem t1StoredMem_read928
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 928 32 =
      UInt256.toByteArray (m9ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 928 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 928 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 928 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 928 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 928 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 928 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 928 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 928 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m9StoredMem
  exact toByteArray_write_read_back_of_gap (m9ParsedWord I) (m8StoredMem I) 928
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read928
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 928 32 =
      UInt256.toByteArray (m9ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 928) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read928 I hlen

theorem memorySlotStoresM9_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 9)
      (Model.parsedM I.calldata)[9]! := by
  have hread := v13MixedMem_read928 I hlen
  rw [m9ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM9_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 9)
      (Model.parsedM I.calldata)[9]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 9)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM9_v13MixedMem I hlen)

theorem t1StoredMem_read896
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 896 32 =
      UInt256.toByteArray (m8ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 896 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 896 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 896 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 896 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 896 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 896 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 896 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 896 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 896 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m8StoredMem
  exact toByteArray_write_read_back_of_gap (m8ParsedWord I) (m7StoredMem I) 896
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read896
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 896 32 =
      UInt256.toByteArray (m8ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 896) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read896 I hlen

theorem memorySlotStoresM8_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 8)
      (Model.parsedM I.calldata)[8]! := by
  have hread := v13MixedMem_read896 I hlen
  rw [m8ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM8_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 8)
      (Model.parsedM I.calldata)[8]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 8)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM8_v13MixedMem I hlen)

theorem t1StoredMem_read864
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 864 32 =
      UInt256.toByteArray (m7ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 864 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 864 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 864 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 864 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 864 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 864 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 864 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 864 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 864 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 864 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m7StoredMem
  exact toByteArray_write_read_back_of_gap (m7ParsedWord I) (m6StoredMem I) 864
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read864
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 864 32 =
      UInt256.toByteArray (m7ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 864) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read864 I hlen

theorem memorySlotStoresM7_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 7)
      (Model.parsedM I.calldata)[7]! := by
  have hread := v13MixedMem_read864 I hlen
  rw [m7ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM7_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 7)
      (Model.parsedM I.calldata)[7]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 7)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM7_v13MixedMem I hlen)

theorem t1StoredMem_read832
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 832 32 =
      UInt256.toByteArray (m6ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 832 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 832 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 832 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 832 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 832 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 832 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 832 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 832 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 832 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 832 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 832 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m6StoredMem
  exact toByteArray_write_read_back_of_gap (m6ParsedWord I) (m5StoredMem I) 832
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read832
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 832 32 =
      UInt256.toByteArray (m6ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 832) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read832 I hlen

theorem memorySlotStoresM6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 6)
      (Model.parsedM I.calldata)[6]! := by
  have hread := v13MixedMem_read832 I hlen
  rw [m6ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 6)
      (Model.parsedM I.calldata)[6]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 6)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM6_v13MixedMem I hlen)

theorem t1StoredMem_read800
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 800 32 =
      UInt256.toByteArray (m5ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 800 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 800 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 800 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 800 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 800 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 800 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 800 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 800 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 800 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 800 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 800 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 800 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m5StoredMem
  exact toByteArray_write_read_back_of_gap (m5ParsedWord I) (m4StoredMem I) 800
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read800
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 800 32 =
      UInt256.toByteArray (m5ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 800) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read800 I hlen

theorem memorySlotStoresM5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 5)
      (Model.parsedM I.calldata)[5]! := by
  have hread := v13MixedMem_read800 I hlen
  rw [m5ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 5)
      (Model.parsedM I.calldata)[5]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 5)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM5_v13MixedMem I hlen)

theorem t1StoredMem_read768
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 768 32 =
      UInt256.toByteArray (m4ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 768 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 768 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 768 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 768 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 768 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 768 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 768 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 768 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 768 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 768 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 768 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 768 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 768 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m4StoredMem
  exact toByteArray_write_read_back_of_gap (m4ParsedWord I) (m3StoredMem I) 768
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read768
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 768 32 =
      UInt256.toByteArray (m4ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 768) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read768 I hlen

theorem memorySlotStoresM4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 4)
      (Model.parsedM I.calldata)[4]! := by
  have hread := v13MixedMem_read768 I hlen
  rw [m4ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM4_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 4)
      (Model.parsedM I.calldata)[4]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 4)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM4_v13MixedMem I hlen)

theorem t1StoredMem_read736
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 736 32 =
      UInt256.toByteArray (m3ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 736 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 736 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 736 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 736 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 736 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 736 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 736 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 736 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 736 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 736 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 736 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 736 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 736 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 736 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m3StoredMem
  exact toByteArray_write_read_back_of_gap (m3ParsedWord I) (m2StoredMem I) 736
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read736
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 736 32 =
      UInt256.toByteArray (m3ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 736) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read736 I hlen

theorem memorySlotStoresM3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 3)
      (Model.parsedM I.calldata)[3]! := by
  have hread := v13MixedMem_read736 I hlen
  rw [m3ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM3_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 3)
      (Model.parsedM I.calldata)[3]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 3)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM3_v13MixedMem I hlen)

theorem t1StoredMem_read704
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 704 32 =
      UInt256.toByteArray (m2ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 704 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 704 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 704 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 704 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 704 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 704 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 704 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 704 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 704 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 704 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 704 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 704 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 704 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 704 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 704 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m2StoredMem
  exact toByteArray_write_read_back_of_gap (m2ParsedWord I) (m1StoredMem I) 704
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read704
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 704 32 =
      UInt256.toByteArray (m2ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 704) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read704 I hlen

theorem memorySlotStoresM2_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 2)
      (Model.parsedM I.calldata)[2]! := by
  have hread := v13MixedMem_read704 I hlen
  rw [m2ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM2_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 2)
      (Model.parsedM I.calldata)[2]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 2)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM2_v13MixedMem I hlen)

theorem t1StoredMem_read672
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 672 32 =
      UInt256.toByteArray (m1ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 672 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 672 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 672 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 672 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 672 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 672 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 672 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 672 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 672 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 672 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 672 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 672 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 672 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 672 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 672 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 672 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m1StoredMem
  exact toByteArray_write_read_back_of_gap (m1ParsedWord I) (m0StoredMem I) 672
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read672
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 672 32 =
      UInt256.toByteArray (m1ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 672) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read672 I hlen

theorem memorySlotStoresM1_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 1)
      (Model.parsedM I.calldata)[1]! := by
  have hread := v13MixedMem_read672 I hlen
  rw [m1ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM1_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 1)
      (Model.parsedM I.calldata)[1]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 1)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM1_v13MixedMem I hlen)

theorem t1StoredMem_read640
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t1StoredMem I).readWithPadding 640 32 =
      UInt256.toByteArray (m0ParsedWord I) := by
  rw [t1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t1ParsedWord I)
    (t0StoredMem I) 1184 640 32 (by decide) (by decide) (by decide)
    (by rw [t0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [t0StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 640 32 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m15StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m15ParsedWord I)
    (m14StoredMem I) 1120 640 32 (by decide) (by decide) (by decide)
    (by rw [m14StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m14StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m14ParsedWord I)
    (m13StoredMem I) 1088 640 32 (by decide) (by decide) (by decide)
    (by rw [m13StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m13StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m13ParsedWord I)
    (m12StoredMem I) 1056 640 32 (by decide) (by decide) (by decide)
    (by rw [m12StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m12StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m12ParsedWord I)
    (m11StoredMem I) 1024 640 32 (by decide) (by decide) (by decide)
    (by rw [m11StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m11StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m11ParsedWord I)
    (m10StoredMem I) 992 640 32 (by decide) (by decide) (by decide)
    (by rw [m10StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m10StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m10ParsedWord I)
    (m9StoredMem I) 960 640 32 (by decide) (by decide) (by decide)
    (by rw [m9StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m9StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m9ParsedWord I)
    (m8StoredMem I) 928 640 32 (by decide) (by decide) (by decide)
    (by rw [m8StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m8StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m8ParsedWord I)
    (m7StoredMem I) 896 640 32 (by decide) (by decide) (by decide)
    (by rw [m7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m7StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m7ParsedWord I)
    (m6StoredMem I) 864 640 32 (by decide) (by decide) (by decide)
    (by rw [m6StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m6StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m6ParsedWord I)
    (m5StoredMem I) 832 640 32 (by decide) (by decide) (by decide)
    (by rw [m5StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m5StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m5ParsedWord I)
    (m4StoredMem I) 800 640 32 (by decide) (by decide) (by decide)
    (by rw [m4StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m4StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m4ParsedWord I)
    (m3StoredMem I) 768 640 32 (by decide) (by decide) (by decide)
    (by rw [m3StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m3StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m3ParsedWord I)
    (m2StoredMem I) 736 640 32 (by decide) (by decide) (by decide)
    (by rw [m2StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m2StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m2ParsedWord I)
    (m1StoredMem I) 704 640 32 (by decide) (by decide) (by decide)
    (by rw [m1StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [m1StoredMem]
  rw [toByteArray_write_read_below_len_padded_of_gap (m1ParsedWord I)
    (m0StoredMem I) 672 640 32 (by decide) (by decide) (by decide)
    (by rw [m0StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  unfold m0StoredMem
  exact toByteArray_write_read_back_of_gap (m0ParsedWord I) (h7StoredMem I) 640
    (by rw [h7StoredMem_size I hlen]; exact lt_usize 0 (by norm_num))

theorem v13MixedMem_read640
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 640 32 =
      UInt256.toByteArray (m0ParsedWord I) := by
  rw [v13MixedMem_readWithPadding_eq_t1StoredMem I hlen
    (off := 640) (len := 32) (by decide) (by decide) (by decide) (by decide)]
  exact t1StoredMem_read640 I hlen

theorem memorySlotStoresM0_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (mSlotOffset 0)
      (Model.parsedM I.calldata)[0]! := by
  have hread := v13MixedMem_read640 I hlen
  rw [m0ParsedWord_eq_readLE64 I hlen] at hread
  rw [Model.parsedM_getElem! I.calldata (by decide)]
  unfold mSlotOffset mBaseOffset wordBytes
  exact memorySlotStoresU64_of_readWithPadding_toByteArray hread

theorem memorySlotStoresM0_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (mSlotOffset 0)
      (Model.parsedM I.calldata)[0]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := mSlotOffset 0)
    (by unfold mSlotOffset mBaseOffset wordBytes; decide)
    (memorySlotStoresM0_v13MixedMem I hlen)

theorem memoryRepresentsM_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsM (v13MixedMem I) (Model.parsedM I.calldata) := by
  constructor
  · exact Model.parsedM_size I.calldata
  · intro i hi
    interval_cases i
    · exact memorySlotStoresM0_v13MixedMem I hlen
    · exact memorySlotStoresM1_v13MixedMem I hlen
    · exact memorySlotStoresM2_v13MixedMem I hlen
    · exact memorySlotStoresM3_v13MixedMem I hlen
    · exact memorySlotStoresM4_v13MixedMem I hlen
    · exact memorySlotStoresM5_v13MixedMem I hlen
    · exact memorySlotStoresM6_v13MixedMem I hlen
    · exact memorySlotStoresM7_v13MixedMem I hlen
    · exact memorySlotStoresM8_v13MixedMem I hlen
    · exact memorySlotStoresM9_v13MixedMem I hlen
    · exact memorySlotStoresM10_v13MixedMem I hlen
    · exact memorySlotStoresM11_v13MixedMem I hlen
    · exact memorySlotStoresM12_v13MixedMem I hlen
    · exact memorySlotStoresM13_v13MixedMem I hlen
    · exact memorySlotStoresM14_v13MixedMem I hlen
    · exact memorySlotStoresM15_v13MixedMem I hlen

theorem memoryRepresentsM_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsM (v14FinalFlagMem I) (Model.parsedM I.calldata) :=
  memoryRepresentsM_v14FinalFlagMem_of_v13MixedMem I hlen
    (memoryRepresentsM_v13MixedMem I hlen)

theorem v0StoredWord_eq_initialV0
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v0StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[0]!).toNat := by
  have hsrc := memorySlotStoresH0_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  change outputH0LoadWord (v13MixedMem I) =
    UInt256.ofNat ((Model.parsedH I.calldata)[0]!).toNat at hsrc
  rw [outputH0LoadWord_v13MixedMem I hlen] at hsrc
  unfold v0StoredWord
  rw [hsrc]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[0]!)

theorem memorySlotStoresV0_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 0)
      (positiveRoundModelState I.calldata 0)[0]! := by
  have hv0 := v0StoredWord_eq_initialV0 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  change outputV0LoadWord (v13MixedMem I) =
    UInt256.ofNat ((positiveRoundModelState I.calldata 0)[0]!).toNat
  rw [outputV0LoadWord_v13MixedMem I hlen, hv0]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV0_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 0)
      (positiveRoundModelState I.calldata 0)[0]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 0)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV0_v13MixedMem I hlen)

theorem v1StoredWord_eq_initialV1
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v1StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[1]!).toNat := by
  have hsrc := memorySlotStoresH1_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  change outputH1LoadWord (v13MixedMem I) =
    UInt256.ofNat ((Model.parsedH I.calldata)[1]!).toNat at hsrc
  rw [outputH1LoadWord_v13MixedMem I hlen] at hsrc
  unfold v1StoredWord
  rw [hsrc]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[1]!)

theorem memorySlotStoresV1_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 1)
      (positiveRoundModelState I.calldata 0)[1]! := by
  have hv1 := v1StoredWord_eq_initialV1 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  change outputV1LoadWord (v13MixedMem I) =
    UInt256.ofNat ((positiveRoundModelState I.calldata 0)[1]!).toNat
  rw [outputV1LoadWord_v13MixedMem I hlen, hv1]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV1_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 1)
      (positiveRoundModelState I.calldata 0)[1]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 1)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV1_v13MixedMem I hlen)

theorem v2StoredWord_eq_initialV2
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v2StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[2]!).toNat := by
  have hsrc := memorySlotStoresH2_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  change outputH2LoadWord (v13MixedMem I) =
    UInt256.ofNat ((Model.parsedH I.calldata)[2]!).toNat at hsrc
  rw [outputH2LoadWord_v13MixedMem I hlen] at hsrc
  unfold v2StoredWord
  rw [hsrc]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[2]!)

theorem memorySlotStoresV2_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 2)
      (positiveRoundModelState I.calldata 0)[2]! := by
  have hv2 := v2StoredWord_eq_initialV2 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  change outputV2LoadWord (v13MixedMem I) =
    UInt256.ofNat ((positiveRoundModelState I.calldata 0)[2]!).toNat
  rw [outputV2LoadWord_v13MixedMem I hlen, hv2]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV2_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 2)
      (positiveRoundModelState I.calldata 0)[2]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 2)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV2_v13MixedMem I hlen)

theorem v3StoredWord_eq_initialV3
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v3StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[3]!).toNat := by
  have hsrc := memorySlotStoresH3_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  change outputH3LoadWord (v13MixedMem I) =
    UInt256.ofNat ((Model.parsedH I.calldata)[3]!).toNat at hsrc
  rw [outputH3LoadWord_v13MixedMem I hlen] at hsrc
  unfold v3StoredWord
  rw [hsrc]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[3]!)

theorem memorySlotStoresV3_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 3)
      (positiveRoundModelState I.calldata 0)[3]! := by
  have hv3 := v3StoredWord_eq_initialV3 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  change outputV3LoadWord (v13MixedMem I) =
    UInt256.ofNat ((positiveRoundModelState I.calldata 0)[3]!).toNat
  rw [outputV3LoadWord_v13MixedMem I hlen, hv3]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV3_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 3)
      (positiveRoundModelState I.calldata 0)[3]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 3)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV3_v13MixedMem I hlen)

theorem v4StoredWord_eq_initialV4
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v4StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[4]!).toNat := by
  have hsrc := memorySlotStoresH4_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  unfold v4StoredWord
  have hload : v4LoadWord I = UInt256.ofNat ((Model.parsedH I.calldata)[4]!).toNat := by
    unfold v4LoadWord
    rw [← v13MixedMem_read512_eq_v3InitMem I hlen]
    exact hsrc
  rw [hload]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[4]!)

theorem memorySlotStoresV4_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 4)
      (positiveRoundModelState I.calldata 0)[4]! := by
  have hv4 := v4StoredWord_eq_initialV4 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1600_eq_v4StoredWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv4]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV4_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 4)
      (positiveRoundModelState I.calldata 0)[4]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 4)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV4_v13MixedMem I hlen)

theorem v5StoredWord_eq_initialV5
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v5StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[5]!).toNat := by
  have hsrc := memorySlotStoresH5_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  unfold v5StoredWord
  have hload : v5LoadWord I = UInt256.ofNat ((Model.parsedH I.calldata)[5]!).toNat := by
    unfold v5LoadWord
    rw [← v13MixedMem_read544_eq_v4InitMem I hlen]
    exact hsrc
  rw [hload]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[5]!)

theorem memorySlotStoresV5_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 5)
      (positiveRoundModelState I.calldata 0)[5]! := by
  have hv5 := v5StoredWord_eq_initialV5 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1632_eq_v5StoredWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv5]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 5)
      (positiveRoundModelState I.calldata 0)[5]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 5)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV5_v13MixedMem I hlen)

theorem v6StoredWord_eq_initialV6
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v6StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[6]!).toNat := by
  have hsrc := memorySlotStoresH6_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  unfold v6StoredWord
  have hload : v6LoadWord I = UInt256.ofNat ((Model.parsedH I.calldata)[6]!).toNat := by
    unfold v6LoadWord
    rw [← v13MixedMem_read576_eq_v5InitMem I hlen]
    exact hsrc
  rw [hload]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[6]!)

theorem memorySlotStoresV6_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 6)
      (positiveRoundModelState I.calldata 0)[6]! := by
  have hv6 := v6StoredWord_eq_initialV6 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1664_eq_v6StoredWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv6]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV6_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 6)
      (positiveRoundModelState I.calldata 0)[6]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 6)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV6_v13MixedMem I hlen)

theorem v7StoredWord_eq_initialV7
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v7StoredWord I =
      UInt256.ofNat ((Model.parsedH I.calldata)[7]!).toNat := by
  have hsrc := memorySlotStoresH7_v13MixedMem I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord hSlotOffset hBaseOffset wordBytes at hsrc
  unfold v7StoredWord
  have hload : v7LoadWord I = UInt256.ofNat ((Model.parsedH I.calldata)[7]!).toNat := by
    unfold v7LoadWord
    rw [← v13MixedMem_read608_eq_v6InitMem I hlen]
    exact hsrc
  rw [hload]
  exact u256_land_u64_mask ((Model.parsedH I.calldata)[7]!)

theorem memorySlotStoresV7_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 7)
      (positiveRoundModelState I.calldata 0)[7]! := by
  have hv7 := v7StoredWord_eq_initialV7 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1696_eq_v7StoredWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv7]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range']

theorem memorySlotStoresV7_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 7)
      (positiveRoundModelState I.calldata 0)[7]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 7)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV7_v13MixedMem I hlen)

theorem memorySlotStoresV8_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 8)
      (positiveRoundModelState I.calldata 0)[8]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1728_eq_iv0 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV8_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 8)
      (positiveRoundModelState I.calldata 0)[8]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 8)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV8_v13MixedMem I hlen)

theorem memorySlotStoresV9_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 9)
      (positiveRoundModelState I.calldata 0)[9]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1760_eq_iv1 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV9_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 9)
      (positiveRoundModelState I.calldata 0)[9]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 9)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV9_v13MixedMem I hlen)

theorem memorySlotStoresV10_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 10)
      (positiveRoundModelState I.calldata 0)[10]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1792_eq_iv2 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV10_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 10)
      (positiveRoundModelState I.calldata 0)[10]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 10)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV10_v13MixedMem I hlen)

theorem memorySlotStoresV11_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 11)
      (positiveRoundModelState I.calldata 0)[11]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1824_eq_iv3 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV11_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 11)
      (positiveRoundModelState I.calldata 0)[11]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 11)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV11_v13MixedMem I hlen)

theorem t0MixMaskedWord_eq_parsedT0
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t0MixMaskedWord I = UInt256.ofNat (Model.parsedT0 I.calldata).toNat := by
  unfold t0MixMaskedWord
  have hload : t0MixLoadWord I = UInt256.ofNat (Model.parsedT0 I.calldata).toNat := by
    unfold t0MixLoadWord Model.parsedT0
    rw [v15InitMem_read1152 I hlen]
    rw [fromByteArrayBigEndian_toByteArray]
    rw [t0ParsedWord_eq_readLE64 I hlen]
    rw [u256_ofNat_toNat]
  rw [hload]
  exact u256_land_u64_mask (Model.parsedT0 I.calldata)

theorem v12MixedWord_eq_initialV12
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v12MixedWord I =
      UInt256.ofNat ((Model.IV[4]! ^^^ Model.parsedT0 I.calldata).toNat) := by
  unfold v12MixedWord
  rw [t0MixMaskedWord_eq_parsedT0 I hlen]
  change UInt256.xor (UInt256.ofNat (Model.IV[4]!).toNat)
    (UInt256.ofNat (Model.parsedT0 I.calldata).toNat) =
      UInt256.ofNat ((Model.IV[4]! ^^^ Model.parsedT0 I.calldata).toNat)
  exact u256_xor_u64 Model.IV[4]! (Model.parsedT0 I.calldata)

theorem memorySlotStoresV12_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 12)
      (positiveRoundModelState I.calldata 0)[12]! := by
  have hv12 := v12MixedWord_eq_initialV12 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1856_eq_v12MixedWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv12]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV12_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 12)
      (positiveRoundModelState I.calldata 0)[12]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 12)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV12_v13MixedMem I hlen)

theorem t1MixMaskedWord_eq_parsedT1
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t1MixMaskedWord I = UInt256.ofNat (Model.parsedT1 I.calldata).toNat := by
  unfold t1MixMaskedWord
  have hload : t1MixLoadWord I = UInt256.ofNat (Model.parsedT1 I.calldata).toNat := by
    unfold t1MixLoadWord Model.parsedT1
    rw [v15InitMem_read1184 I hlen]
    rw [fromByteArrayBigEndian_toByteArray]
    rw [t1ParsedWord_eq_readLE64 I hlen]
    rw [u256_ofNat_toNat]
  rw [hload]
  exact u256_land_u64_mask (Model.parsedT1 I.calldata)

theorem v13MixedWord_eq_initialV13
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    v13MixedWord I =
      UInt256.ofNat ((Model.IV[5]! ^^^ Model.parsedT1 I.calldata).toNat) := by
  unfold v13MixedWord
  rw [t1MixMaskedWord_eq_parsedT1 I hlen]
  change UInt256.xor (UInt256.ofNat (Model.IV[5]!).toNat)
    (UInt256.ofNat (Model.parsedT1 I.calldata).toNat) =
      UInt256.ofNat ((Model.IV[5]! ^^^ Model.parsedT1 I.calldata).toNat)
  exact u256_xor_u64 Model.IV[5]! (Model.parsedT1 I.calldata)

theorem memorySlotStoresV13_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 13)
      (positiveRoundModelState I.calldata 0)[13]! := by
  have hv13 := v13MixedWord_eq_initialV13 I hlen
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1888_eq_v13MixedWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [hv13]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV13_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 13)
      (positiveRoundModelState I.calldata 0)[13]! := by
  exact memorySlotStoresU64_v14FinalFlagMem_of_v13MixedMem I hlen
    (off := vSlotOffset 13)
    (by unfold vSlotOffset vBaseOffset wordBytes; decide)
    (memorySlotStoresV13_v13MixedMem I hlen)

theorem memorySlotStoresV14_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 14)
      (positiveRoundModelState I.calldata 0)[14]! := by
  have hflag := parsedFinalFlag_eq_false_of_byte_zero I hbyte
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1920_eq_iv6 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero, hflag]
  simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV14_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 14)
      (positiveRoundModelState I.calldata 0)[14]! := by
  have hflag := parsedFinalFlag_eq_true_of_byte_one I hbyte
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v14FinalFlagMem_read1920_eq_finalFlagWord I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero, hflag]
  simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV15_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v13MixedMem I) (vSlotOffset 15)
      (positiveRoundModelState I.calldata 0)[15]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v13MixedMem_read1952_eq_iv7 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem memorySlotStoresV15_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memorySlotStoresU64 (v14FinalFlagMem I) (vSlotOffset 15)
      (positiveRoundModelState I.calldata 0)[15]! := by
  unfold memorySlotStoresU64 memoryWord u64AsWord vSlotOffset vBaseOffset wordBytes
  rw [v14FinalFlagMem_read1952_eq_iv7 I hlen]
  rw [readWord_of_toByteArray_extract0_32]
  rw [positiveRoundModelState_zero]
  cases Model.parsedFinalFlag I.calldata <;> simp [Model.initialV, List.range', Model.IV]

theorem v13MixedMem_read1152
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1152 32 =
      UInt256.toByteArray (t0ParsedWord I) := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I)
    (v12MixedMem I) 1888 1152 (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I)
    (v15InitMem I) 1856 1152 (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  exact v15InitMem_read1152 I hlen

theorem v13MixedMem_read1184
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v13MixedMem I).readWithPadding 1184 32 =
      UInt256.toByteArray (t1ParsedWord I) := by
  rw [v13MixedMem]
  rw [toByteArray_write_read_below_of_gap (v13MixedWord I)
    (v12MixedMem I) 1888 1184 (by rw [v12MixedMem_size I hlen]; decide) (by decide)
    (by rw [v12MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  rw [v12MixedMem]
  rw [toByteArray_write_read_below_of_gap (v12MixedWord I)
    (v15InitMem I) 1856 1184 (by rw [v15InitMem_size I hlen]; decide) (by decide)
    (by rw [v15InitMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  exact v15InitMem_read1184 I hlen

theorem v14FinalFlagMem_read1152
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1152 32 =
      UInt256.toByteArray (t0ParsedWord I) := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108)
    (v13MixedMem I) 1920 1152 (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read1152 I hlen

theorem v14FinalFlagMem_read1184
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (v14FinalFlagMem I).readWithPadding 1184 32 =
      UInt256.toByteArray (t1ParsedWord I) := by
  rw [v14FinalFlagMem]
  rw [toByteArray_write_read_below_of_gap (UInt256.ofNat 16175846103906665108)
    (v13MixedMem I) 1920 1184 (by rw [v13MixedMem_size I hlen]; decide) (by decide)
    (by rw [v13MixedMem_size I hlen]; exact lt_usize 0 (by norm_num))]
  exact v13MixedMem_read1184 I hlen

theorem memoryRepresentsT_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsT (v13MixedMem I) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata) := by
  constructor
  · unfold Model.parsedT0 tSlotOffset wordBytes tBaseOffset
    have hread := v13MixedMem_read1152 I hlen
    rw [t0ParsedWord_eq_readLE64 I hlen] at hread
    exact memorySlotStoresU64_of_readWithPadding_toByteArray
      hread
  · unfold Model.parsedT1 tSlotOffset wordBytes tBaseOffset
    have hread := v13MixedMem_read1184 I hlen
    rw [t1ParsedWord_eq_readLE64 I hlen] at hread
    exact memorySlotStoresU64_of_readWithPadding_toByteArray
      hread

theorem memoryRepresentsT_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    memoryRepresentsT (v14FinalFlagMem I) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata) := by
  constructor
  · unfold Model.parsedT0 tSlotOffset wordBytes tBaseOffset
    have hread := v14FinalFlagMem_read1152 I hlen
    rw [t0ParsedWord_eq_readLE64 I hlen] at hread
    exact memorySlotStoresU64_of_readWithPadding_toByteArray
      hread
  · unfold Model.parsedT1 tSlotOffset wordBytes tBaseOffset
    have hread := v14FinalFlagMem_read1184 I hlen
    rw [t1ParsedWord_eq_readLE64 I hlen] at hread
    exact memorySlotStoresU64_of_readWithPadding_toByteArray
      hread

/-- Initial working-vector memory relation at the positive-round loop header for final flag `0`. -/
theorem memoryRepresentsVector_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    memoryRepresentsVector (v13MixedMem I) (positiveRoundModelState I.calldata 0) := by
  constructor
  · rw [positiveRoundModelState_zero]
    exact Model.initialV_size (Model.parsedH I.calldata) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata) (Model.parsedFinalFlag I.calldata)
  · intro i hi
    interval_cases i
    · exact memorySlotStoresV0_v13MixedMem I hlen
    · exact memorySlotStoresV1_v13MixedMem I hlen
    · exact memorySlotStoresV2_v13MixedMem I hlen
    · exact memorySlotStoresV3_v13MixedMem I hlen
    · exact memorySlotStoresV4_v13MixedMem I hlen
    · exact memorySlotStoresV5_v13MixedMem I hlen
    · exact memorySlotStoresV6_v13MixedMem I hlen
    · exact memorySlotStoresV7_v13MixedMem I hlen
    · exact memorySlotStoresV8_v13MixedMem I hlen
    · exact memorySlotStoresV9_v13MixedMem I hlen
    · exact memorySlotStoresV10_v13MixedMem I hlen
    · exact memorySlotStoresV11_v13MixedMem I hlen
    · exact memorySlotStoresV12_v13MixedMem I hlen
    · exact memorySlotStoresV13_v13MixedMem I hlen
    · exact memorySlotStoresV14_v13MixedMem I hlen hbyte
    · exact memorySlotStoresV15_v13MixedMem I hlen

/-- Initial working-vector memory relation at the positive-round loop header for final flag `1`. -/
theorem memoryRepresentsVector_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    memoryRepresentsVector (v14FinalFlagMem I) (positiveRoundModelState I.calldata 0) := by
  constructor
  · rw [positiveRoundModelState_zero]
    exact Model.initialV_size (Model.parsedH I.calldata) (Model.parsedT0 I.calldata)
      (Model.parsedT1 I.calldata) (Model.parsedFinalFlag I.calldata)
  · intro i hi
    interval_cases i
    · exact memorySlotStoresV0_v14FinalFlagMem I hlen
    · exact memorySlotStoresV1_v14FinalFlagMem I hlen
    · exact memorySlotStoresV2_v14FinalFlagMem I hlen
    · exact memorySlotStoresV3_v14FinalFlagMem I hlen
    · exact memorySlotStoresV4_v14FinalFlagMem I hlen
    · exact memorySlotStoresV5_v14FinalFlagMem I hlen
    · exact memorySlotStoresV6_v14FinalFlagMem I hlen
    · exact memorySlotStoresV7_v14FinalFlagMem I hlen
    · exact memorySlotStoresV8_v14FinalFlagMem I hlen
    · exact memorySlotStoresV9_v14FinalFlagMem I hlen
    · exact memorySlotStoresV10_v14FinalFlagMem I hlen
    · exact memorySlotStoresV11_v14FinalFlagMem I hlen
    · exact memorySlotStoresV12_v14FinalFlagMem I hlen
    · exact memorySlotStoresV13_v14FinalFlagMem I hlen
    · exact memorySlotStoresV14_v14FinalFlagMem I hlen hbyte
    · exact memorySlotStoresV15_v14FinalFlagMem I hlen

/-- Full initial model/memory invariant for the final-flag-`0` setup memory. -/
theorem positiveRoundHeaderInvariantZero_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    positiveRoundHeaderInvariant I 0 (v13MixedMem I) := by
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · exact v13MixedMem_size I hlen
  · exact memoryRepresentsH_v13MixedMem I hlen
  · exact memoryRepresentsM_v13MixedMem I hlen
  · exact memoryRepresentsT_v13MixedMem I hlen
  · exact memoryRepresentsVector_v13MixedMem I hlen hbyte

/-- Full initial model/memory invariant for the final-flag-`1` setup memory. -/
theorem positiveRoundHeaderInvariantOne_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    positiveRoundHeaderInvariant I 0 (v14FinalFlagMem I) := by
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · exact v14FinalFlagMem_size I hlen
  · exact memoryRepresentsH_v14FinalFlagMem I hlen
  · exact memoryRepresentsM_v14FinalFlagMem I hlen
  · exact memoryRepresentsT_v14FinalFlagMem I hlen
  · exact memoryRepresentsVector_v14FinalFlagMem I hlen hbyte

/-- Full initial positive-loop invariant for valid inputs whose final flag is `0`. -/
theorem positiveRoundInitialInvariantZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    positiveRoundInvariantContext ctx 0 (v13MixedMem ctx.executionEnv) := by
  have hvalid' := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  exact positiveRoundInitialInvariantZero_of_memory ctx hcode haccepts hvalid' hbyte
    (positiveRoundHeaderInvariantZero_v13MixedMem ctx.executionEnv hlen' hbyte)

/-- Full initial positive-loop invariant for valid inputs whose final flag is `1`. -/
theorem positiveRoundInitialInvariantOne
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    positiveRoundInvariantContext ctx 0 (v14FinalFlagMem ctx.executionEnv) := by
  have hvalid' := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  exact positiveRoundInitialInvariantOne_of_memory ctx hcode haccepts hvalid' hbyte
    (positiveRoundHeaderInvariantOne_v14FinalFlagMem ctx.executionEnv hlen' hbyte)

end Blake2f
