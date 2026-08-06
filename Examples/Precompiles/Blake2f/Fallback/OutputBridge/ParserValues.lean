import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserWindows

/-!
# BLAKE2F zero-round parser-value bridge

This file contains the byte-order and parser-value facts needed to connect the bytecode's
`SHR 192; evmSwap64` parsing of the `t0`/`t1` calldata words to the trusted model's
`Model.readLE64` view.  These facts are intentionally local to the Blake2f precompile example; they
avoid adding more special-purpose byte-array machinery to `Reasoning`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxHeartbeats 0
set_option maxRecDepth 500000

theorem bitvec_ofNatLT_toNat_eq_setWidth {n m : Nat} (x : BitVec n) (h : x.toNat < 2 ^ m) :
    BitVec.ofNatLT x.toNat h = BitVec.setWidth m x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  exact (Nat.mod_eq_of_lt h).symm

def readLE64Unrolled (bs : ByteArray) (off : Nat) : UInt64 :=
  (((((((((0 : UInt64) ||| (if _ : off + 0 < bs.size then bs[off + 0].toUInt64 else 0) <<< UInt64.ofNat 0)
    ||| (if _ : off + 1 < bs.size then bs[off + 1].toUInt64 else 0) <<< UInt64.ofNat 8)
    ||| (if _ : off + 2 < bs.size then bs[off + 2].toUInt64 else 0) <<< UInt64.ofNat 16)
    ||| (if _ : off + 3 < bs.size then bs[off + 3].toUInt64 else 0) <<< UInt64.ofNat 24)
    ||| (if _ : off + 4 < bs.size then bs[off + 4].toUInt64 else 0) <<< UInt64.ofNat 32)
    ||| (if _ : off + 5 < bs.size then bs[off + 5].toUInt64 else 0) <<< UInt64.ofNat 40)
    ||| (if _ : off + 6 < bs.size then bs[off + 6].toUInt64 else 0) <<< UInt64.ofNat 48)
    ||| (if _ : off + 7 < bs.size then bs[off + 7].toUInt64 else 0) <<< UInt64.ofNat 56)

theorem readLE64_eq_unrolled (bs : ByteArray) (off : Nat) :
    Model.readLE64 bs off = readLE64Unrolled bs off := by
  simp [Model.readLE64, readLE64Unrolled, List.range']

def le8BV64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  (BitVec.setWidth 64 b0) ||| (BitVec.setWidth 64 b1 <<< 8) |||
  (BitVec.setWidth 64 b2 <<< 16) ||| (BitVec.setWidth 64 b3 <<< 24) |||
  (BitVec.setWidth 64 b4 <<< 32) ||| (BitVec.setWidth 64 b5 <<< 40) |||
  (BitVec.setWidth 64 b6 <<< 48) ||| (BitVec.setWidth 64 b7 <<< 56)

def be8BV64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  BitVec.setWidth 64 b7 ||| (BitVec.setWidth 64 b6 <<< 8) |||
  (BitVec.setWidth 64 b5 <<< 16) ||| (BitVec.setWidth 64 b4 <<< 24) |||
  (BitVec.setWidth 64 b3 <<< 32) ||| (BitVec.setWidth 64 b2 <<< 40) |||
  (BitVec.setWidth 64 b1 <<< 48) ||| (BitVec.setWidth 64 b0 <<< 56)

theorem readLE64_expr_to_le8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (0 ||| b0.toUInt64 <<< UInt64.ofNat 0 ||| b1.toUInt64 <<< UInt64.ofNat 8 |||
      b2.toUInt64 <<< UInt64.ofNat 16 ||| b3.toUInt64 <<< UInt64.ofNat 24 |||
      b4.toUInt64 <<< UInt64.ofNat 32 ||| b5.toUInt64 <<< UInt64.ofNat 40 |||
      b6.toUInt64 <<< UInt64.ofNat 48 ||| b7.toUInt64 <<< UInt64.ofNat 56).toBitVec =
      le8BV64 b0.toBitVec b1.toBitVec b2.toBitVec b3.toBitVec b4.toBitVec b5.toBitVec b6.toBitVec b7.toBitVec := by
  cases b0 with | ofBitVec b0 =>
  cases b1 with | ofBitVec b1 =>
  cases b2 with | ofBitVec b2 =>
  cases b3 with | ofBitVec b3 =>
  cases b4 with | ofBitVec b4 =>
  cases b5 with | ofBitVec b5 =>
  cases b6 with | ofBitVec b6 =>
  cases b7 with | ofBitVec b7 =>
  change (0 ||| (UInt8.ofBitVec b0).toUInt64 <<< UInt64.ofNat 0 ||| (UInt8.ofBitVec b1).toUInt64 <<< UInt64.ofNat 8 ||| (UInt8.ofBitVec b2).toUInt64 <<< UInt64.ofNat 16 ||| (UInt8.ofBitVec b3).toUInt64 <<< UInt64.ofNat 24 ||| (UInt8.ofBitVec b4).toUInt64 <<< UInt64.ofNat 32 ||| (UInt8.ofBitVec b5).toUInt64 <<< UInt64.ofNat 40 ||| (UInt8.ofBitVec b6).toUInt64 <<< UInt64.ofNat 48 ||| (UInt8.ofBitVec b7).toUInt64 <<< UInt64.ofNat 56).toBitVec = le8BV64 b0 b1 b2 b3 b4 b5 b6 b7
  unfold le8BV64
  simp [UInt8.toUInt64]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b0]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b1]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b2]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b3]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b4]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b5]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b6]
  rw [bitvec_ofNatLT_toNat_eq_setWidth b7]

theorem readLE64_toBitVec_of_inbounds (bs : ByteArray) (off : Nat)
    (h0 : off + 0 < bs.size) (h1 : off + 1 < bs.size) (h2 : off + 2 < bs.size)
    (h3 : off + 3 < bs.size) (h4 : off + 4 < bs.size) (h5 : off + 5 < bs.size)
    (h6 : off + 6 < bs.size) (h7 : off + 7 < bs.size) :
    (Model.readLE64 bs off).toBitVec =
      le8BV64 (bs[off+0].toBitVec) (bs[off+1].toBitVec) (bs[off+2].toBitVec) (bs[off+3].toBitVec)
        (bs[off+4].toBitVec) (bs[off+5].toBitVec) (bs[off+6].toBitVec) (bs[off+7].toBitVec) := by
  rw [readLE64_eq_unrolled]
  unfold readLE64Unrolled
  simp only [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4, dif_pos h5, dif_pos h6, dif_pos h7]
  exact readLE64_expr_to_le8 (bs[off+0]) (bs[off+1]) (bs[off+2]) (bs[off+3])
    (bs[off+4]) (bs[off+5]) (bs[off+6]) (bs[off+7])

theorem byteArray_toList_eq_8 (bs : ByteArray) (hsize : bs.size = 8) :
    bs.toList = [bs[0], bs[1], bs[2], bs[3], bs[4], bs[5], bs[6], bs[7]] := by
  change bs.data.size = 8 at hsize
  rw [byteArray_toList_eq]
  apply List.ext_getElem
  · rw [Array.length_toList, hsize]
    rfl
  · intro i hleft hright
    have hi : i < 8 := by simpa using hright
    interval_cases i <;> (rw [Array.getElem_toList]; rfl)

theorem fromBytesBigEndian_8_to_be8BV64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    BitVec.ofNat 64 (fromBytesBigEndian [UInt8.ofBitVec b0, UInt8.ofBitVec b1, UInt8.ofBitVec b2, UInt8.ofBitVec b3, UInt8.ofBitVec b4, UInt8.ofBitVec b5, UInt8.ofBitVec b6, UInt8.ofBitVec b7]) =
      be8BV64 b0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold be8BV64
  norm_num [fromBytesBigEndian, fromBytes']
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul, bitvec_ofNat_toNat_eq_setWidth]
  bv_decide

def be8BV256 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 256 :=
  BitVec.setWidth 256 (be8BV64 b0 b1 b2 b3 b4 b5 b6 b7)

theorem bvSwap64In256_be8BV256 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bvSwap64In256 (be8BV256 b0 b1 b2 b3 b4 b5 b6 b7) =
      BitVec.setWidth 256 (le8BV64 b0 b1 b2 b3 b4 b5 b6 b7) := by
  unfold bvSwap64In256 swapStep32B swapStep16B swapStep8B be8BV256 be8BV64 le8BV64
  bv_decide

theorem bvSwap64In256_fromBytesBigEndian_8_to_le8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    bvSwap64In256 (BitVec.ofNat 256 (fromBytesBigEndian [b0, b1, b2, b3, b4, b5, b6, b7])) =
      BitVec.setWidth 256 (le8BV64 b0.toBitVec b1.toBitVec b2.toBitVec b3.toBitVec b4.toBitVec b5.toBitVec b6.toBitVec b7.toBitVec) := by
  cases b0 with | ofBitVec b0 =>
  cases b1 with | ofBitVec b1 =>
  cases b2 with | ofBitVec b2 =>
  cases b3 with | ofBitVec b3 =>
  cases b4 with | ofBitVec b4 =>
  cases b5 with | ofBitVec b5 =>
  cases b6 with | ofBitVec b6 =>
  cases b7 with | ofBitVec b7 =>
  have hbe := fromBytesBigEndian_8_to_be8BV64 b0 b1 b2 b3 b4 b5 b6 b7
  have hbe256 : BitVec.ofNat 256 (fromBytesBigEndian [UInt8.ofBitVec b0, UInt8.ofBitVec b1, UInt8.ofBitVec b2, UInt8.ofBitVec b3, UInt8.ofBitVec b4, UInt8.ofBitVec b5, UInt8.ofBitVec b6, UInt8.ofBitVec b7]) = be8BV256 b0 b1 b2 b3 b4 b5 b6 b7 := by
    unfold be8BV256
    rw [← hbe]
    apply BitVec.eq_of_toNat_eq
    have hlt64 : fromBytesBigEndian [UInt8.ofBitVec b0, UInt8.ofBitVec b1, UInt8.ofBitVec b2, UInt8.ofBitVec b3, UInt8.ofBitVec b4, UInt8.ofBitVec b5, UInt8.ofBitVec b6, UInt8.ofBitVec b7] < 2 ^ 64 := by
      unfold fromBytesBigEndian
      have hle := fromBytes'_le (bs := [UInt8.ofBitVec b0, UInt8.ofBitVec b1, UInt8.ofBitVec b2, UInt8.ofBitVec b3, UInt8.ofBitVec b4, UInt8.ofBitVec b5, UInt8.ofBitVec b6, UInt8.ofBitVec b7].reverse)
      simpa using hle
    have hlt256 : fromBytesBigEndian [UInt8.ofBitVec b0, UInt8.ofBitVec b1, UInt8.ofBitVec b2, UInt8.ofBitVec b3, UInt8.ofBitVec b4, UInt8.ofBitVec b5, UInt8.ofBitVec b6, UInt8.ofBitVec b7] < 2 ^ 256 := by
      exact lt_trans hlt64 (by norm_num)
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hlt64]
  rw [hbe256]
  exact bvSwap64In256_be8BV256 b0 b1 b2 b3 b4 b5 b6 b7

theorem u256bv_ofNat_u64 (w : UInt64) :
    u256bv (UInt256.ofNat w.toNat) = BitVec.setWidth 256 w.toBitVec := by
  cases w with | ofBitVec wb =>
  rw [u256bv_ofNat]
  change BitVec.ofNat 256 wb.toNat = BitVec.setWidth 256 wb
  rw [bitvec_ofNat_toNat_eq_setWidth]

theorem evmSwap64_fromBytesBigEndian_size8_eq_readLE64_zero
    (bs : ByteArray) (hsize : bs.size = 8) :
    evmSwap64 (UInt256.ofNat (fromBytesBigEndian bs.toList)) =
      UInt256.ofNat (Model.readLE64 bs 0).toNat := by
  apply u256bv_inj
  rw [u256bv_evmSwap64, u256bv_ofNat, u256bv_ofNat_u64]
  rw [byteArray_toList_eq_8 bs hsize]
  rw [readLE64_toBitVec_of_inbounds bs 0]
  · exact bvSwap64In256_fromBytesBigEndian_8_to_le8 (bs[0]) (bs[1]) (bs[2]) (bs[3])
      (bs[4]) (bs[5]) (bs[6]) (bs[7])

theorem readLE64_extract_window (cd : ByteArray) (off : Nat) (hwin : off + 8 <= cd.size) :
    Model.readLE64 cd off = Model.readLE64 (cd.extract off (off + 8)) 0 := by
  have hmin : min (off + 8) cd.size - off = 8 := by omega
  have h0 : off < cd.size := by omega
  have h1 : off + 1 < cd.size := by omega
  have h2 : off + 2 < cd.size := by omega
  have h3 : off + 3 < cd.size := by omega
  have h4 : off + 4 < cd.size := by omega
  have h5 : off + 5 < cd.size := by omega
  have h6 : off + 6 < cd.size := by omega
  have h7 : off + 7 < cd.size := by omega
  unfold Model.readLE64
  simp [List.range', hmin, h0, h1, h2, h3, h4, h5, h6, h7]

theorem shr192_fromByteArrayBigEndian_readWithPadding32
    (mem : ByteArray) (addr : Nat) (hin : addr + 32 <= mem.size) :
    UInt256.shiftRight (UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding addr 32))) ⟨192⟩ =
      UInt256.ofNat (fromBytesBigEndian (mem.readWithPadding addr 8).toList) := by
  have hsplit := byteArray_readWithPadding_split mem addr 8 24
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
  have hpreSize : (mem.readWithPadding addr 8).size = 8 := by
    rw [readWithPadding_eq_extract' mem addr 8 (by decide) (by decide) (by omega)]
    rw [ByteArray.size_extract]
    omega
  have hsufSize : (mem.readWithPadding (addr + 8) 24).size = 24 := by
    rw [readWithPadding_eq_extract' mem (addr + 8) 24 (by decide) (by decide) (by omega)]
    rw [ByteArray.size_extract]
    omega
  apply u256_inj
  rw [show (⟨192⟩ : UInt256) = UInt256.ofNat 192 by native_decide]
  rw [ushr_ofNat_toNat _ 192 (by decide)]
  have hsize32 : (mem.readWithPadding addr 32).size = 32 := by
    rw [readWithPadding_eq_extract' mem addr 32 (by decide) (by decide) hin]
    rw [ByteArray.size_extract]
    omega
  have hltFull : fromByteArrayBigEndian (mem.readWithPadding addr 32) < UInt256.size := by
    unfold fromByteArrayBigEndian fromBytesBigEndian
    have hle := fromBytes'_le (bs := (mem.readWithPadding addr 32).toList.reverse)
    have hlen : (mem.readWithPadding addr 32).toList.length = 32 := by
      simpa [byteArray_toList_eq] using hsize32
    rw [List.length_reverse, hlen] at hle
    simpa [byteArray_toList_eq, UInt256.size] using hle
  rw [UInt256.toNat_ofNat_of_lt hltFull]
  rw [Nat.shiftRight_eq_div_pow]
  rw [hsplit]
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [← byteArray_toList_eq (mem.readWithPadding addr 8)]
  rw [← byteArray_toList_eq (mem.readWithPadding (addr + 8) 24)]
  have hsufLen : (mem.readWithPadding (addr + 8) 24).toList.length = 24 := by
    simpa [byteArray_toList_eq] using hsufSize
  rw [show 2 ^ 192 = 2 ^ (8 * (mem.readWithPadding (addr + 8) 24).toList.length) by
    rw [hsufLen]]
  rw [fromBytesBigEndian_append_div]
  have hlt8 : fromBytesBigEndian (mem.readWithPadding addr 8).toList < UInt256.size := by
    unfold fromBytesBigEndian Function.comp
    have hle := fromBytes'_le (bs := (mem.readWithPadding addr 8).toList.reverse)
    rw [List.length_reverse] at hle
    have hlen : (mem.readWithPadding addr 8).toList.length = 8 := by
      simpa [byteArray_toList_eq] using hpreSize
    rw [hlen] at hle
    exact lt_trans hle (by norm_num [UInt256.size])
  rw [UInt256.toNat_ofNat_of_lt hlt8]

theorem t0ParsedWord_eq_readLE64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t0ParsedWord I = UInt256.ofNat (Model.readLE64 I.calldata 196).toNat := by
  unfold t0ParsedWord t0LoadWord
  rw [shr192_fromByteArrayBigEndian_readWithPadding32 (m15StoredMem I) 356
    (by rw [m15StoredMem_size I hlen]; decide)]
  rw [m15StoredMem_read356_8 I hlen]
  rw [evmSwap64_fromBytesBigEndian_size8_eq_readLE64_zero _
    (by rw [ByteArray.size_extract, hlen]; decide)]
  rw [← readLE64_extract_window I.calldata 196 (by rw [hlen]; decide)]

theorem t0StoredMem_read364_8 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (t0StoredMem I).readWithPadding 364 8 = I.calldata.extract 204 212 := by
  unfold t0StoredMem
  rw [toByteArray_write_read_below_len_padded_of_gap (t0ParsedWord I)
    (m15StoredMem I) 1152 364 8 (by decide) (by decide) (by decide)
    (by rw [m15StoredMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact m15StoredMem_read364_8 I hlen

theorem t1ParsedWord_eq_readLE64 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t1ParsedWord I = UInt256.ofNat (Model.readLE64 I.calldata 204).toNat := by
  unfold t1ParsedWord t1LoadWord
  rw [shr192_fromByteArrayBigEndian_readWithPadding32 (t0StoredMem I) 364
    (by rw [t0StoredMem_size I hlen]; decide)]
  rw [t0StoredMem_read364_8 I hlen]
  rw [evmSwap64_fromBytesBigEndian_size8_eq_readLE64_zero _
    (by rw [ByteArray.size_extract, hlen]; decide)]
  rw [← readLE64_extract_window I.calldata 204 (by rw [hlen]; decide)]

theorem u256bv_xor (x y : UInt256) :
    u256bv (UInt256.xor x y) = u256bv x ^^^ u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [BitVec.toNat_xor]
  rw [u256bv_toNat, u256bv_toNat]
  unfold UInt256.xor Fin.xor
  simp only
  apply Nat.mod_eq_of_lt
  change Nat.bitwise bne x.val.val y.val.val < 2 ^ 256
  exact Nat.bitwise_lt_two_pow x.val.isLt y.val.isLt

theorem land_u64_mask (w : UInt64) :
    UInt256.land (UInt256.ofNat w.toNat) ⟨18446744073709551615⟩ =
      UInt256.ofNat w.toNat := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_ofNat, u256bv_mk]
  cases w with | ofBitVec wb =>
  change (BitVec.ofNat 256 wb.toNat &&& BitVec.ofNat 256 18446744073709551615) =
    BitVec.ofNat 256 wb.toNat
  rw [bitvec_ofNat_toNat_eq_setWidth]
  bv_decide

theorem xor_u64_to_u256_mask (c w : UInt64) :
    UInt256.land (UInt256.xor (UInt256.ofNat c.toNat) (UInt256.ofNat w.toNat))
        ⟨18446744073709551615⟩ =
      UInt256.ofNat (c ^^^ w).toNat := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_xor, u256bv_ofNat, u256bv_ofNat, u256bv_mk, u256bv_ofNat]
  cases c with | ofBitVec cb =>
  cases w with | ofBitVec wb =>
  change ((BitVec.ofNat 256 cb.toNat ^^^ BitVec.ofNat 256 wb.toNat) &&&
      BitVec.ofNat 256 18446744073709551615) =
    BitVec.ofNat 256 (UInt64.xor (UInt64.ofBitVec cb) (UInt64.ofBitVec wb)).toNat
  simp [UInt64.xor]
  bv_decide

theorem t0MixLoadWord_eq_t0ParsedWord (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t0MixLoadWord I = t0ParsedWord I := by
  unfold t0MixLoadWord
  rw [v15InitMem_read1152 I hlen]
  rw [fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (t0ParsedWord I)

theorem t1MixLoadWord_eq_t1ParsedWord (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    t1MixLoadWord I = t1ParsedWord I := by
  unfold t1MixLoadWord
  rw [v15InitMem_read1184 I hlen]
  rw [fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (t1ParsedWord I)

theorem v12MixedMasked_eq_modelWord (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩ =
      UInt256.ofNat (((UInt64.ofNat 5840696475078001361) ^^^
        Model.readLE64 I.calldata 196).toNat) := by
  unfold v12MixedWord t0MixMaskedWord
  rw [t0MixLoadWord_eq_t0ParsedWord I hlen]
  rw [t0ParsedWord_eq_readLE64 I hlen]
  rw [land_u64_mask]
  rw [show (UInt256.ofNat 5840696475078001361) =
      UInt256.ofNat (UInt64.ofNat 5840696475078001361).toNat by native_decide]
  rw [xor_u64_to_u256_mask]

theorem v13MixedMasked_eq_modelWord (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩ =
      UInt256.ofNat (((UInt64.ofNat 11170449401992604703) ^^^
        Model.readLE64 I.calldata 204).toNat) := by
  unfold v13MixedWord t1MixMaskedWord
  rw [t1MixLoadWord_eq_t1ParsedWord I hlen]
  rw [t1ParsedWord_eq_readLE64 I hlen]
  rw [land_u64_mask]
  rw [show (UInt256.ofNat 11170449401992604703) =
      UInt256.ofNat (UInt64.ofNat 11170449401992604703).toNat by native_decide]
  rw [xor_u64_to_u256_mask]

theorem model_writeLE64_append (acc : ByteArray) (w : UInt64) :
    Model.writeLE64 acc w = acc ++ modelWordChunk w := by
  cases w with | ofBitVec wb =>
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [Model.writeLE64, modelWordChunk, List.range']

theorem bytecodeZeroFlag0Bytes_eq_modelZeroFlag0Bytes
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    bytecodeZeroFlag0Bytes I = modelZeroFlag0Bytes I.calldata := by
  unfold bytecodeZeroFlag0Bytes modelZeroFlag0Bytes
  simp only
  repeat rw [model_writeLE64_append]
  change bytecodeWordChunk (UInt256.ofNat 7640891576956012808) ++
      bytecodeWordChunk (UInt256.ofNat 13503953896175478587) ++
      bytecodeWordChunk (UInt256.ofNat 4354685564936845355) ++
      bytecodeWordChunk (UInt256.ofNat 11912009170470909681) ++
      bytecodeWordChunk (UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩) ++
      bytecodeWordChunk (UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩) ++
      bytecodeWordChunk (UInt256.ofNat 2270897969802886507) ++
      bytecodeWordChunk (UInt256.ofNat 6620516959819538809) = _
  rw [bytecodeWordChunk_iv0, bytecodeWordChunk_iv1, bytecodeWordChunk_iv2,
    bytecodeWordChunk_iv3]
  rw [v12MixedMasked_eq_modelWord I hlen, v13MixedMasked_eq_modelWord I hlen]
  rw [bytecodeWordChunk_of_u64, bytecodeWordChunk_of_u64]
  rw [bytecodeWordChunk_iv6_zeroFlag, bytecodeWordChunk_iv7]
  simp

theorem bytecodeZeroFlag1Bytes_eq_modelZeroFlag1Bytes
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    bytecodeZeroFlag1Bytes I = modelZeroFlag1Bytes I.calldata := by
  unfold bytecodeZeroFlag1Bytes modelZeroFlag1Bytes
  simp only
  repeat rw [model_writeLE64_append]
  change bytecodeWordChunk (UInt256.ofNat 7640891576956012808) ++
      bytecodeWordChunk (UInt256.ofNat 13503953896175478587) ++
      bytecodeWordChunk (UInt256.ofNat 4354685564936845355) ++
      bytecodeWordChunk (UInt256.ofNat 11912009170470909681) ++
      bytecodeWordChunk (UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩) ++
      bytecodeWordChunk (UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩) ++
      bytecodeWordChunk (UInt256.ofNat 16175846103906665108) ++
      bytecodeWordChunk (UInt256.ofNat 6620516959819538809) = _
  rw [bytecodeWordChunk_iv0, bytecodeWordChunk_iv1, bytecodeWordChunk_iv2,
    bytecodeWordChunk_iv3]
  rw [v12MixedMasked_eq_modelWord I hlen, v13MixedMasked_eq_modelWord I hlen]
  rw [bytecodeWordChunk_of_u64, bytecodeWordChunk_of_u64]
  rw [bytecodeWordChunk_iv6_oneFlag, bytecodeWordChunk_iv7]
  simp

end Blake2f
