import Examples.Ripemd160Old.HashMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ripemd160Old

open Ripemd160

theorem runtimeWordAt_readByte {c : RuntimeMemCursor} {addr value : UInt256}
    (hw : RuntimeWordAt c addr value) {q : Nat} (hq : q < 32) :
    c.mem.readWithPadding (addr.toNat + q) 1 =
      value.toByteArray.extract q (q + 1) := by
  rcases hw with ⟨hread, hcover, _⟩
  have hwhole : c.mem.extract addr.toNat (addr.toNat + 32) = value.toByteArray := by
    rw [← readWithPadding_eq_extract c.mem addr.toNat hcover]
    exact hread
  rw [readWithPadding_eq_extract' c.mem (addr.toNat + q) 1 (by omega)
    (by omega) (by omega)]
  have hsub := congrArg (fun b : ByteArray => b.extract q (q + 1)) hwhole
  dsimp only at hsub
  rw [extract_extract_BA] at hsub
  rw [show min (addr.toNat + (q + 1)) (addr.toNat + 32) =
      addr.toNat + q + 1 by omega] at hsub
  simpa only [Nat.add_zero, Nat.min_eq_left (by omega)] using hsub

theorem oldSourceWord_bytes (I : ExecutionEnv) {j : Nat}
    (hj : j < oldCopyIterations I) :
    (oldSourceWord I j).toByteArray =
      (hashAllocatedMem I).readWithPadding (160 + 32 * j) 32 := by
  symm
  apply oldRead32_roundtrip
  rw [hashAllocatedMem_size]
  have hb := oldCopy_body_lt I hj
  omega

theorem oldZeroFinal_readData (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hp : p < I.calldata.size) :
    (oldZeroCursor I (oldZeroIterations I)).mem.readWithPadding
        ((hashPadPtr I).toNat + p) 1 =
      I.calldata.extract p (p + 1) := by
  let j := p / 32
  let q := p % 32
  have hq : q < 32 := Nat.mod_lt _ (by decide)
  have hpjq : p = 32 * j + q := by
    dsimp only [j, q]
    have hd := Nat.mod_add_div p 32
    omega
  have hj : j < oldCopyIterations I := by
    unfold j oldCopyIterations
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    omega
  obtain ⟨_, _, hcopied, _⟩ :=
    oldZeroCursor_invariant I hsmall (le_refl (oldZeroIterations I))
  have hw := hcopied j hj
  have hbyte := runtimeWordAt_readByte hw hq
  rw [oldCopyDest_toNat I j hsmall (by omega), oldSourceWord_bytes I hj] at hbyte
  have hsource :
      ((hashAllocatedMem I).readWithPadding (160 + 32 * j) 32).extract q (q + 1) =
        (hashAllocatedMem I).readWithPadding (160 + p) 1 := by
    rw [readWithPadding_eq_extract (hashAllocatedMem I) (160 + 32 * j) (by
      rw [hashAllocatedMem_size]
      have hb := oldCopy_body_lt I hj
      omega)]
    rw [extract_extract_BA]
    rw [show min (160 + 32 * j + (q + 1)) (160 + 32 * j + 32) =
      160 + 32 * j + q + 1 by omega]
    rw [readWithPadding_eq_extract' (hashAllocatedMem I) (160 + p) 1
      (by omega) (by omega) (by rw [hashAllocatedMem_size]; omega)]
    rw [hpjq]
    simp only [Nat.add_assoc]
  rw [hsource] at hbyte
  rw [hashAllocatedMem_read_data I (by omega) (by omega) (by omega)] at hbyte
  simpa [hpjq, Nat.add_assoc] using hbyte

theorem hashAllocatedMem_read_copyPadding (I : ExecutionEnv) {p : Nat}
    (hp0 : I.calldata.size ≤ p)
    (hp1 : p < 32 * oldCopyIterations I) :
    (hashAllocatedMem I).readWithPadding (160 + p) 1 = ⟨#[0]⟩ := by
  have hrounded : 32 * oldCopyIterations I ≤ I.calldata.size + 31 := by
    unfold oldCopyIterations
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (I.calldata.size + 31) 32
  have hq : p - I.calldata.size + 1 ≤ 32 := by omega
  unfold hashAllocatedMem
  rw [write32_read_above_len (hashNewFreePtr I).toByteArray (fallbackPaddedMem I) 64
    (160 + p) 1 (by rw [toByteArray_size])
    (by rw [fallbackPaddedMem_size]; omega) (by omega)
    (by rw [fallbackPaddedMem_size]; omega) (by decide) (by decide)]
  unfold fallbackPaddedMem
  have haddr : 160 + p = 160 + I.calldata.size + (p - I.calldata.size) := by omega
  rw [haddr]
  rw [write_read_window_from (⟨0⟩ : UInt256).toByteArray
    (fallbackCalldataMem I) 0 (160 + I.calldata.size) 32
    (p - I.calldata.size) 1 (by decide) (by rw [toByteArray_size])
    (by rw [fallbackCalldataMem_size]) hq (by decide) (by decide)]
  simp only [Nat.zero_add]
  rw [zero_toByteArray_eq_zeroes32,
    zeroes_extract_window 32 (p - I.calldata.size) 1 hq]
  native_decide

theorem oldZeroFinal_readCopiedZero (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hp0 : I.calldata.size ≤ p)
    (hp1 : p < 32 * oldCopyIterations I) :
    (oldZeroCursor I (oldZeroIterations I)).mem.readWithPadding
        ((hashPadPtr I).toNat + p) 1 = ⟨#[0]⟩ := by
  let j := p / 32
  let q := p % 32
  have hq : q < 32 := Nat.mod_lt _ (by decide)
  have hpjq : p = 32 * j + q := by
    dsimp only [j, q]
    have hd := Nat.mod_add_div p 32
    omega
  have hj : j < oldCopyIterations I := by
    unfold j
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    simpa [Nat.mul_comm] using hp1
  obtain ⟨_, _, hcopied, _⟩ :=
    oldZeroCursor_invariant I hsmall (le_refl (oldZeroIterations I))
  have hbyte := runtimeWordAt_readByte (hcopied j hj) hq
  rw [oldCopyDest_toNat I j hsmall (by omega), oldSourceWord_bytes I hj] at hbyte
  have hsource :
      ((hashAllocatedMem I).readWithPadding (160 + 32 * j) 32).extract q (q + 1) =
        (hashAllocatedMem I).readWithPadding (160 + p) 1 := by
    rw [readWithPadding_eq_extract (hashAllocatedMem I) (160 + 32 * j) (by
      rw [hashAllocatedMem_size]
      have hb := oldCopy_body_lt I hj
      omega)]
    rw [extract_extract_BA]
    rw [show min (160 + 32 * j + (q + 1)) (160 + 32 * j + 32) =
      160 + 32 * j + q + 1 by omega]
    rw [readWithPadding_eq_extract' (hashAllocatedMem I) (160 + p) 1
      (by omega) (by omega) (by
        rw [hashAllocatedMem_size]
        have hrounded : 32 * oldCopyIterations I ≤ I.calldata.size + 31 := by
          unfold oldCopyIterations
          simpa [Nat.mul_comm] using Nat.div_mul_le_self (I.calldata.size + 31) 32
        omega)]
    rw [hpjq]
    simp only [Nat.add_assoc]
  rw [hsource, hashAllocatedMem_read_copyPadding I hp0 hp1] at hbyte
  simpa [hpjq, Nat.add_assoc] using hbyte

theorem oldZeroFinal_readZero (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hp0 : 32 * oldCopyIterations I ≤ p)
    (hp1 : p < Model.paddedLength I.calldata.size) :
    (oldZeroCursor I (oldZeroIterations I)).mem.readWithPadding
        ((hashPadPtr I).toNat + p) 1 = ⟨#[0]⟩ := by
  let j := p / 32 - oldCopyIterations I
  let q := p % 32
  have hq : q < 32 := Nat.mod_lt _ (by decide)
  have hcopyDiv : oldCopyIterations I ≤ p / 32 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 32)]
    simpa [Nat.mul_comm] using hp0
  have hpjq : p = 32 * (oldCopyIterations I + j) + q := by
    dsimp only [j, q]
    rw [Nat.add_sub_of_le hcopyDiv]
    have hd := Nat.mod_add_div p 32
    omega
  have hj : j < oldZeroIterations I := by
    have hend := oldZeroIndex_at_end I
    dsimp only [j]
    unfold oldZeroIndex at hend
    omega
  obtain ⟨_, _, _, hzero⟩ :=
    oldZeroCursor_invariant I hsmall (le_refl (oldZeroIterations I))
  have hbyte := runtimeWordAt_readByte (hzero j hj) hq
  rw [oldZeroDest_toNat I j hsmall (by omega)] at hbyte
  unfold oldZeroIndex at hbyte
  rw [zero_toByteArray_eq_zeroes32,
    zeroes_extract_window 32 q 1 (by omega)] at hbyte
  have hz : ffi.ByteArray.zeroes 1 = (⟨#[0]⟩ : ByteArray) := by native_decide
  rw [hz] at hbyte
  simpa [hpjq, Nat.add_assoc] using hbyte

private theorem oldLand255_toNat (x : UInt256) :
    (UInt256.land x ⟨255⟩).toNat = x.toNat &&& 255 := by
  have hlt : x.toNat &&& 255 < UInt256.size :=
    lt_of_le_of_lt Nat.and_le_right (by decide)
  simpa [uland_toNat, show (⟨255⟩ : UInt256).toNat = 255 from by decide,
    Nat.mod_eq_of_lt hlt]

private theorem oldLandMask32_toNat (x : UInt256) :
    (UInt256.land x ⟨0xffffffff⟩).toNat = x.toNat &&& 0xffffffff := by
  have hlt : x.toNat &&& 0xffffffff < UInt256.size :=
    lt_of_le_of_lt Nat.and_le_right (by decide)
  simpa [uland_toNat,
    show (⟨0xffffffff⟩ : UInt256).toNat = 0xffffffff from by decide,
    Nat.mod_eq_of_lt hlt]

private theorem oldHashBitLength_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldHashBitLength I).toNat = I.calldata.size * 8 := by
  unfold oldHashBitLength calldataSizeWord
  rw [umul_toNat]
  · rw [ulit_toNat' I.calldata.size (lt_of_le_of_lt hsmall (by native_decide)),
      show (⟨8⟩ : UInt256).toNat = 8 from by decide]
  · rw [ulit_toNat' I.calldata.size (lt_of_le_of_lt hsmall (by native_decide)),
      show (⟨8⟩ : UInt256).toNat = 8 from by decide,
      show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega

private theorem oldByteAfterMask32 (n shift : Nat) (hshift : shift + 8 ≤ 32) :
    (((n &&& 0xffffffff) >>> shift) &&& 255) = ((n >>> shift) &&& 255) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · have hsi : shift + i < 32 := by omega
    rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
      Nat.testBit_two_pow_sub_one,
      show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi, hsi]
  · have hpow : 255 < 2 ^ i :=
      lt_of_lt_of_le (by norm_num : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp

private theorem oldByteAfterShift32 (n shift : Nat) :
    (((n >>> 32) >>> shift) &&& 255) = ((n >>> (32 + shift)) &&& 255) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight]
  congr 2
  omega

private theorem oldNatByte_mod64 (n q : Nat) (hq : q < 8) :
    ((n >>> (q * 8)) &&& 255) = (((n % 2 ^ 64) >>> (q * 8)) &&& 255) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · rw [Nat.testBit_mod_two_pow]
    simp [show q * 8 + i < 64 by omega]
  · have hpow : 255 < 2 ^ i :=
      lt_of_lt_of_le (by norm_num : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp

theorem oldLengthByte_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat} (hq : q < 8) :
    (oldLengthByte I q).toNat =
      (Model.bitLength I.calldata.size >>> (q * 8)) &&& 255 := by
  have hbit := oldHashBitLength_toNat I hsmall
  have hlo : (oldBitLengthLo I).toNat =
      (I.calldata.size * 8) &&& 0xffffffff := by
    unfold oldBitLengthLo
    rw [oldLandMask32_toNat, hbit]
  have hhi : (oldBitLengthHi I).toNat = (I.calldata.size * 8) >>> 32 := by
    unfold oldBitLengthHi
    rw [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl]
    rw [ushr_ofNat_toNat _ 32 (by decide), hbit]
  have hmodel (r : Nat) (hr : r < 8) :
      (((I.calldata.size * 8) >>> (r * 8)) &&& 255) =
        (Model.bitLength I.calldata.size >>> (r * 8)) &&& 255 := by
    unfold Model.bitLength
    exact oldNatByte_mod64 (I.calldata.size * 8) r hr
  interval_cases q
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, hlo]
    have hm := oldByteAfterMask32 (I.calldata.size * 8) 0 (by decide)
    simp only [Nat.shiftRight_zero] at hm
    rw [hm]
    simpa using hmodel 0 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from rfl,
      ushr_ofNat_toNat _ 8 (by decide), hlo, oldByteAfterMask32 _ 8 (by decide)]
    simpa using hmodel 1 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨16⟩ : UInt256) = UInt256.ofNat 16 from rfl,
      ushr_ofNat_toNat _ 16 (by decide), hlo, oldByteAfterMask32 _ 16 (by decide)]
    simpa using hmodel 2 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨24⟩ : UInt256) = UInt256.ofNat 24 from rfl,
      ushr_ofNat_toNat _ 24 (by decide), hlo, oldByteAfterMask32 _ 24 (by decide)]
    simpa using hmodel 3 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, hhi]
    simpa using hmodel 4 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from rfl,
      ushr_ofNat_toNat _ 8 (by decide), hhi, oldByteAfterShift32 _ 8]
    simpa using hmodel 5 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨16⟩ : UInt256) = UInt256.ofNat 16 from rfl,
      ushr_ofNat_toNat _ 16 (by decide), hhi, oldByteAfterShift32 _ 16]
    simpa using hmodel 6 (by decide)
  · simp only [oldLengthByte]
    rw [oldLand255_toNat, show (⟨24⟩ : UInt256) = UInt256.ofNat 24 from rfl,
      ushr_ofNat_toNat _ 24 (by decide), hhi, oldByteAfterShift32 _ 24]
    simpa using hmodel 7 (by decide)

theorem oldMarkerAddr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldMarkerAddr I).toNat = (hashPadPtr I).toNat + I.calldata.size := by
  simpa [oldMarkerAddr, hashMarkerAddr] using hashMarkerAddr_toNat I hsmall

private theorem hashPaddedLengthWord_sub_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (b : UInt256)
    (hb : b.toNat ≤ 8) :
    (hashPaddedLengthWord I - b).toNat =
      Model.paddedLength I.calldata.size - b.toNat := by
  have hdiv : 1 ≤ (I.calldata.size + 72) / 64 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 64)]
    omega
  have hle : b.toNat ≤ (hashPaddedLengthWord I).toNat := by
    rw [hashPaddedLengthWord_toNat I hsmall]
    unfold Model.paddedLength
    omega
  change (UInt256.sub (hashPaddedLengthWord I) b).toNat = _
  rw [usub_toNat hle, hashPaddedLengthWord_toNat I hsmall]

theorem oldLengthAddr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat}
    (hq : q < 8) :
    (oldLengthAddr I q).toNat =
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 + q := by
  have hplen := hashPaddedLengthWord_toNat I hsmall
  have hptr := hashPadPtr_toNat I hsmall
  have hb := (hashPaddedLength_bounds I.calldata.size).2
  have hdiv : 1 ≤ (I.calldata.size + 72) / 64 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 64)]
    omega
  have hpad8 : 8 ≤ Model.paddedLength I.calldata.size := by
    unfold Model.paddedLength
    omega
  have hsum :
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size < 2 ^ 256 := by
    rw [hptr]
    unfold maxFallbackCalldataSize at hsmall
    omega
  interval_cases q <;>
    simp only [oldLengthAddr] <;>
    rw [uadd_toNat, hashPaddedLengthWord_sub_toNat I hsmall _ (by decide)] <;>
    simp only [show (⟨1⟩ : UInt256).toNat = 1 from by decide,
      show (⟨2⟩ : UInt256).toNat = 2 from by decide,
      show (⟨3⟩ : UInt256).toNat = 3 from by decide,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨5⟩ : UInt256).toNat = 5 from by decide,
      show (⟨6⟩ : UInt256).toNat = 6 from by decide,
      show (⟨7⟩ : UInt256).toNat = 7 from by decide,
      show (⟨8⟩ : UInt256).toNat = 8 from by decide] <;>
    norm_num <;>
    rw [show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt] <;>
    omega

theorem runtimeMstore8Mem_size_eq_of_inbounds (mem : ByteArray)
    (addr value : UInt256) (haddr : addr.toNat + 1 ≤ mem.size) :
    (runtimeMstore8Mem mem addr value).size = mem.size := by
  unfold runtimeMstore8Mem
  apply write_size_of_inbounds_from
  · decide
  · change 1 ≤ 1
    omega
  · exact haddr

theorem runtimeStore8Cursor_readSelf {c : RuntimeMemCursor} {addr value : UInt256}
    (haddr : addr.toNat + 1 ≤ c.mem.size) :
    (runtimeStore8Cursor c addr value).mem.readWithPadding addr.toNat 1 =
      ⟨#[UInt8.ofNat value.toNat]⟩ := by
  unfold runtimeStore8Cursor runtimeMstore8Mem
  simpa using write_read_window_from
    (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) c.mem 0 addr.toNat 1 0 1
    (by decide) (by change 1 ≤ 1; omega) (by omega) (by omega) (by omega) (by omega)

theorem runtimeStore8Cursor_readOther {c : RuntimeMemCursor} {addr value : UInt256}
    {read : Nat} (haddr : addr.toNat + 1 ≤ c.mem.size)
    (hread : read + 1 ≤ c.mem.size) (hne : read ≠ addr.toNat) :
    (runtimeStore8Cursor c addr value).mem.readWithPadding read 1 =
      c.mem.readWithPadding read 1 := by
  unfold runtimeStore8Cursor runtimeMstore8Mem
  by_cases hbelow : read < addr.toNat
  · exact write_read_below_len_from
      (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) c.mem
      0 addr.toNat 1 read 1 (by decide) (by change 1 ≤ 1; omega)
      haddr (by omega) (by decide) (by decide)
  · exact write_read_above_len_from
      (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) c.mem
      0 addr.toNat 1 read 1 (by decide) (by change 1 ≤ 1; omega)
      haddr (by omega) hread (by decide) (by decide)

theorem runtimeMstore8Aw_lt_pow64 {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 32 < 32 * (2 ^ 64)) :
    (runtimeMstore8Aw aw addr).toNat < 2 ^ 64 := by
  unfold runtimeMstore8Aw
  have hm : MachineState.M aw.toNat addr.toNat 1 < 2 ^ 64 := by
    simp only [MachineState.M, OfNat.ofNat]
    rw [max_lt_iff]
    refine ⟨haw, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    omega
  rw [ulit_toNat' _ (lt_trans hm (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    norm_num))]
  exact hm

theorem runtimeMstore8Aw_coversEnd {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 32 < 32 * (2 ^ 64)) :
    addr.toNat + 1 ≤ 32 * (runtimeMstore8Aw aw addr).toNat := by
  have hout := runtimeMstore8Aw_lt_pow64 haw haddr
  unfold runtimeMstore8Aw
  rw [ulit_toNat' _ (machineM_lt_uint256 aw addr.toNat 1 (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega))]
  unfold MachineState.M
  simp only [OfNat.ofNat]
  have hm := Nat.mod_lt (addr.toNat + 32) (by decide : 0 < 32)
  have hd := Nat.mod_add_div (addr.toNat + 32) 32
  have hceil : addr.toNat + 1 ≤ 32 * ((addr.toNat + 32) / 32) := by
    rw [show addr.toNat + 32 = addr.toNat + 1 * 32 by omega,
      Nat.add_mul_div_right _ _ (by decide : 0 < 32)]
    have hmod := Nat.mod_lt addr.toNat (by decide : 0 < 32)
    have hdecomp := Nat.mod_add_div addr.toNat 32
    omega
  apply le_trans (b := 32 * ((addr.toNat + 32) / 32))
  · exact hceil
  · exact Nat.mul_le_mul_left 32 (Nat.le_max_right _ _)

theorem runtimeMstoreAw_coversEnd {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    addr.toNat + 32 ≤ 32 * (runtimeMstoreAw aw addr).toNat := by
  have hm : MachineState.M aw.toNat addr.toNat 32 < 2 ^ 64 := by
    simp only [MachineState.M]
    rw [max_lt_iff]
    refine ⟨haw, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    exact haddr
  unfold runtimeMstoreAw
  rw [ulit_toNat' _ (lt_trans hm (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    norm_num))]
  unfold MachineState.M
  simp only
  have hm := Nat.mod_lt (addr.toNat + 63) (by decide : 0 < 32)
  have hd := Nat.mod_add_div (addr.toNat + 63) 32
  apply le_trans (b := 32 * ((addr.toNat + 63) / 32))
  · omega
  · exact Nat.mul_le_mul_left 32 (Nat.le_max_right _ _)

theorem oldCopyCursor_activeCover (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldCopyIterations I) :
    (hashPadPtr I).toNat + 32 * i ≤ 32 * (oldCopyCursor I i).aw.toNat := by
  induction i with
  | zero =>
      simp only [oldCopyCursor, Nat.mul_zero, Nat.add_zero]
      rw [hashPadPtr_toNat I hsmall, fallbackPaddedAw_toNat I hsmall]
      have hdiv := Nat.mod_add_div (I.calldata.size + 31) 32
      have hmod := Nat.mod_lt (I.calldata.size + 31) (by decide : 0 < 32)
      have hdiv' := Nat.mod_add_div (I.calldata.size + 223) 32
      have hmod' := Nat.mod_lt (I.calldata.size + 223) (by decide : 0 < 32)
      omega
  | succ i ih =>
      have hip : i ≤ oldCopyIterations I := by omega
      have hit : i < oldCopyIterations I := by omega
      obtain ⟨haw, _, _, _⟩ := oldCopyCursor_invariant I hsmall hip
      have hsrc := oldCopySource_toNat I i hsmall hit
      have hdst := oldCopyDest_toNat I i hsmall hip
      have hsrcBound : (oldCopySourceAddr i).toNat + 63 < 32 * (2 ^ 64) := by
        rw [hsrc]
        have hb := oldCopy_body_lt I hit
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hloadAw :
          (runtimeLoadCursor (oldCopyCursor I i) (oldCopySourceAddr i)).aw.toNat <
            2 ^ 64 := by
        simpa [runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
          runtimeMstoreAw_lt_pow64 haw hsrcBound
      have hdstBound : (oldCopyDestAddr I i).toNat + 63 < 32 * (2 ^ 64) := by
        rw [hdst, hashPadPtr_toNat I hsmall]
        have hb := oldCopy_body_lt I hit
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hcovers := runtimeMstoreAw_coversEnd hloadAw hdstBound
      have hload := (oldCopyCursor_invariant I hsmall hip).2.2.1 i hit
      rw [oldCopyCursor, hload.load]
      rw [hdst] at hcovers
      simpa [Nat.mul_add, Nat.add_assoc] using hcovers

theorem oldZeroCursor_activeCover (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldZeroIterations I) :
    (hashPadPtr I).toNat + oldZeroIndex I i ≤
      32 * (oldZeroCursor I i).aw.toNat := by
  induction i with
  | zero =>
      simpa [oldZeroCursor, oldZeroIndex] using
        oldCopyCursor_activeCover I hsmall (le_refl (oldCopyIterations I))
  | succ i ih =>
      have hip : i ≤ oldZeroIterations I := by omega
      have hit : i < oldZeroIterations I := by omega
      obtain ⟨haw, _, _, _⟩ := oldZeroCursor_invariant I hsmall hip
      have haddr := oldZeroDest_toNat I i hsmall hip
      have hbound : (hashPadPtr I + oldZeroIndexWord I i).toNat + 63 <
          32 * (2 ^ 64) := by
        rw [haddr, hashPadPtr_toNat I hsmall]
        have hz := oldZeroIndex_before_end I hit
        have hp := (hashPaddedLength_bounds I.calldata.size).2
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hcovers := runtimeMstoreAw_coversEnd haw hbound
      simp only [oldZeroCursor]
      change (hashPadPtr I).toNat + oldZeroIndex I (i + 1) ≤
        32 * (runtimeMstoreAw (oldZeroCursor I i).aw
          (hashPadPtr I + oldZeroIndexWord I i)).toNat
      rw [haddr] at hcovers
      unfold oldZeroIndex at hcovers ⊢
      simpa [Nat.mul_add, Nat.add_assoc] using hcovers

theorem runtimeMstore8Aw_ge {aw addr : UInt256}
    (haddr : addr.toNat + 32 < 32 * UInt256.size) :
    aw.toNat ≤ (runtimeMstore8Aw aw addr).toNat := by
  unfold runtimeMstore8Aw
  exact machineM_ofNat_ge aw addr.toNat 1 (by omega)

private theorem oldZeroFinal_bounds (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldZeroCursor I (oldZeroIterations I)).aw.toNat < 2 ^ 64 ∧
    (hashScratchPtr I).toNat ≤
      32 * (oldZeroCursor I (oldZeroIterations I)).aw.toNat ∧
    (hashScratchPtr I).toNat ≤
      (oldZeroCursor I (oldZeroIterations I)).mem.size := by
  obtain ⟨haw, hmem, _, _⟩ :=
    oldZeroCursor_invariant I hsmall (le_refl (oldZeroIterations I))
  have hactive := oldZeroCursor_activeCover I hsmall
    (le_refl (oldZeroIterations I))
  rw [oldZeroIndex_at_end I] at hmem hactive
  unfold hashScratchPtr
  rw [hashNewFreePtr_toNat I hsmall]
  exact ⟨haw, hactive, hmem⟩

theorem oldMarkerAddr_end_le_scratch (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldMarkerAddr I).toNat + 1 ≤ (hashScratchPtr I).toNat := by
  unfold hashScratchPtr
  rw [oldMarkerAddr_toNat I hsmall, hashNewFreePtr_toNat I hsmall]
  have hp := (hashPaddedLength_bounds I.calldata.size).1
  omega

theorem oldLengthAddr_end_le_scratch (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat} (hq : q < 8) :
    (oldLengthAddr I q).toNat + 1 ≤ (hashScratchPtr I).toNat := by
  unfold hashScratchPtr
  rw [oldLengthAddr_toNat I hsmall hq, hashNewFreePtr_toNat I hsmall]
  have hpad : 8 ≤ Model.paddedLength I.calldata.size := by
    have hp := (hashPaddedLength_bounds I.calldata.size).1
    omega
  omega

theorem oldLengthCursor_bounds (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat} (hq : q ≤ 8) :
    (oldLengthCursor I q).aw.toNat < 2 ^ 64 ∧
    (hashScratchPtr I).toNat ≤ 32 * (oldLengthCursor I q).aw.toNat ∧
    (hashScratchPtr I).toNat ≤ (oldLengthCursor I q).mem.size := by
  have hwide : (hashScratchPtr I).toNat + 31 < 32 * (2 ^ 64) := by
    change (hashNewFreePtr I).toNat + 31 < 32 * (2 ^ 64)
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hz := oldZeroFinal_bounds I hsmall
  have hmarkerEnd := oldMarkerAddr_end_le_scratch I hsmall
  have hmarkerIn :
      (oldMarkerAddr I).toNat + 1 ≤
        (oldZeroCursor I (oldZeroIterations I)).mem.size :=
    le_trans hmarkerEnd hz.2.2
  have hmarkerAw : (oldMarkerCursor I).aw.toNat < 2 ^ 64 := by
    apply runtimeMstore8Aw_lt_pow64 hz.1
    omega
  have hmarkerActive :
      (hashScratchPtr I).toNat ≤ 32 * (oldMarkerCursor I).aw.toNat := by
    apply le_trans hz.2.1
    exact Nat.mul_le_mul_left 32 (runtimeMstore8Aw_ge (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega))
  have hmarkerMem :
      (hashScratchPtr I).toNat ≤ (oldMarkerCursor I).mem.size := by
    rw [show (oldMarkerCursor I).mem.size =
      (oldZeroCursor I (oldZeroIterations I)).mem.size by
        apply runtimeMstore8Mem_size_eq_of_inbounds
        exact hmarkerIn]
    exact hz.2.2
  induction q with
  | zero => exact ⟨hmarkerAw, hmarkerActive, hmarkerMem⟩
  | succ q ih =>
      have hq8 : q < 8 := by omega
      obtain ⟨haw, hactive, hmem⟩ := ih (by omega)
      have hend := oldLengthAddr_end_le_scratch I hsmall hq8
      have hin : (oldLengthAddr I q).toNat + 1 ≤
          (oldLengthCursor I q).mem.size := le_trans hend hmem
      have haw' : (oldLengthCursor I (q + 1)).aw.toNat < 2 ^ 64 := by
        simp only [oldLengthCursor]
        apply runtimeMstore8Aw_lt_pow64 haw
        omega
      have hactive' :
          (hashScratchPtr I).toNat ≤
            32 * (oldLengthCursor I (q + 1)).aw.toNat := by
        simp only [oldLengthCursor]
        apply le_trans hactive
        exact Nat.mul_le_mul_left 32 (runtimeMstore8Aw_ge (by
          rw [show UInt256.size = 2 ^ 256 from by decide]
          omega))
      have hmem' :
          (hashScratchPtr I).toNat ≤ (oldLengthCursor I (q + 1)).mem.size := by
        simp only [oldLengthCursor]
        change (hashScratchPtr I).toNat ≤
          (runtimeMstore8Mem (oldLengthCursor I q).mem
            (oldLengthAddr I q) (oldLengthByte I q)).size
        rw [runtimeMstore8Mem_size_eq_of_inbounds _ _ _ hin]
        exact hmem
      exact ⟨haw', hactive', hmem'⟩

private theorem oldLengthCursor_read_fromMarker (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {n read : Nat}
    (hn : n ≤ 8) (hread : read + 1 ≤ (hashScratchPtr I).toNat)
    (hne : ∀ q, q < n → read ≠ (oldLengthAddr I q).toNat) :
    (oldLengthCursor I n).mem.readWithPadding read 1 =
      (oldMarkerCursor I).mem.readWithPadding read 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hb := oldLengthCursor_bounds I hsmall (q := n) (by omega)
      have hend := oldLengthAddr_end_le_scratch I hsmall hn8
      have haddr : (oldLengthAddr I n).toNat + 1 ≤
          (oldLengthCursor I n).mem.size := le_trans hend hb.2.2
      have hr : read + 1 ≤ (oldLengthCursor I n).mem.size :=
        le_trans hread hb.2.2
      simp only [oldLengthCursor]
      rw [runtimeStore8Cursor_readOther haddr hr (hne n (by omega))]
      exact ih (by omega) (fun q hq => hne q (by omega))

private theorem oldLengthCursor_read_fromZero (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {read : Nat}
    (hread : read + 1 ≤ (hashScratchPtr I).toNat)
    (hmarker : read ≠ (oldMarkerAddr I).toNat)
    (hlength : ∀ q, q < 8 → read ≠ (oldLengthAddr I q).toNat) :
    (oldLengthCursor I 8).mem.readWithPadding read 1 =
      (oldZeroCursor I (oldZeroIterations I)).mem.readWithPadding read 1 := by
  rw [oldLengthCursor_read_fromMarker I hsmall (by decide) hread hlength]
  have hz := oldZeroFinal_bounds I hsmall
  have hend := oldMarkerAddr_end_le_scratch I hsmall
  unfold oldMarkerCursor
  exact runtimeStore8Cursor_readOther (le_trans hend hz.2.2)
    (le_trans hread hz.2.2) hmarker

private theorem oldLengthCursor_readMarker (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldLengthCursor I 8).mem.readWithPadding (oldMarkerAddr I).toNat 1 =
      ⟨#[128]⟩ := by
  have hread := oldMarkerAddr_end_le_scratch I hsmall
  rw [oldLengthCursor_read_fromMarker I hsmall (by decide) hread]
  · have hz := oldZeroFinal_bounds I hsmall
    unfold oldMarkerCursor
    exact runtimeStore8Cursor_readSelf (le_trans hread hz.2.2)
  · intro q hq heq
    have hm := oldMarkerAddr_toNat I hsmall
    have hl := oldLengthAddr_toNat I hsmall hq
    have hp := (hashPaddedLength_bounds I.calldata.size).1
    rw [hm, hl] at heq
    omega

private theorem oldLengthCursor_readLength (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {n q : Nat}
    (hn : n ≤ 8) (hq : q < n) :
    (oldLengthCursor I n).mem.readWithPadding (oldLengthAddr I q).toNat 1 =
      ⟨#[UInt8.ofNat (oldLengthByte I q).toNat]⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hb := oldLengthCursor_bounds I hsmall (q := n) (by omega)
      have hendN := oldLengthAddr_end_le_scratch I hsmall hn8
      have haddrN : (oldLengthAddr I n).toNat + 1 ≤
          (oldLengthCursor I n).mem.size := le_trans hendN hb.2.2
      by_cases hqn : q < n
      · have hq8 : q < 8 := by omega
        have hendQ := oldLengthAddr_end_le_scratch I hsmall hq8
        have hreadQ : (oldLengthAddr I q).toNat + 1 ≤
            (oldLengthCursor I n).mem.size := le_trans hendQ hb.2.2
        have hne : (oldLengthAddr I q).toNat ≠ (oldLengthAddr I n).toNat := by
          intro heq
          rw [oldLengthAddr_toNat I hsmall hq8,
            oldLengthAddr_toNat I hsmall hn8] at heq
          omega
        simp only [oldLengthCursor]
        rw [runtimeStore8Cursor_readOther haddrN hreadQ hne]
        exact ih (by omega) hqn
      · have hqeq : q = n := by omega
        subst q
        simp only [oldLengthCursor]
        exact runtimeStore8Cursor_readSelf haddrN

/-- The old padding implementation produces the same byte-level padded message as the model. -/
theorem oldLengthCursor_padded (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (oldLengthCursor I 8) 0 := by
  have hb := oldLengthCursor_bounds I hsmall (q := 8) (by decide)
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · simpa using hb.2.2
  · intro p hp
    have hread : (hashPadPtr I).toNat + p + 1 ≤
        (hashScratchPtr I).toNat := by
      unfold hashScratchPtr
      rw [hashNewFreePtr_toNat I hsmall]
      omega
    unfold Model.paddedByte
    dsimp only
    by_cases hdata : p < I.calldata.size
    · rw [dif_pos hdata]
      rw [oldLengthCursor_read_fromZero I hsmall hread]
      · rw [oldZeroFinal_readData I hsmall hdata]
        rw [byteArray_extract_one I.calldata p hdata]
        congr 3
        exact UInt8.ofNat_toNat.symm
      · rw [oldMarkerAddr_toNat I hsmall]
        omega
      · intro q hq heq
        rw [oldLengthAddr_toNat I hsmall hq] at heq
        have htail := (hashPaddedLength_bounds I.calldata.size).1
        omega
    · rw [dif_neg hdata]
      by_cases hmarker : p = I.calldata.size
      · rw [if_pos hmarker]
        subst p
        rw [show (hashPadPtr I).toNat + I.calldata.size =
          (oldMarkerAddr I).toNat by rw [oldMarkerAddr_toNat I hsmall]]
        exact oldLengthCursor_readMarker I hsmall
      · rw [if_neg hmarker]
        by_cases htail : Model.paddedLength I.calldata.size - 8 ≤ p
        · rw [if_pos htail]
          let q := p - (Model.paddedLength I.calldata.size - 8)
          have hq : q < 8 := by dsimp [q]; omega
          have hpq :
              (hashPadPtr I).toNat + p = (oldLengthAddr I q).toNat := by
            rw [oldLengthAddr_toNat I hsmall hq]
            dsimp only [q]
            have hpad := (hashPaddedLength_bounds I.calldata.size).1
            omega
          rw [hpq, oldLengthCursor_readLength I hsmall (n := 8) (by decide) hq]
          congr 3
          rw [oldLengthByte_toNat I hsmall hq]
        · rw [if_neg htail]
          have hpdata : I.calldata.size ≤ p := by omega
          rw [oldLengthCursor_read_fromZero I hsmall hread]
          · by_cases hcopy : p < 32 * oldCopyIterations I
            · exact oldZeroFinal_readCopiedZero I hsmall hpdata hcopy
            · exact oldZeroFinal_readZero I hsmall (by omega) hp
          · rw [oldMarkerAddr_toNat I hsmall]
            omega
          · intro q hq heq
            rw [oldLengthAddr_toNat I hsmall hq] at heq
            omega

end Ripemd160Old
