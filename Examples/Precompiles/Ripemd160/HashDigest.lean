import Examples.Precompiles.Ripemd160.HashPure

/-!
# RIPEMD-160 digest serializer bridge

This module connects the runtime's packed return word to the pure model's 32-byte raw output.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem nat_and_mod_two_pow_of_lt (a mask k : Nat) (hm : mask < 2 ^ k) :
    (a % 2 ^ k) &&& mask = a &&& mask := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · simp [hi]
  · have hmask : mask.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi, hmask]

theorem nat_swap32_identity (n : Nat) (hn : n < 2 ^ 32) :
    (n >>> 24 &&& 0xff) ||| (n >>> 8 &&& 0xff00) |||
      (n <<< 8 &&& 0xff0000) ||| (n <<< 24 &&& 0xff000000) =
    ((n &&& 0xff) <<< 24) ||| (((n >>> 8) &&& 0xff) <<< 16) |||
      (((n >>> 16) &&& 0xff) <<< 8) ||| ((n >>> 24) &&& 0xff) := by
  let x : BitVec 32 := BitVec.ofNat 32 n
  have hb :
      ((x >>> 24) &&& 0xff) ||| ((x >>> 8) &&& 0xff00) |||
          ((x <<< 8) &&& 0xff0000) ||| ((x <<< 24) &&& 0xff000000) =
        ((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16) |||
          (((x >>> 16) &&& 0xff) <<< 8) ||| ((x >>> 24) &&& 0xff) := by
    bv_decide
  have h := congrArg BitVec.toNat hb
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, x, BitVec.toNat_ofNat] at h
  norm_num [BitVec.toNat_ofNat] at h
  rw [show BitVec.toNat (255 : BitVec 32) = 255 by decide,
    show BitVec.toNat (65280 : BitVec 32) = 65280 by decide,
    show BitVec.toNat (16711680 : BitVec 32) = 16711680 by decide,
    show BitVec.toNat (4278190080 : BitVec 32) = 4278190080 by decide] at h
  have hmod : n % 4294967296 = n := Nat.mod_eq_of_lt (by simpa using hn)
  rw [hmod] at h
  have hleft8 := nat_and_mod_two_pow_of_lt (n <<< 8) 0xff0000 32 (by norm_num)
  have hleft24 := nat_and_mod_two_pow_of_lt (n <<< 24) 0xff000000 32 (by norm_num)
  norm_num at hleft8 hleft24
  rw [hleft8, hleft24] at h
  have hs24 : (n &&& 255) <<< 24 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    have hb : n &&& 255 ≤ 255 := Nat.and_le_right
    norm_num
    omega
  have hs16 : (n >>> 8 &&& 255) <<< 16 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    have hb : n >>> 8 &&& 255 ≤ 255 := Nat.and_le_right
    norm_num
    omega
  have hs8 : (n >>> 16 &&& 255) <<< 8 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    have hb : n >>> 16 &&& 255 ≤ 255 := Nat.and_le_right
    norm_num
    omega
  rw [Nat.mod_eq_of_lt hs24, Nat.mod_eq_of_lt hs16, Nat.mod_eq_of_lt hs8] at h
  exact h

theorem runtimeSwap32_toNat {x : UInt256} (hx : x.toNat < 2 ^ 32) :
    (runtimeSwap32 x).toNat =
      ((x.toNat &&& 0xff) <<< 24) |||
      (((x.toNat >>> 8) &&& 0xff) <<< 16) |||
      (((x.toNat >>> 16) &&& 0xff) <<< 8) |||
      ((x.toNat >>> 24) &&& 0xff) := by
  unfold runtimeSwap32
  simp only [u256_lor_toNat, uland_toNat]
  rw [show (⟨24⟩ : UInt256) = UInt256.ofNat 24 from rfl,
    show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from rfl]
  rw [ushr_ofNat_toNat x 24 (by decide),
    ushr_ofNat_toNat x 8 (by decide),
    ushl_ofNat_toNat x 8 (by decide),
    ushl_ofNat_toNat x 24 (by decide)]
  simp only [show (⟨0xff⟩ : UInt256).toNat = 0xff by decide,
    show (⟨0xff00⟩ : UInt256).toNat = 0xff00 by decide,
    show (⟨0xff0000⟩ : UInt256).toNat = 0xff0000 by decide,
    show (⟨0xff000000⟩ : UInt256).toNat = 0xff000000 by decide]
  have hx8 : x.toNat <<< 8 < UInt256.size := by
    rw [Nat.shiftLeft_eq, UInt256.size]
    norm_num
    omega
  have hx24 : x.toNat <<< 24 < UInt256.size := by
    rw [Nat.shiftLeft_eq, UInt256.size]
    norm_num
    omega
  rw [Nat.mod_eq_of_lt hx8, Nat.mod_eq_of_lt hx24]
  change (((x.toNat >>> 24 &&& 255 ||| x.toNat >>> 8 &&& 65280) % UInt256.size |||
      (x.toNat <<< 8 &&& 16711680 ||| x.toNat <<< 24 &&& 4278190080) % UInt256.size) %
        UInt256.size) = _
  have ha : x.toNat >>> 24 &&& 255 < 2 ^ 32 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hb : x.toNat >>> 8 &&& 65280 < 2 ^ 32 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hc : x.toNat <<< 8 &&& 16711680 < 2 ^ 32 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hd : x.toNat <<< 24 &&& 4278190080 < 2 ^ 32 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hab := Nat.or_lt_two_pow ha hb
  have hcd := Nat.or_lt_two_pow hc hd
  have hall := Nat.or_lt_two_pow hab hcd
  have hab256 : x.toNat >>> 24 &&& 255 ||| x.toNat >>> 8 &&& 65280 < 2 ^ 256 :=
    lt_trans hab (by norm_num)
  have hcd256 : x.toNat <<< 8 &&& 16711680 |||
      x.toNat <<< 24 &&& 4278190080 < 2 ^ 256 :=
    lt_trans hcd (by norm_num)
  have hall256 : x.toNat >>> 24 &&& 255 ||| x.toNat >>> 8 &&& 65280 |||
      (x.toNat <<< 8 &&& 16711680 ||| x.toNat <<< 24 &&& 4278190080) < 2 ^ 256 :=
    lt_trans hall (by norm_num)
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_eq_of_lt hab256,
    Nat.mod_eq_of_lt hcd256,
    Nat.mod_eq_of_lt hall256]
  simpa [Nat.or_assoc] using nat_swap32_identity x.toNat hx

def Model.rawOutputOfChain (h : Model.ChainState) : ByteArray :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ++
    (Model.wordLE h.h0 ++ Model.wordLE h.h1 ++ Model.wordLE h.h2 ++
      Model.wordLE h.h3 ++ Model.wordLE h.h4).toByteArray

theorem Model.rawOutput_eq (data : ByteArray) :
    Model.rawOutput data = Model.rawOutputOfChain (Model.finalState data) := by
  rfl

def Model.swap32Nat (w : Nat) : Nat :=
  (w >>> 24) % 256 + 256 * ((w >>> 16) % 256 +
    256 * ((w >>> 8) % 256 + 256 * (w % 256)))

theorem bv_swap32_eq_arith (x : BitVec 32) :
    ((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16) |||
        (((x >>> 16) &&& 0xff) <<< 8) ||| ((x >>> 24) &&& 0xff) =
      ((x >>> 24) &&& 0xff) + 256 * (((x >>> 16) &&& 0xff) +
        256 * (((x >>> 8) &&& 0xff) + 256 * (x &&& 0xff))) := by
  bv_decide

theorem nat_swap32_eq_arith (n : Nat) (hn : n < 2 ^ 32) :
    ((n &&& 0xff) <<< 24) ||| (((n >>> 8) &&& 0xff) <<< 16) |||
        (((n >>> 16) &&& 0xff) <<< 8) ||| ((n >>> 24) &&& 0xff) =
      Model.swap32Nat n := by
  have h := congrArg BitVec.toNat
    (bv_swap32_eq_arith (BitVec.ofNat 32 n))
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofNat] at h
  norm_num at h
  rw [show BitVec.toNat (255 : BitVec 32) = 255 by decide,
    show BitVec.toNat (256 : BitVec 32) = 256 by decide] at h
  have hmod : n % 4294967296 = n := Nat.mod_eq_of_lt (by simpa using hn)
  rw [hmod] at h
  have hmask (x : Nat) : x &&& 255 = x % 256 := by
    simpa using nat_land_mask_eq_mod x 8
  simp_rw [hmask] at h ⊢
  unfold Model.swap32Nat
  have hb0 : n % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb1 : (n >>> 8) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb2 : (n >>> 16) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb3 : (n >>> 24) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hs24 : (n % 256) <<< 24 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hs16 : ((n >>> 8) % 256) <<< 16 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hs8 : ((n >>> 16) % 256) <<< 8 < 4294967296 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have htotal : (n >>> 24) % 256 +
      256 * ((n >>> 16) % 256 +
        256 * ((n >>> 8) % 256 + 256 * (n % 256))) < 4294967296 := by
    omega
  rw [Nat.mod_eq_of_lt hs24, Nat.mod_eq_of_lt hs16,
    Nat.mod_eq_of_lt hs8, Nat.mod_eq_of_lt htotal] at h
  exact h

theorem Model.swap32Nat_lt (w : Nat) : Model.swap32Nat w < 2 ^ 32 := by
  have h0 : w % 256 < 256 := Nat.mod_lt _ (by decide)
  have h1 : (w >>> 8) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h2 : (w >>> 16) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h3 : (w >>> 24) % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold Model.swap32Nat
  norm_num
  omega

theorem runtimeSwap32_model {x : UInt256} (hx : x.toNat < 2 ^ 32) :
    (runtimeSwap32 x).toNat = Model.swap32Nat x.toNat :=
  (runtimeSwap32_toNat hx).trans (nat_swap32_eq_arith x.toNat hx)

theorem runtimeSwap32_lt_of_lt {x : UInt256} (hx : x.toNat < 2 ^ 32) :
    (runtimeSwap32 x).toNat < 2 ^ 32 := by
  rw [runtimeSwap32_model hx]
  exact Model.swap32Nat_lt _

def Model.packedDigestNat (h : Model.ChainState) : Nat :=
  (((Model.swap32Nat h.h4 + Model.swap32Nat h.h3 * 2 ^ 32) +
      Model.swap32Nat h.h2 * 2 ^ 64) + Model.swap32Nat h.h1 * 2 ^ 96) +
    Model.swap32Nat h.h0 * 2 ^ 128

theorem nestedPack5_eq_expanded (a b c d e : Nat) :
    e + 2 ^ 32 * (d + 2 ^ 32 * (c + 2 ^ 32 * (b + 2 ^ 32 * a))) =
      (((e + d * 2 ^ 32) + c * 2 ^ 64) + b * 2 ^ 96) + a * 2 ^ 128 := by
  ring

theorem Model.packedDigestNat_lt (h : Model.ChainState) :
    Model.packedDigestNat h < 2 ^ 160 := by
  have h0 := Model.swap32Nat_lt h.h0
  have h1 := Model.swap32Nat_lt h.h1
  have h2 := Model.swap32Nat_lt h.h2
  have h3 := Model.swap32Nat_lt h.h3
  have h4 := Model.swap32Nat_lt h.h4
  unfold Model.packedDigestNat
  omega

theorem packFourBytes (a b c d rest : Nat) :
    a + 256 * (b + 256 * (c + 256 * (d + 256 * rest))) =
      (a + 256 * (b + 256 * (c + 256 * d))) + 2 ^ 32 * rest := by
  ring

theorem fromBytes'_reverse_wordLE (w : Nat) :
    Ethereum.fromBytes' (Model.wordLE w).reverse = Model.swap32Nat w := by
  simp [Model.wordLE, Model.swap32Nat, Ethereum.fromBytes']

@[simp] theorem Model.rawOutputOfChain_size (h : Model.ChainState) :
    (Model.rawOutputOfChain h).size = 32 := by
  unfold Model.rawOutputOfChain Model.wordLE
  rw [ByteArray.size_append, list_toByteArray_size]
  have hz : (⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray).size = 12 := by
    native_decide
  rw [hz]
  simp

theorem rawOutputOfChain_word_toNat (h : Model.ChainState) :
    (ABI.bytesToWord (Model.rawOutputOfChain h).toList).toNat =
      Model.packedDigestNat h := by
  have hlt : Model.packedDigestNat h < UInt256.size :=
    lt_trans (Model.packedDigestNat_lt h) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      norm_num)
  have hdecode : Ethereum.fromByteArrayBigEndian
      (ByteArray.mk (Model.rawOutputOfChain h).toList.toArray) =
        Model.packedDigestNat h := by
    have hout : (Model.rawOutputOfChain h).toList =
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
          (Model.wordLE h.h0 ++ Model.wordLE h.h1 ++ Model.wordLE h.h2 ++
            Model.wordLE h.h3 ++ Model.wordLE h.h4) := by
      unfold Model.rawOutputOfChain
      rw [byteArray_toList_eq, ByteArray.data_append, Array.toList_append]
      simp
    unfold Ethereum.fromByteArrayBigEndian Ethereum.fromBytesBigEndian Function.comp
    rw [byteArray_toList_eq]
    simp
    rw [hout]
    simp only [List.reverse_append]
    repeat' rw [fromBytes'_append]
    simp only [fromBytes'_reverse_wordLE]
    simp [Model.wordLE, Ethereum.fromBytes']
    exact nestedPack5_eq_expanded _ _ _ _ _
  unfold ABI.bytesToWord
  rw [hdecode, ulit_toNat' _ hlt]

def runtimePack5 (a b c d e : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft a ⟨128⟩)
    (UInt256.lor (UInt256.shiftLeft b ⟨96⟩)
      (UInt256.lor (UInt256.shiftLeft c ⟨64⟩)
        (UInt256.lor (UInt256.shiftLeft d ⟨32⟩) e)))

/-
theorem runtimePrepend_toNat_and_lt {high low : UInt256} {m k : Nat}
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32)
    (he : e.toNat < 2 ^ 32) :
    (runtimePack5 a b c d e).toNat =
      (((e.toNat + d.toNat * 2 ^ 32) + c.toNat * 2 ^ 64) +
        b.toNat * 2 ^ 96) + a.toNat * 2 ^ 128 := by
  unfold runtimePack5
  simp only [u256_lor_toNat]
  rw [show (⟨128⟩ : UInt256) = UInt256.ofNat 128 from rfl,
    show (⟨96⟩ : UInt256) = UInt256.ofNat 96 from rfl,
    show (⟨64⟩ : UInt256) = UInt256.ofNat 64 from rfl,
    show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl,
    ushl_ofNat_toNat a 128 (by decide), ushl_ofNat_toNat b 96 (by decide),
    ushl_ofNat_toNat c 64 (by decide), ushl_ofNat_toNat d 32 (by decide)]
  have hsa : a.toNat <<< 128 < UInt256.size := by
    have hs := Nat.shiftLeft_lt ha (m := 128)
    exact lt_trans (by simpa using hs) (by rw [UInt256.size]; norm_num)
  have hsb : b.toNat <<< 96 < UInt256.size := by
    have hs := Nat.shiftLeft_lt hb (m := 96)
    exact lt_trans (by simpa using hs) (by rw [UInt256.size]; norm_num)
  have hsc : c.toNat <<< 64 < UInt256.size := by
    have hs := Nat.shiftLeft_lt hc (m := 64)
    exact lt_trans (by simpa using hs) (by rw [UInt256.size]; norm_num)
  have hsd : d.toNat <<< 32 < UInt256.size := by
    have hs := Nat.shiftLeft_lt hd (m := 32)
    exact lt_trans (by simpa using hs) (by rw [UInt256.size]; norm_num)
  rw [Nat.mod_eq_of_lt hsa, Nat.mod_eq_of_lt hsb,
    Nat.mod_eq_of_lt hsc, Nat.mod_eq_of_lt hsd]
  change (a.toNat <<< 128 ||| ((b.toNat <<< 96 |||
      ((c.toNat <<< 64 ||| ((d.toNat <<< 32 ||| e.toNat) % UInt256.size)) %
        UInt256.size)) % UInt256.size)) % UInt256.size = _
  have hde : d.toNat <<< 32 ||| e.toNat =
      e.toNat + d.toNat * 2 ^ 32 := by
    calc
      d.toNat <<< 32 ||| e.toNat = e.toNat ||| d.toNat <<< 32 :=
        nat_lor_comm _ _
      _ = e.toNat ||| d.toNat * 2 ^ 32 := by rw [Nat.shiftLeft_eq, Nat.mul_comm]
      _ = e.toNat + d.toNat * 2 ^ 32 := nat_lor_shift_add e.toNat d.toNat 32 he
  have hde_lt : d.toNat <<< 32 ||| e.toNat < 2 ^ 64 := by
    exact Nat.or_lt_two_pow
      (by simpa using Nat.shiftLeft_lt hd (m := 32))
      (lt_trans he (by norm_num))
  have hcde : c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat) =
      (d.toNat <<< 32 ||| e.toNat) + c.toNat * 2 ^ 64 := by
    calc
      c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat) =
          (d.toNat <<< 32 ||| e.toNat) ||| c.toNat <<< 64 := nat_lor_comm _ _
      _ = (d.toNat <<< 32 ||| e.toNat) ||| c.toNat * 2 ^ 64 := by
        congr 1
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      _ = _ := nat_lor_shift_add _ c.toNat 64 hde_lt
  have hcde_lt : c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat) < 2 ^ 96 := by
    exact Nat.or_lt_two_pow
      (by simpa using Nat.shiftLeft_lt hc (m := 64))
      (lt_trans hde_lt (by norm_num))
  have hbcde : b.toNat <<< 96 |||
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) =
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) + b.toNat * 2 ^ 96 := by
    calc
      b.toNat <<< 96 ||| (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) =
          (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) ||| b.toNat <<< 96 :=
        nat_lor_comm _ _
      _ = (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) |||
          b.toNat * 2 ^ 96 := by
        congr 1
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      _ = _ := nat_lor_shift_add _ b.toNat 96 hcde_lt
  have hbcde_lt : b.toNat <<< 96 |||
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) < 2 ^ 128 := by
    exact Nat.or_lt_two_pow
      (by simpa using Nat.shiftLeft_lt hb (m := 96))
      (lt_trans hcde_lt (by norm_num))
  have habcde : a.toNat <<< 128 ||| (b.toNat <<< 96 |||
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat))) =
      (b.toNat <<< 96 ||| (c.toNat <<< 64 |||
        (d.toNat <<< 32 ||| e.toNat))) + a.toNat * 2 ^ 128 := by
    calc
      a.toNat <<< 128 ||| (b.toNat <<< 96 |||
          (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat))) =
          (b.toNat <<< 96 ||| (c.toNat <<< 64 |||
            (d.toNat <<< 32 ||| e.toNat))) ||| a.toNat <<< 128 := nat_lor_comm _ _
      _ = (b.toNat <<< 96 ||| (c.toNat <<< 64 |||
          (d.toNat <<< 32 ||| e.toNat))) ||| a.toNat * 2 ^ 128 := by
        congr 1
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      _ = _ := nat_lor_shift_add _ a.toNat 128 hbcde_lt
  have habcde_lt : a.toNat <<< 128 ||| (b.toNat <<< 96 |||
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat))) < UInt256.size := by
    rw [UInt256.size]
    exact lt_trans (Nat.or_lt_two_pow
      (by simpa using Nat.shiftLeft_lt ha (m := 128))
      (lt_trans hbcde_lt (by norm_num))) (by norm_num)
  have hde_uint : d.toNat <<< 32 ||| e.toNat < UInt256.size := by
    rw [UInt256.size]
    exact lt_trans hde_lt (by norm_num)
  have hcde_uint : c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat) <
      UInt256.size := by
    rw [UInt256.size]
    exact lt_trans hcde_lt (by norm_num)
  have hbcde_uint : b.toNat <<< 96 |||
      (c.toNat <<< 64 ||| (d.toNat <<< 32 ||| e.toNat)) < UInt256.size := by
    rw [UInt256.size]
    exact lt_trans hbcde_lt (by norm_num)
  rw [Nat.mod_eq_of_lt hde_uint,
    Nat.mod_eq_of_lt hcde_uint,
    Nat.mod_eq_of_lt hbcde_uint,
    Nat.mod_eq_of_lt habcde_lt]
  rw [habcde, hbcde, hcde, hde]
  rfl

#check runtimePack5_toNat
-/

theorem runtimePrepend_toNat_and_lt {high low : UInt256} {m k : Nat}
    (hk : k < 256) (hmk : m + k ≤ 256)
    (hhigh : high.toNat < 2 ^ m) (hlow : low.toNat < 2 ^ k) :
    (UInt256.lor (UInt256.shiftLeft high (UInt256.ofNat k)) low).toNat =
        low.toNat + high.toNat * 2 ^ k ∧
      (UInt256.lor (UInt256.shiftLeft high (UInt256.ofNat k)) low).toNat <
        2 ^ (m + k) := by
  have hshift := Nat.shiftLeft_lt hhigh (m := k)
  have hshift256 : high.toNat <<< k < UInt256.size := by
    exact lt_of_lt_of_le hshift (by
      rw [UInt256.size]
      exact Nat.pow_le_pow_right (by decide) hmk)
  have hlowWide : low.toNat < 2 ^ (m + k) :=
    lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by decide) (by omega))
  have hor : high.toNat <<< k ||| low.toNat < 2 ^ (m + k) :=
    Nat.or_lt_two_pow hshift hlowWide
  have hor256 : high.toNat <<< k ||| low.toNat < UInt256.size :=
    lt_of_lt_of_le hor (by
      rw [UInt256.size]
      exact Nat.pow_le_pow_right (by decide) hmk)
  have hpack : high.toNat <<< k ||| low.toNat =
      low.toNat + high.toNat * 2 ^ k := by
    calc
      high.toNat <<< k ||| low.toNat = low.toNat ||| high.toNat <<< k :=
        nat_lor_comm _ _
      _ = low.toNat ||| high.toNat * 2 ^ k := by
        congr 1
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      _ = low.toNat + high.toNat * 2 ^ k :=
        nat_lor_shift_add low.toNat high.toNat k hlow
  rw [u256_lor_toNat,
    ushl_ofNat_toNat high k hk,
    Nat.mod_eq_of_lt hshift256]
  change (high.toNat <<< k ||| low.toNat) % UInt256.size =
      low.toNat + high.toNat * 2 ^ k ∧
    (high.toNat <<< k ||| low.toNat) % UInt256.size < 2 ^ (m + k)
  rw [Nat.mod_eq_of_lt hor256, hpack]
  exact ⟨rfl, by simpa [← hpack] using hor⟩

theorem runtimePack5_toNat {a b c d e : UInt256}
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32)
    (he : e.toNat < 2 ^ 32) :
    (runtimePack5 a b c d e).toNat =
      (((e.toNat + d.toNat * 2 ^ 32) + c.toNat * 2 ^ 64) +
        b.toNat * 2 ^ 96) + a.toNat * 2 ^ 128 := by
  let de := UInt256.lor (UInt256.shiftLeft d (UInt256.ofNat 32)) e
  let cde := UInt256.lor (UInt256.shiftLeft c (UInt256.ofNat 64)) de
  let bcde := UInt256.lor (UInt256.shiftLeft b (UInt256.ofNat 96)) cde
  have hde := runtimePrepend_toNat_and_lt (m := 32) (k := 32)
    (by decide) (by decide) hd he
  have hcde := runtimePrepend_toNat_and_lt (high := c) (low := de)
    (m := 32) (k := 64) (by decide) (by decide) hc (by simpa [de] using hde.2)
  have hbcde := runtimePrepend_toNat_and_lt (high := b) (low := cde)
    (m := 32) (k := 96) (by decide) (by decide) hb (by simpa [cde] using hcde.2)
  have habcde := runtimePrepend_toNat_and_lt (high := a) (low := bcde)
    (m := 32) (k := 128) (by decide) (by decide) ha (by simpa [bcde] using hbcde.2)
  change (UInt256.lor (UInt256.shiftLeft a ⟨128⟩)
    (UInt256.lor (UInt256.shiftLeft b ⟨96⟩)
      (UInt256.lor (UInt256.shiftLeft c ⟨64⟩)
        (UInt256.lor (UInt256.shiftLeft d ⟨32⟩) e)))).toNat = _
  rw [show (⟨128⟩ : UInt256) = UInt256.ofNat 128 from rfl,
    show (⟨96⟩ : UInt256) = UInt256.ofNat 96 from rfl,
    show (⟨64⟩ : UInt256) = UInt256.ofNat 64 from rfl,
    show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl]
  change (UInt256.lor (UInt256.shiftLeft a (UInt256.ofNat 128)) bcde).toNat = _
  rw [habcde.1]
  rw [hbcde.1]
  rw [hcde.1]
  rw [hde.1]

theorem runtimeDigestPacked_toNat {runtime : RuntimeChain}
    {model : Model.ChainState} (hrep : RuntimeChainRep runtime model)
    (hbound : Model.ChainBound model) :
    (runtimeDigestPacked runtime).toNat = Model.packedDigestNat model := by
  rcases hrep with ⟨hr0, hr1, hr2, hr3, hr4⟩
  rcases hbound with ⟨hm0, hm1, hm2, hm3, hm4⟩
  have hb0 : runtime.h0.toNat < 2 ^ 32 := by simpa [hr0] using hm0
  have hb1 : runtime.h1.toNat < 2 ^ 32 := by simpa [hr1] using hm1
  have hb2 : runtime.h2.toNat < 2 ^ 32 := by simpa [hr2] using hm2
  have hb3 : runtime.h3.toNat < 2 ^ 32 := by simpa [hr3] using hm3
  have hb4 : runtime.h4.toNat < 2 ^ 32 := by simpa [hr4] using hm4
  change (runtimePack5 (runtimeSwap32 runtime.h0) (runtimeSwap32 runtime.h1)
    (runtimeSwap32 runtime.h2) (runtimeSwap32 runtime.h3)
    (runtimeSwap32 runtime.h4)).toNat = _
  rw [runtimePack5_toNat
    (runtimeSwap32_lt_of_lt hb0) (runtimeSwap32_lt_of_lt hb1)
    (runtimeSwap32_lt_of_lt hb2) (runtimeSwap32_lt_of_lt hb3)
    (runtimeSwap32_lt_of_lt hb4)]
  rw [runtimeSwap32_model hb0, runtimeSwap32_model hb1,
    runtimeSwap32_model hb2, runtimeSwap32_model hb3,
    runtimeSwap32_model hb4]
  simp [Model.packedDigestNat, hr0, hr1, hr2, hr3, hr4]

theorem runtimeDigestValue_toNat {runtime : RuntimeChain}
    {model : Model.ChainState} (hrep : RuntimeChainRep runtime model)
    (hbound : Model.ChainBound model) :
    (runtimeDigestValue runtime).toNat = Model.packedDigestNat model := by
  have hpacked := runtimeDigestPacked_toNat hrep hbound
  have hp160 : (runtimeDigestPacked runtime).toNat < 2 ^ 160 := by
    rw [hpacked]
    exact Model.packedDigestNat_lt model
  have hshift : (runtimeDigestPacked runtime).toNat <<< 96 < UInt256.size := by
    have hs := Nat.shiftLeft_lt hp160 (m := 96)
    simpa [UInt256.size] using hs
  unfold runtimeDigestValue
  rw [show (⟨96⟩ : UInt256) = UInt256.ofNat 96 from rfl,
    ushr_ofNat_toNat _ 96 (by decide), ushl_ofNat_toNat _ 96 (by decide),
    Nat.mod_eq_of_lt hshift]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp
  exact hpacked

theorem runtimeDigestValue_toByteArray {runtime : RuntimeChain}
    {model : Model.ChainState} (hrep : RuntimeChainRep runtime model)
    (hbound : Model.ChainBound model) :
    (runtimeDigestValue runtime).toByteArray = Model.rawOutputOfChain model := by
  have hword : runtimeDigestValue runtime =
      ABI.bytesToWord (Model.rawOutputOfChain model).toList := by
    apply u256_inj
    rw [runtimeDigestValue_toNat hrep hbound,
      rawOutputOfChain_word_toNat]
  rw [hword, toByteArray_eq_toBytesBE]
  have hbytes := toBytesBE_bytesToWord_of_length
    (bs := (Model.rawOutputOfChain model).toList) (by
      simp [byteArray_toList_eq])
  rw [hbytes]
  apply ByteArray.ext
  simp [byteArray_toList_eq]

theorem Model.chainBound_foldl (data : ByteArray) (blocks : List Nat)
    (h : Model.ChainState) (hbound : Model.ChainBound h) :
    Model.ChainBound
      (blocks.foldl (fun state block => Model.compress data block state) h) := by
  induction blocks generalizing h with
  | nil => simpa using hbound
  | cons block blocks ih =>
      simp only [List.foldl_cons]
      exact ih _ (Model.chainBound_compress data block h)

theorem Model.chainBound_finalState (data : ByteArray) :
    Model.ChainBound (Model.finalState data) := by
  unfold Model.finalState
  exact Model.chainBound_foldl data _ Model.initial modelInitial_bound

theorem runtimeDigestValue_final (data : ByteArray) {runtime : RuntimeChain}
    (hrep : RuntimeChainRep runtime (Model.finalState data)) :
    (runtimeDigestValue runtime).toByteArray = Model.rawOutput data := by
  rw [Model.rawOutput_eq]
  exact runtimeDigestValue_toByteArray hrep (Model.chainBound_finalState data)

end Ripemd160
