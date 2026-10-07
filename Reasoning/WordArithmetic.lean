import Reasoning.PackedStorage
import Reasoning.SolmBody
import Reasoning.Initcode

/-!
# Word arithmetic used by compiler proofs

Signed and unsigned arithmetic guards, byte masks, address conversions, and bounded offsets.
The hypotheses here are the original arithmetic bounds, independent of any contract or bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem boolWordClean_iff (word : UInt256) :
    UInt256.isZero (UInt256.isZero word) = word ↔ word = ⟨0⟩ ∨ word = ⟨1⟩ := by
  by_cases hz : word = ⟨0⟩
  · subst word
    decide
  · rw [isZero_eq_zero_of_ne hz]
    change ⟨1⟩ = word ↔ word = ⟨0⟩ ∨ word = ⟨1⟩
    simp only [hz, false_or, eq_comm]

theorem checkedMul_div_ne {a b : UInt256} (hb : UInt256.size ≤ b.toNat * a.toNat) :
    UInt256.div (UInt256.mul b a) a ≠ b := by
  have hp : 0 < a.toNat := by
    by_contra hn
    have hz : a.toNat = 0 := by omega
    rw [hz, Nat.mul_zero] at hb
    exact (by decide : ¬ UInt256.size ≤ 0) hb
  have hm : b.toNat * a.toNat % UInt256.size < b.toNat * a.toNat :=
    lt_of_lt_of_le (Nat.mod_lt _ (by decide)) hb
  have hd : b.toNat * a.toNat % UInt256.size / a.toNat < b.toNat :=
    (Nat.div_lt_iff_lt_mul hp).mpr hm
  intro he
  have hn := congrArg UInt256.toNat he
  rw [udiv_toNat, u256_mul_toNat] at hn
  omega

theorem word_add_sub_left (a b : UInt256) : UInt256.sub (a + b) a = b := by
  apply u256_inj
  change ((a.val + b.val) - a.val).val = b.val.val
  rw [add_sub_cancel_left]

theorem word_div_one (word : UInt256) : UInt256.div word ⟨1⟩ = word := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.div_one word.toNat

theorem lnot3_add_returnSize {size : Nat} (hl : 4 ≤ size) (hb : size < UInt256.size) :
    UInt256.lnot ⟨3⟩ + UInt256.ofNat size = UInt256.ofNat (size - 4) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' size hb, ulit_toNat' (size - 4) (by omega)]
  have hn : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = 2 ^ 256 - 4 := by decide
  rw [hn]
  change (2 ^ 256 - 4 + size) % (2 ^ 256) = size - 4
  change size < 2 ^ 256 at hb
  omega

theorem addressOfWord_eq (word : UInt256) :
    AccountAddress.ofUInt256 word = AccountAddress.ofNat word.toNat := by
  exact accountAddress_ofUInt256_eq_ofNat_toNat word

theorem addressOfAddress (target : AccountAddress) : EVM.address target.val = target := by
  apply Fin.ext
  change target.val % AccountAddress.size = target.val
  exact Nat.mod_eq_of_lt target.isLt

/-- The signed `int256` negative encoding: `-int256(x)` two's-complements to `0 - x`. -/
theorem wordOfInt_neg_natCast_eq_sub_zero (x : UInt256) :
    EVM.wordOfInt (-(Int.ofNat x.toNat)) = UInt256.sub ⟨0⟩ x := by
  have hlt : x.toNat < UInt256.size := x.val.isLt
  rcases Nat.eq_zero_or_pos x.toNat with h0 | hpos
  · have hx : x = ⟨0⟩ := u256_inj (by rw [h0]; rfl)
    subst hx
    decide
  · apply u256_inj
    rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := x)
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; exact hpos),
      show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    have hneg : -(Int.ofNat x.toNat) < 0 := by
      show -(x.toNat : ℤ) < 0; omega
    have hAbs : (-(Int.ofNat x.toNat)).natAbs = x.toNat := by
      show (-(x.toNat : ℤ)).natAbs = x.toNat; simp
    unfold EVM.wordOfInt
    rw [if_pos hneg, hAbs, show EVM.wordModulus = UInt256.size from rfl, Nat.mod_eq_of_lt hlt,
      if_neg (by omega : ¬ x.toNat = 0),
      show EVM.word (UInt256.size - x.toNat) = UInt256.ofNat (UInt256.size - x.toNat) from rfl,
      ulit_toNat' (UInt256.size - x.toNat) (by omega)]
    omega

/-- For grown active-words (`8 ≤ aw`, no wraparound) every byte offset `≤ 228` sits strictly below
    `aw * 32`, so `MLOAD`/`MSTORE`/`REVERT` at those offsets never triggers the out-of-range branch. -/
theorem awNotGe {aw : UInt256} (hawsz : aw.toNat * 32 < UInt256.size) (haw : 8 ≤ aw.toNat)
    (off : UInt256) (hoff : off.toNat ≤ 228) : ¬ (off ≥ aw * ⟨32⟩) := by
  intro hh
  have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := hh
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hawsz] at hle
  omega

theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  change (UInt256.ofNat a.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · exact a.isLt
  · exact lt_trans a.isLt (by decide)

theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem setAddressOffset0Word_bytecode (old dataKey : UInt256) :
    UInt256.lor (UInt256.land dataKey solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old dataKey := by
  unfold setAddressOffset0Word
  rw [u256_lor_comm (UInt256.land dataKey solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old),
    u256_land_comm (UInt256.lnot solcAddrMask) old]

theorem evm_address_ofNat_canonical (n : Nat) (_hc : n < EVM.addressModulus) :
    EVM.address (AccountAddress.ofNat n) = AccountAddress.ofNat n := by
  apply Fin.ext
  simp only [EVM.address, EVM.uintN, AccountAddress.ofNat, Fin.ofNat]
  show n % EVM.addressModulus % EVM.addressModulus = n % EVM.addressModulus
  rw [Nat.mod_mod]

theorem evm_address_ofUInt256_canonical (w : UInt256) (hc : w.toNat < EVM.addressModulus) :
    EVM.address (AccountAddress.ofUInt256 w) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact evm_address_ofNat_canonical _ hc

theorem maskedWord_address_canonical (flip : UInt256) :
    (UInt256.land flip solcAddrMask).toNat < EVM.addressModulus :=
  solcAddrMask_result_canonical flip

theorem mul_zero_left (x : UInt256) : UInt256.mul ⟨0⟩ x = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  simp

theorem mulDiv_cancel {x y : UInt256}
    (hx : x ≠ ⟨0⟩) (hmul : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) x = y := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat]
  rw [Nat.mod_eq_of_lt hmul]
  have hxNat : 0 < x.toNat := by
    by_contra hzero
    have hxzero : x.toNat = 0 := by omega
    exact hx (uint256_toNat_eq_zero hxzero)
  exact Nat.mul_div_right y.toNat hxNat

theorem mulDiv_cancel_comm {x y : UInt256}
    (hx : x ≠ ⟨0⟩) (hmul : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul y x) x = y := by
  rw [u256_mul_comm y x]
  exact mulDiv_cancel hx hmul

theorem mulDiv_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul y x) x ≠ y := by
  intro hEq
  have hxNatNe : x.toNat ≠ 0 := by
    intro hx0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hx0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 := Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) x.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega


theorem subOne_eq_addNotZero (a : UInt256) :
    UInt256.sub a ⟨1⟩ = a + UInt256.lnot ⟨0⟩ := by
  apply u256_inj
  rw [uadd_toNat,
    show (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 by decide]
  by_cases hz : a.toNat = 0
  · rw [usub_toNat_underflow (by
      rw [hz, show (⟨1⟩ : UInt256).toNat = 1 by decide]
      omega)]
    rw [hz, show (⟨1⟩ : UInt256).toNat = 1 by decide]
    norm_num [UInt256.size]
  · have hone : (⟨1⟩ : UInt256).toNat ≤ a.toNat := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
      omega
    rw [usub_toNat hone]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
    have hadd : a.toNat + (UInt256.size - 1) = UInt256.size + (a.toNat - 1) := by
      have hsize : 1 ≤ UInt256.size := by norm_num [UInt256.size]
      omega
    rw [hadd, Nat.add_mod, Nat.mod_self, zero_add]
    have hlt : a.toNat - 1 < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    simp [Nat.mod_eq_of_lt hlt]

theorem shiftLeft96_toNat_of_lt_160 (w : UInt256)
    (hw : w.toNat < 2 ^ (160 : Nat)) :
    (UInt256.shiftLeft w ⟨96⟩).toNat = w.toNat * 2 ^ (96 : Nat) := by
  have hprod : w.toNat * 2 ^ (96 : Nat) < UInt256.size := by
    change w.toNat * 2 ^ (96 : Nat) < 2 ^ (256 : Nat)
    nlinarith [hw,
      show (2 : Nat) ^ (256 : Nat) = 2 ^ (160 : Nat) * 2 ^ (96 : Nat) by
        norm_num [← Nat.pow_add]]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨96⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val]
  rw [show (⟨96⟩ : UInt256).val.val = 96 by decide]
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hprod

theorem ctorAddressHighShift (a : AccountAddress) :
    UInt256.land (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩)
        (UInt256.lnot (UInt256.sub
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)) =
      UInt256.shiftLeft (EVM.word a.val) ⟨96⟩ := by
  rw [show UInt256.lnot (UInt256.sub
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 96) by decide]
  apply u256_land_high_mask_eq_self (hk := by norm_num)
  have hlt : (EVM.word a.val).toNat < 2 ^ (160 : Nat) := by
    have hword : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide)
    rw [hword]
    exact a.isLt
  rw [shiftLeft96_toNat_of_lt_160 _ hlt]
  exact Nat.mod_eq_zero_of_dvd
    (Nat.dvd_mul_left (2 ^ 96) (EVM.word a.val).toNat)

set_option maxHeartbeats 1000000 in
theorem ctorAddressHighShiftDecode (a : AccountAddress) :
    UInt256.shiftRight (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩) ⟨96⟩ =
      EVM.word a.val := by
  apply u256_inj
  have hword : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt]
    exact lt_trans a.isLt (by decide)
  have hlt : (EVM.word a.val).toNat < 2 ^ (160 : Nat) := by
    rw [hword]
    exact a.isLt
  have hshift := shiftLeft96_toNat_of_lt_160 (EVM.word a.val) hlt
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ (⟨96⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val]
  change (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩).toNat >>> 96 =
    (EVM.word a.val).toNat
  rw [Nat.shiftRight_eq_div_pow, hshift, Nat.mul_comm]
  exact Nat.mul_div_right (EVM.word a.val).toNat (by norm_num : 0 < 2 ^ 96)

theorem ctorSetAddressWord_eq (old data : UInt256) :
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old data := by
  calc
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
        UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land old (UInt256.lnot solcAddrMask)) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
    _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
          (UInt256.land data solcAddrMask) := u256_lor_comm _ _

theorem uInt256_one_add_ofNat_of_lt {n : Nat} (hn : n + 1 < UInt256.size) :
    (⟨1⟩ : UInt256) + UInt256.ofNat n = UInt256.ofNat (n + 1) := by
  apply u256_inj
  rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by decide,
    ulit_toNat' n (by omega), ulit_toNat' (n + 1) hn]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem not_u256_ge_of_toNat_lt {a b : UInt256} (h : a.toNat < b.toNat) : ¬ a ≥ b := by
  intro hge
  have hnat : b.toNat ≤ a.toNat := hge
  omega

theorem u256_mul32_toNat_of_toNat {a : UInt256} {n : Nat}
    (ha : a.toNat = n) (h : 32 * n < UInt256.size) :
    (a * (⟨32⟩ : UInt256)).toNat = 32 * n := by
  rw [umul_toNat a (⟨32⟩ : UInt256) (by
    rw [ha, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega), ha, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  omega

theorem maskedAddress_ne_zero_of_mask_ne_zero {w : UInt256}
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval : (UInt256.land w solcAddrMask).toNat = 0 := by
    have hlt : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
      rw [u256_land_toNat]
      have hland : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat :=
        Nat.and_le_right
      have hmask : solcAddrMask.toNat < AccountAddress.size := by
        decide
      have hlandlt : Nat.land w.toNat solcAddrMask.toNat < UInt256.size := by
        have hsize : AccountAddress.size < UInt256.size := by decide
        omega
      rw [Nat.mod_eq_of_lt hlandlt]
      omega
    apply congrArg Fin.val at haddr
    simpa [AccountAddress.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt] using haddr
  exact h (u256_inj (by simpa using hval))

theorem word_of_addressOfNat_eq_mask (w : UInt256) :
    EVM.word (AccountAddress.ofNat w.toNat).val = UInt256.land w solcAddrMask := by
  apply u256_inj
  rw [u256_land_toNat]
  unfold EVM.word EVM.uintN AccountAddress.ofNat
  simp only [UInt256.toNat, Fin.ofNat]
  rw [show (↑solcAddrMask.val : Nat) = 2 ^ 160 - 1 from by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 from by decide,
    show EVM.twoPow 256 = UInt256.size from by decide]

theorem eVM_address_id (a : AccountAddress) : EVM.address a = a := by
  apply Fin.ext
  show ↑a % EVM.twoPow 160 = ↑a
  rw [Nat.mod_eq_of_lt]
  exact a.isLt

theorem uInt256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem nat_le_paddedSize (n : Nat) : n ≤ ABI.paddedSize n := by
  have hdecomp := Nat.div_add_mod (n + 31) 32
  have hmod := Nat.mod_lt (n + 31) (by norm_num : 0 < 32)
  unfold ABI.paddedSize
  omega

theorem paddedSize_le_add31 (n : Nat) : ABI.paddedSize n ≤ n + 31 := by
  unfold ABI.paddedSize
  exact Nat.mul_div_le (n + 31) 32


theorem maskedAddress_injective {a b : UInt256}
    (haddr : AccountAddress.ofNat (UInt256.land a solcAddrMask).toNat =
      AccountAddress.ofNat (UInt256.land b solcAddrMask).toNat) :
    UInt256.land a solcAddrMask = UInt256.land b solcAddrMask := by
  apply u256_inj
  have ha := solcAddrMask_result_canonical a
  have hb := solcAddrMask_result_canonical b
  have hval := congrArg Fin.val haddr
  have ha' : (UInt256.land a solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using ha
  have hb' : (UInt256.land b solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hb
  simp only [AccountAddress.ofNat, Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hval
  exact hval

theorem addressOfNat_eq_of_masked_word (w : UInt256) :
    AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat := by
  have h := solcAddressValue_masked w
  have haddr : AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat :=
    Solm.Value.address.inj h
  simpa [u256_land_comm] using haddr

theorem word_of_addressOfNat_eq_mask' (who : UInt256) :
    EVM.word (AccountAddress.ofNat who.toNat).val =
      UInt256.land who solcAddrMask := by
  apply u256_inj
  rw [u256_land_toNat]
  unfold EVM.word EVM.uintN AccountAddress.ofNat
  simp only [UInt256.toNat, Fin.ofNat]
  rw [show (↑solcAddrMask.val : Nat) = 2 ^ 160 - 1 from by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 from by decide,
    show EVM.twoPow 256 = UInt256.size from by decide]

theorem addressOfWordOfNat (a : EVM.Address) :
    AccountAddress.ofNat (EVM.Word.ofNat (↑a : Nat)).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat (EVM.Word.ofNat (↑a : Nat))]
  simpa [EVM.Word.ofNat] using AccountAddress.ofUInt256_ofNat a

theorem addressMask_land_complement_eq_zero (w : UInt256) :
    UInt256.land (UInt256.land w (UInt256.lnot solcAddrMask)) solcAddrMask = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat, addressOffset0High160Mask_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mul_comm]
  rw [Nat.mul_mod_right]
  rfl

theorem u256_32_toNat : (⟨32⟩ : UInt256).toNat = 32 := by u256_toNat

theorem u256_64_toNat : (⟨64⟩ : UInt256).toNat = 64 := by u256_toNat

theorem u256_add_lnot_zero_eq_sub_one (Z : UInt256) :
    Z + UInt256.lnot ⟨0⟩ = UInt256.sub Z ⟨1⟩ := by
  apply u256_inj
  have hlnot : (UInt256.lnot ⟨0⟩).toNat = 2 ^ 256 - 1 := by
    unfold UInt256.lnot
    decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hZ : Z.toNat < UInt256.size := Z.val.isLt
  rw [show UInt256.size = 2 ^ 256 from by decide] at hZ
  rcases Nat.eq_zero_or_pos Z.toNat with hz | hz
  · rw [uadd_toNat, hlnot, usub_toNat_underflow (by rw [hz, h1]; omega), hz, h1,
      show UInt256.size = 2 ^ 256 from by decide]
    omega
  · rw [uadd_toNat, hlnot, usub_toNat (by rw [h1]; omega), h1,
      show UInt256.size = 2 ^ 256 from by decide]
    omega

theorem u256_pred_lt_of_ne_zero (len : UInt256) (hlen : len ≠ ⟨0⟩) :
    UInt256.lt (len + UInt256.lnot ⟨0⟩) len = ⟨1⟩ := by
  rw [u256_add_lnot_zero_eq_sub_one]
  apply ult_one
  have hpos : 0 < len.toNat := by
    by_contra hnot
    have hzeroNat : len.toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  rw [usub_toNat]
  · rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    omega
  · rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    exact Nat.succ_le_of_lt hpos


theorem u256_add_lnot_zero_eq_pred_of_pos (len : UInt256) (hpos : 0 < len.toNat) :
    len + UInt256.lnot ⟨0⟩ = UInt256.ofNat (len.toNat - 1) := by
  apply u256_inj
  rw [uadd_toNat]
  have hlnot : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    decide
  have hmod :
      (len.toNat + (UInt256.size - 1)) % UInt256.size = len.toNat - 1 := by
    have hsizePos : 0 < UInt256.size := by decide
    have hsum : len.toNat + (UInt256.size - 1) =
        UInt256.size + (len.toNat - 1) := by
      omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by
      have hlt : len.toNat < UInt256.size := len.val.isLt
      omega)
  rw [hlnot, hmod]
  exact (ulit_toNat' (len.toNat - 1) (by
    have hlt : len.toNat < UInt256.size := len.val.isLt
    omega)).symm

theorem u256_sub_one_eq_pred_of_pos (w : UInt256) (hpos : 0 < w.toNat) :
    UInt256.sub w ⟨1⟩ = UInt256.ofNat (w.toNat - 1) := by
  apply u256_inj
  rw [usub_toNat (by simpa using Nat.succ_le_of_lt hpos)]
  rw [ulit_toNat' (w.toNat - 1) (by
    have hlt : w.toNat < UInt256.size := w.val.isLt
    omega)]
  rfl


/-- Symbolic `¬ off ≥ aw·32` from `off < aw.toNat·32` (no `aw·32` overflow). -/
theorem wordMul32_not_ge_of_lt {off aw : UInt256} (hlt : off.toNat < aw.toNat * 32)
    (hNoWrap : aw.toNat * 32 < UInt256.size) : ¬ off ≥ aw * ⟨32⟩ := by
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hge
  have h : off.toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hge
  rw [hmul] at h; omega

theorem ctorMin32_toNat_of_lt {n : ℕ} (h : n < 32) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg, ulit_toNat' n hnsize]
  · show ¬ (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hnsize]
    omega

theorem ctorMin32_toNat_of_ge {n : ℕ}
    (h32 : 32 ≤ n) (hsize : n < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = 32
  rw [if_pos]
  · rfl
  · show (32 : ℕ) ≤ (UInt256.ofNat n).toNat
    rw [ulit_toNat' n hsize]
    exact h32

theorem addressOfNat_toNat_masked (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land w solcAddrMask).toNat := by
  have hmaskAddr :
      AccountAddress.ofNat w.toNat = AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change w.val.val % AccountAddress.size =
      Nat.land w.val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hcanon : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus] using solcAddrMask_result_canonical w
  rw [hmaskAddr]
  unfold AccountAddress.ofNat
  change (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
    (UInt256.land w solcAddrMask).toNat
  exact Nat.mod_eq_of_lt hcanon

theorem addressOfNat_eq_iff_solcAddrMask_eq (a b : UInt256) :
    AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔
      UInt256.land solcAddrMask a = UInt256.land solcAddrMask b := by
  constructor
  · intro haddr
    have h := congrArg (fun addr : AccountAddress => keyValueToWord (.address addr)) haddr
    simpa [keyValueToWord_address_ofNat_mask] using h
  · intro hmask
    apply Fin.ext
    change (AccountAddress.ofNat a.toNat).toNat = (AccountAddress.ofNat b.toNat).toNat
    have ha := addressOfNat_toNat_masked a
    have hb := addressOfNat_toNat_masked b
    rw [ha, hb]
    have hmask' : UInt256.land a solcAddrMask = UInt256.land b solcAddrMask := by
      simpa [u256_land_comm solcAddrMask a, u256_land_comm solcAddrMask b] using hmask
    rw [hmask']

theorem address_eq_target (word : UInt256) :
    AccountAddress.ofNat word.toNat = AccountAddress.ofUInt256 word := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem mulGuard_of_fit {x y : UInt256}
    (hy : y ≠ ⟨0⟩) (hfit : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  have hyNatNe : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simpa [Nat.mul_comm] using
    Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)

theorem mulOverflow_of_guard_fail {x y : UInt256}
    (hy : y ≠ ⟨0⟩)
    (hguard : UInt256.div (UInt256.mul x y) y ≠ x) :
    UInt256.size ≤ x.toNat * y.toNat := by
  by_contra hnot
  exact hguard (mulGuard_of_fit hy (Nat.lt_of_not_ge hnot))

theorem mulFit_of_guard {x y : UInt256}
    (hguard : UInt256.div (UInt256.mul x y) y = x) :
    x.toNat * y.toNat < UInt256.size := by
  by_contra hnot
  exact (u256_mul_div_right_overflow_ne x y (Nat.le_of_not_gt hnot)) hguard


theorem wordOfInt_sub_toUInt256 (x y : UInt256) :
    EVM.wordOfInt ((x.toNat : Int) - (y.toNat : Int)) = UInt256.sub x y := by
  by_cases hle : y.toNat ≤ x.toNat
  · have hnonneg : 0 ≤ (x.toNat : Int) - (y.toNat : Int) := by omega
    rw [wordOfInt_nonneg _ hnonneg]
    apply u256_inj
    have htoNat : ((x.toNat : Int) - (y.toNat : Int)).toNat = x.toNat - y.toNat := by
      omega
    rw [usub_toNat (a := x) (b := y) hle]
    simp [EVM.word, EVM.uintN, htoNat]
    exact Nat.mod_eq_of_lt (by exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.val.isLt)
  · have hlt : x.toNat < y.toNat := Nat.lt_of_not_ge hle
    rw [EVM.wordOfInt]
    have hwordMod : EVM.wordModulus = UInt256.size := by decide
    have hneg : (x.toNat : Int) - (y.toNat : Int) < 0 := by omega
    rw [if_pos hneg]
    have hnatAbs :
        Int.natAbs ((x.toNat : Int) - (y.toNat : Int)) = y.toNat - x.toNat := by
      omega
    have hdiffMod :
        (y.toNat - x.toNat) % EVM.wordModulus = y.toNat - x.toNat := by
      apply Nat.mod_eq_of_lt
      rw [hwordMod]
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega
    have hdiffNe : y.toNat - x.toNat ≠ 0 := by omega
    rw [hnatAbs, hdiffMod, if_neg hdiffNe]
    apply u256_inj
    rw [usub_toNat_underflow (a := x) (b := y) hlt]
    have hword :
        EVM.wordModulus - (y.toNat - x.toNat) =
          UInt256.size + x.toNat - y.toNat := by
      rw [hwordMod]
      omega
    simp [EVM.word, EVM.uintN, hword, show EVM.twoPow 256 = UInt256.size from by decide]
    exact Nat.mod_eq_of_lt (by
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega)

theorem word_of_addressOfUInt256_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    EVM.word ↑(AccountAddress.ofUInt256 w) = w := by
  have hcanonVal : ↑w.val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  apply u256_inj
  simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
  rw [show AccountAddress.size = EVM.addressModulus from by decide]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt (by exact w.val.isLt)]

theorem addressWord_val_canonical (addr : AccountAddress) :
    (EVM.word addr.val).toNat < EVM.addressModulus := by
  change (UInt256.ofNat addr.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · exact addr.isLt
  · exact lt_of_lt_of_le addr.isLt (by decide)

theorem addressWord_val_clean (addr : AccountAddress) :
    UInt256.land (EVM.word addr.val) solcAddrMask = EVM.word addr.val :=
  solcAddrMask_clean (addressWord_val_canonical addr)

set_option maxHeartbeats 1000000 in
theorem addressWord_shiftLeft96_shiftRight96 (addr : AccountAddress) :
    UInt256.shiftRight (UInt256.shiftLeft (EVM.word addr.val) ⟨96⟩) ⟨96⟩ =
      EVM.word addr.val := by
  apply u256_inj
  have haddr : (EVM.word addr.val).toNat = addr.val := by
    change (UInt256.ofNat addr.val).toNat = addr.val
    rw [UInt256.toNat_ofNat_of_lt]
    exact lt_of_lt_of_le addr.isLt (by decide)
  have hlt160 : (EVM.word addr.val).toNat < 2 ^ (160 : Nat) := by
    rw [haddr]
    exact addr.isLt
  have hshift := shiftLeft96_toNat_of_lt_160 (EVM.word addr.val) hlt160
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ ((⟨96⟩ : UInt256).val ≥ 256))]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val]
  change (UInt256.shiftLeft (EVM.word addr.val) ⟨96⟩).toNat >>> (96 : Nat) =
    (EVM.word addr.val).toNat
  rw [Nat.shiftRight_eq_div_pow, hshift]
  rw [Nat.mul_comm]
  exact Nat.mul_div_right (EVM.word addr.val).toNat (by norm_num : 0 < 2 ^ 96)

theorem addressWord_shiftLeft96_high_mask (addr : AccountAddress) :
    UInt256.land (UInt256.shiftLeft (EVM.word addr.val) ⟨96⟩)
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)) =
      UInt256.shiftLeft (EVM.word addr.val) ⟨96⟩ := by
  rw [show UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 96) by decide]
  apply u256_land_high_mask_eq_self (hk := by norm_num)
  have hlt160 : (EVM.word addr.val).toNat < 2 ^ (160 : Nat) := by
    have haddr : (EVM.word addr.val).toNat = addr.val := by
      change (UInt256.ofNat addr.val).toNat = addr.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_of_lt_of_le addr.isLt (by decide)
    rw [haddr]
    exact addr.isLt
  rw [shiftLeft96_toNat_of_lt_160 (EVM.word addr.val) hlt160]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left (2 ^ 96) (EVM.word addr.val).toNat)

theorem u256_div_one (w : UInt256) :
    UInt256.div w ⟨1⟩ = w := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.div_one w.toNat

theorem solcAddrMask_idem_right (w : UInt256) :
    UInt256.land (UInt256.land w solcAddrMask) solcAddrMask =
      UInt256.land w solcAddrMask := by
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

theorem solcAddrMask_idem_left (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land w solcAddrMask) =
      UInt256.land w solcAddrMask := by
  exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)

theorem solcAddrMask_idem_left_left (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land solcAddrMask w := by
  rw [u256_land_comm solcAddrMask w]
  rw [solcAddrMask_idem_left w]

theorem address_of_addressOfUInt256 (w : UInt256) :
    EVM.address (AccountAddress.ofUInt256 w) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  show ↑(AccountAddress.ofUInt256 w) % EVM.twoPow 160 = ↑(AccountAddress.ofUInt256 w)
  rw [Nat.mod_eq_of_lt]
  exact (AccountAddress.ofUInt256 w).isLt

theorem wordOfInt_toNat_of_neg_of_abs_lt (i : Int) (hneg : i < 0)
    (hle : i.natAbs < EVM.wordModulus) :
    (EVM.wordOfInt i).toNat = UInt256.size - i.natAbs := by
  have hdiffPos : i.natAbs ≠ 0 := by
    intro h
    have : i = 0 := by omega
    omega
  have hpos : 0 < i.natAbs := Nat.pos_of_ne_zero hdiffPos
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [Nat.mod_eq_of_lt hle, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - i.natAbs)).toNat = UInt256.size - i.natAbs
  rw [ulit_toNat']
  · rw [show EVM.wordModulus = UInt256.size by decide]
  · rw [show EVM.wordModulus = UInt256.size by decide]
    exact Nat.sub_lt (by decide : 0 < UInt256.size) hpos

theorem wordOfInt_neg_natCast_eq_sub_zero_of_le_sign (w : UInt256) (hle : w.toNat ≤ 2 ^ 255) :
    EVM.wordOfInt (-(Int.ofNat w.toNat)) = UInt256.sub ⟨0⟩ w := by
  by_cases hz0 : w.toNat = 0
  · have hw : w = ⟨0⟩ := by
      apply u256_inj
      exact hz0
    subst hw
    rw [u256_sub_self]
    rfl
  · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hz0
    apply u256_inj
    rw [wordOfInt_toNat_of_neg_of_abs_lt]
    · rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos]
      have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by simp
      rw [habs]
      norm_num
    · have hcastPos : (0 : Int) < Int.ofNat w.toNat := by
        simpa using (Int.ofNat_lt.mpr hpos)
      exact neg_neg_of_pos hcastPos
    · have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by simp
      rw [habs]
      exact lt_of_le_of_lt hle (by decide : 2 ^ 255 < EVM.wordModulus)

theorem u256_zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := by
  decide

theorem uint256_mul_zero (x : UInt256) :
    x * (⟨0⟩ : UInt256) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_op_toNat]
  rfl

theorem uint256_zero_mul (x : UInt256) :
    (⟨0⟩ : UInt256) * x = ⟨0⟩ := by
  rw [show (⟨0⟩ : UInt256) * x = x * (⟨0⟩ : UInt256) by
    exact u256_mul_comm (⟨0⟩ : UInt256) x]
  exact uint256_mul_zero x

theorem uint256_div_zero_num (x : UInt256) :
    UInt256.div (⟨0⟩ : UInt256) x = ⟨0⟩ := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.zero_div x.toNat

theorem uInt256One_toNat : (⟨1⟩ : UInt256).toNat = 1 := by
  decide

theorem uInt256Two_toNat : (⟨2⟩ : UInt256).toNat = 2 := by
  decide

theorem uInt256Two_ne_zero : (⟨2⟩ : UInt256) ≠ ⟨0⟩ := by
  decide

theorem uInt256DivZeroTwo :
    UInt256.div (⟨0⟩ : UInt256) (⟨2⟩ : UInt256) = ⟨0⟩ := by
  decide

theorem uInt256DivOneTwo :
    UInt256.div (⟨1⟩ : UInt256) (⟨2⟩ : UInt256) = ⟨0⟩ := by
  decide

theorem rpow_div_two_toNat_le_pred {n : UInt256} {v : ℕ}
    (hnz : n ≠ ⟨0⟩) (hle : n.toNat ≤ v + 1) :
    (UInt256.div n ⟨2⟩).toNat ≤ v := by
  have hnNatNe : n.toNat ≠ 0 := by
    intro hzero
    exact hnz (uint256_toNat_eq_zero hzero)
  have hnPos : 0 < n.toNat := Nat.pos_of_ne_zero hnNatNe
  have hlt : (UInt256.div n ⟨2⟩).toNat < n.toNat := by
    rw [udiv_toNat, uInt256Two_toNat]
    exact Nat.div_lt_self hnPos (by decide : 1 < 2)
  omega

theorem rpowShiftRight128_toNat (x : UInt256) :
    (UInt256.shiftRight x (⟨128⟩ : UInt256)).toNat = x.toNat / 2 ^ 128 := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg]
  · change (x.val >>> (⟨128⟩ : UInt256).val).val = x.val.val / 2 ^ 128
    rw [Fin.shiftRight_val]
    rw [Nat.shiftRight_eq_div_pow]
    norm_num [UInt256.size]
  · decide

theorem rpowShiftRight128_zero_of_square_fit (x : UInt256)
    (hfit : x.toNat * x.toNat < UInt256.size) :
    UInt256.shiftRight x (⟨128⟩ : UInt256) = ⟨0⟩ := by
  have hxlt : x.toNat < 2 ^ 128 := by
    by_contra hnot
    have hxge : 2 ^ 128 ≤ x.toNat := Nat.le_of_not_lt hnot
    have hsize : UInt256.size = 2 ^ 256 := by decide
    have hsqge : 2 ^ 256 ≤ x.toNat * x.toNat := by
      nlinarith [hxge]
    omega
  apply u256_inj
  change (UInt256.shiftRight x (⟨128⟩ : UInt256)).toNat = (⟨0⟩ : UInt256).toNat
  rw [rpowShiftRight128_toNat]
  change x.toNat / 2 ^ 128 = 0
  exact Nat.div_eq_of_lt hxlt

theorem rpowShiftRight128_ne_zero_of_square_overflow (x : UInt256)
    (hover : UInt256.size ≤ x.toNat * x.toNat) :
    UInt256.shiftRight x (⟨128⟩ : UInt256) ≠ ⟨0⟩ := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  rw [rpowShiftRight128_toNat] at hnat
  change x.toNat / 2 ^ 128 = 0 at hnat
  have hxlt : x.toNat < 2 ^ 128 :=
    Nat.lt_of_div_eq_zero (by norm_num : 0 < 2 ^ 128) hnat
  have hsize : UInt256.size = 2 ^ 256 := by decide
  have hsq : x.toNat * x.toNat < UInt256.size := by
    rw [hsize]
    nlinarith [hxlt]
  omega

theorem uInt256_land_one_eq_zero_of_even {n : UInt256} (heven : n.toNat % 2 = 0) :
    UInt256.land n ⟨1⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, heven]
  decide

theorem uInt256_land_one_eq_one_of_odd {n : UInt256} (hodd : n.toNat % 2 ≠ 0) :
    UInt256.land n ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256One_toNat]
  have hlt : n.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem u256_add_overflow_lt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.lt (a + b) a = ⟨1⟩ := by
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  exact ult_one (by
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega)

theorem u256_land_zero_left (a : UInt256) :
    UInt256.land (⟨0⟩ : UInt256) a = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  change Nat.land 0 a.toNat % UInt256.size = 0
  have hzero : Nat.land 0 a.toNat = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (0 &&& a.toNat).testBit i = (0 : Nat).testBit i
    rw [Nat.testBit_and]
    simp
  simpa [hzero]

theorem u256_land_zero_right (a : UInt256) :
    UInt256.land a (⟨0⟩ : UInt256) = ⟨0⟩ := by
  rw [u256_land_comm]
  exact u256_land_zero_left a

theorem uint48Mask_add_no_wrap_toNat (a b : UInt256)
    (hfit : (UInt256.land a uint48Mask).toNat + b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) uint48Mask).toNat =
      (UInt256.land a uint48Mask).toNat + b.toNat := by
  rw [u256_land_toNat]
  change Nat.land (a + b).toNat (2 ^ 48 - 1) % UInt256.size = _
  rw [nat_land_mask_eq_mod]
  rw [uadd_toNat]
  have h48pos : 0 < 2 ^ 48 := by norm_num
  have h48ltSize : 2 ^ 48 < UInt256.size := by norm_num [UInt256.size]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    change 2 ^ 48 ∣ 2 ^ 256
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_eq_mod_mod_of_dvd hdvd]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)]
  have ha : (UInt256.land a uint48Mask).toNat = a.toNat % 2 ^ 48 := by
    rw [u256_land_toNat]
    change Nat.land a.toNat (2 ^ 48 - 1) % UInt256.size = a.toNat % 2 ^ 48
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)
  rw [ha] at hfit ⊢
  rw [Nat.add_mod]
  have hbmod : b.toNat % 2 ^ 48 = b.toNat := by
    have hb : b.toNat < 2 ^ 48 := by omega
    exact Nat.mod_eq_of_lt hb
  rw [hbmod]
  rw [Nat.mod_eq_of_lt hfit]
  exact Nat.mod_eq_of_lt (lt_trans hfit h48ltSize)

theorem uint48Mask_add_toNat_mod (a b : UInt256) (hb : b.toNat < 2 ^ 48) :
    (UInt256.land (a + b) uint48Mask).toNat =
      ((UInt256.land a uint48Mask).toNat + b.toNat) % 2 ^ 48 := by
  rw [u256_land_toNat]
  change Nat.land (a + b).toNat (2 ^ 48 - 1) % UInt256.size = _
  rw [nat_land_mask_eq_mod]
  rw [uadd_toNat]
  have h48pos : 0 < 2 ^ 48 := by norm_num
  have h48ltSize : 2 ^ 48 < UInt256.size := by norm_num [UInt256.size]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    change 2 ^ 48 ∣ 2 ^ 256
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_eq_mod_mod_of_dvd hdvd]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)]
  have ha : (UInt256.land a uint48Mask).toNat = a.toNat % 2 ^ 48 := by
    rw [u256_land_toNat]
    change Nat.land a.toNat (2 ^ 48 - 1) % UInt256.size = a.toNat % 2 ^ 48
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)
  rw [ha]
  rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ h48pos) h48ltSize)

theorem uint48AddGuard_false_of_no_wrap (a b : UInt256)
    (hfit : (UInt256.land a uint48Mask).toNat + b.toNat < 2 ^ 48) :
    UInt256.lt (UInt256.land (a + b) uint48Mask)
        (UInt256.land a uint48Mask) = ⟨0⟩ := by
  have hsum := uint48Mask_add_no_wrap_toNat a b hfit
  apply ult_zero
  rw [hsum]
  exact Nat.le_add_right _ _

theorem uint48AddGuard_true_of_wrap (a b : UInt256)
    (hb : b.toNat < 2 ^ 48)
    (hover : 2 ^ 48 ≤ (UInt256.land a uint48Mask).toNat + b.toNat) :
    UInt256.lt (UInt256.land (a + b) uint48Mask)
        (UInt256.land a uint48Mask) = ⟨1⟩ := by
  apply ult_one
  rw [uint48Mask_add_toNat_mod a b hb]
  have hx : (UInt256.land a uint48Mask).toNat < 2 ^ 48 := by
    simpa [EVM.twoPow] using uint48Masked_lt a
  have hsumLt : (UInt256.land a uint48Mask).toNat + b.toNat < 2 ^ 49 := by
    omega
  rw [Nat.mod_eq_sub_mod hover]
  have hsubLt : (UInt256.land a uint48Mask).toNat + b.toNat - 2 ^ 48 < 2 ^ 48 := by
    omega
  rw [Nat.mod_eq_of_lt hsubLt]
  omega

theorem addressWord_eq_ofNat_address {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    EVM.word (AccountAddress.ofNat w.toNat).val = w := by
  have haddrVal : (AccountAddress.ofNat w.toNat).val = w.toNat := by
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  change UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w
  rw [haddrVal]
  exact u256_ofNat_toNat _

theorem addressWord_address_eq_target {w : UInt256} :
    EVM.address (AccountAddress.ofNat w.toNat) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simpa [EVM.twoPow, AccountAddress.size] using
        (AccountAddress.ofNat w.toNat).isLt)

theorem addressOfNat_ne_zero_of_word_ne_zero {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hne : w ≠ ⟨0⟩) :
    AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval := congrArg Fin.val haddr
  have hmod : w.toNat % AccountAddress.size = w.toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  have hzeroNat : w.toNat = 0 := by
    simpa [AccountAddress.ofNat, Fin.ofNat, hmod] using hval
  exact hne (uint256_toNat_eq_zero hzeroNat)

theorem natLandClearMiddle160_208 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1) =
      n % 2 ^ 160 + (n / 2 ^ 208) * 2 ^ 208 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1)).testBit i =
    (n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208).testBit i
  have hmask :
      (2 : Nat) ^ 256 - 2 ^ 208 + 2 ^ 160 - 1 =
        Nat.lor (2 ^ 160 - 1) ((2 ^ 48 - 1) <<< 208) := by
    rw [Nat.shiftLeft_eq]
    rw [nat_lor_shift_add (2 ^ 160 - 1) (2 ^ 48 - 1) 208]
    · norm_num [Nat.pow_add]
    · norm_num
  have hrhs :
      n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208 =
        Nat.lor (n % 2 ^ 160) ((n / 2 ^ 208) * 2 ^ 208) := by
    rw [nat_lor_shift_add (n % 2 ^ 160) (n / 2 ^ 208) 208]
    · exact (Nat.mod_lt _ (by positivity : 0 < 2 ^ 160)).trans_le (by norm_num)
  rw [hmask, hrhs]
  rw [Nat.testBit_and]
  change (n.testBit i && (((2 ^ 160 - 1) ||| ((2 ^ 48 - 1) <<< 208)).testBit i)) =
    (((n % 2 ^ 160) ||| (n / 2 ^ 208 * 2 ^ 208)).testBit i)
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 208) * 2 ^ 208 = (n / 2 ^ 208) <<< 208 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi160 : i < 160
  · have hi208 : i < 208 := by omega
    simp [hi160, hi208]
  · have hnot160 : ¬ i < 160 := hi160
    by_cases hi208 : i < 208
    · simp [hnot160, hi208]
    · have h208le : 208 ≤ i := Nat.le_of_not_gt hi208
      by_cases hi256 : i < 256
      · have hlt48 : i - 208 < 48 := by omega
        have hmaskBit :
            Nat.testBit 281474976710655 (i - 208) = true := by
          change Nat.testBit (2 ^ 48 - 1) (i - 208) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlt48]
        simp [hnot160, hi208, hmaskBit]
        exact (divPow_testBit n 208 i h208le).symm
      · have hnot48 : ¬ i - 208 < 48 := by omega
        have hmaskBit :
            Nat.testBit 281474976710655 (i - 208) = false := by
          change Nat.testBit (2 ^ 48 - 1) (i - 208) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot48]
        simp [hnot160, hi208, hmaskBit]
        have hq : n / 2 ^ 208 < 2 ^ 48 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by
            rw [← Nat.pow_add]]
          exact hn
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem natLandClearMiddle48_96 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1) =
      n % 2 ^ 48 + (n / 2 ^ 96) * 2 ^ 96 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1)).testBit i =
    (n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96).testBit i
  have hmask :
      (2 : Nat) ^ 256 - 2 ^ 96 + 2 ^ 48 - 1 =
        Nat.lor (2 ^ 48 - 1) ((2 ^ 160 - 1) <<< 96) := by
    rw [Nat.shiftLeft_eq]
    rw [nat_lor_shift_add (2 ^ 48 - 1) (2 ^ 160 - 1) 96]
    · norm_num [Nat.pow_add]
    · norm_num
  have hrhs :
      n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96 =
        Nat.lor (n % 2 ^ 48) ((n / 2 ^ 96) * 2 ^ 96) := by
    rw [nat_lor_shift_add (n % 2 ^ 48) (n / 2 ^ 96) 96]
    · exact (Nat.mod_lt _ (by positivity : 0 < 2 ^ 48)).trans_le (by norm_num)
  rw [hmask, hrhs]
  rw [Nat.testBit_and]
  change (n.testBit i && (((2 ^ 48 - 1) ||| ((2 ^ 160 - 1) <<< 96)).testBit i)) =
    (((n % 2 ^ 48) ||| (n / 2 ^ 96 * 2 ^ 96)).testBit i)
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (n / 2 ^ 96) * 2 ^ 96 = (n / 2 ^ 96) <<< 96 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi48 : i < 48
  · have hi96 : i < 96 := by omega
    simp [hi48, hi96]
  · have hnot48 : ¬ i < 48 := hi48
    by_cases hi96 : i < 96
    · simp [hnot48, hi96]
    · have h96le : 96 ≤ i := Nat.le_of_not_gt hi96
      by_cases hi256 : i < 256
      · have hlt160 : i - 96 < 160 := by omega
        have hmaskBit :
            Nat.testBit 1461501637330902918203684832716283019655932542975
              (i - 96) = true := by
          change Nat.testBit (2 ^ 160 - 1) (i - 96) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlt160]
        simp [hnot48, hi96, hmaskBit]
        exact (divPow_testBit n 96 i h96le).symm
      · have hnot160 : ¬ i - 96 < 160 := by omega
        have hmaskBit :
            Nat.testBit 1461501637330902918203684832716283019655932542975
              (i - 96) = false := by
          change Nat.testBit (2 ^ 160 - 1) (i - 96) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot160]
        simp [hnot48, hi96, hmaskBit]
        have hq : n / 2 ^ 96 < 2 ^ 160 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by
            rw [← Nat.pow_add]]
          exact hn
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem setAddressOffset0Word_zero (old : UInt256) :
    setAddressOffset0Word old ⟨0⟩ =
      UInt256.land old (UInt256.lnot solcAddrMask) := by
  rw [setAddressOffset0Word]
  rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ by decide]
  exact u256_lor_zero _

theorem ctorSetAddressOffset0Word_low_address (old : UInt256) (a : AccountAddress) :
    UInt256.land solcAddrMask (setAddressOffset0Word old (EVM.word a.val)) = EVM.word a.val := by
  apply u256_inj
  rw [u256_land_toNat, setAddressOffset0Word_toNat]
  · rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_comm]
    rw [nat_land_mask_eq_mod]
    have ha : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size)
    rw [ha]
    have hmod : (a.val + old.toNat / 2 ^ 160 * 2 ^ 160) % 2 ^ 160 = a.val := by
      rw [Nat.mul_comm (old.toNat / 2 ^ 160) (2 ^ 160)]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size, EVM.addressModulus,
        EVM.twoPow] using a.isLt)
    rw [hmod]
    exact Nat.mod_eq_of_lt (lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size))
  · have ha : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size)
    rw [ha]
    exact a.isLt

theorem ult_eq_zero_to_le {a b : UInt256}
    (h : UInt256.lt a b = ⟨0⟩) : b.toNat ≤ a.toNat := by
  by_contra hnot
  have hone : UInt256.lt a b = ⟨1⟩ := ult_one (by omega)
  have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
    rw [← hone, h]
  exact False.elim ((by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)

/-- SafeMath mul division-check succeeds when the product fits and `a ≠ 0`. -/
theorem mulOkEqOne {a b : UInt256} (ha : a ≠ (⟨0⟩ : UInt256))
    (hfit : b.toNat * a.toNat < UInt256.size) :
    UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨1⟩ := by
  have haNe : a.toNat ≠ 0 := fun hz => ha (uint256_toNat_eq_zero hz)
  have hdiv : UInt256.div (UInt256.mul b a) a = b := by
    apply u256_inj
    rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
    simpa [Nat.mul_comm] using Nat.mul_div_right b.toNat (Nat.pos_of_ne_zero haNe)
  rw [hdiv, u256_eq_refl]

/-- SafeMath mul division-check fails on overflow (`size ≤ b*a`, `a ≠ 0`). -/
theorem mulOverflowEqZero {a b : UInt256} (ha : a ≠ (⟨0⟩ : UInt256))
    (hover : UInt256.size ≤ b.toNat * a.toNat) :
    UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨0⟩ := by
  apply u256_eq_of_ne
  intro hbad
  have hmod : (UInt256.mul b a).toNat = b.toNat * a.toNat % UInt256.size := u256_mul_toNat b a
  have hsizePos : 0 < UInt256.size := by decide
  have hlt : (UInt256.mul b a).toNat < b.toNat * a.toNat := by
    rw [hmod]; exact lt_of_lt_of_le (Nat.mod_lt _ hsizePos) hover
  have hdiv : (UInt256.mul b a).toNat / a.toNat = b.toNat := by
    have hh := congrArg UInt256.toNat hbad
    rwa [udiv_toNat] at hh
  have hge : b.toNat * a.toNat ≤ (UInt256.mul b a).toNat := by
    calc b.toNat * a.toNat = ((UInt256.mul b a).toNat / a.toNat) * a.toNat := by rw [hdiv]
      _ ≤ (UInt256.mul b a).toNat := Nat.div_mul_le_self _ _
  omega

theorem u256_eq_ne_zero_to_eq {a b : UInt256}
    (h : UInt256.eq a b ≠ ⟨0⟩) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have hzero : UInt256.eq a b = ⟨0⟩ := u256_eq_of_ne hab
    exact False.elim (h hzero)

theorem u256_mul_zero_right (w : UInt256) : UInt256.mul w ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  simp

theorem u256_mul_zero_left (w : UInt256) : UInt256.mul ⟨0⟩ w = ⟨0⟩ := by
  rw [u256_mul_comm]
  exact u256_mul_zero_right w

theorem u256_div_zero_left (w : UInt256) : (⟨0⟩ : UInt256) / w = ⟨0⟩ := by
  apply u256_inj
  change (UInt256.div (⟨0⟩ : UInt256) w).toNat = (⟨0⟩ : UInt256).toNat
  rw [udiv_toNat]
  simp

theorem u256_sdiv_zero_left (w : UInt256) : UInt256.sdiv ⟨0⟩ w = ⟨0⟩ := by
  unfold UInt256.sdiv
  by_cases hw : EVM.twoPow 255 ≤ w.toNat
  · simp [u256_div_zero_left]
  · simp [u256_div_zero_left]

theorem u256_sdiv_high_low
    {prod rate : UInt256}
    (hprodHigh : EVM.twoPow 255 ≤ prod.toNat)
    (hrateLow : rate.toNat < EVM.twoPow 255) :
    UInt256.sdiv prod rate =
      { val := (UInt256.div (UInt256.abs prod) rate).val * (-1 : Fin UInt256.size) } := by
  unfold UInt256.sdiv
  rw [if_pos (by simpa [EVM.twoPow] using hprodHigh)]
  rw [if_neg (by simpa [EVM.twoPow] using not_le.mpr hrateLow)]
  rfl

theorem u256_div_toNat_eq_of_toNat {a b z : UInt256} {denom : Nat}
    (ha : a.toNat = denom * z.toNat)
    (hb : b.toNat = denom)
    (hdenomPos : 0 < denom) :
    (UInt256.div a b).toNat = z.toNat := by
  rw [udiv_toNat, ha, hb]
  exact Nat.mul_div_right z.toNat hdenomPos

theorem int_neg_mul_bound_to_nat {a r : Nat}
    (h : -((2 : Int) ^ 255) ≤ Int.ofNat a * -Int.ofNat r) :
    r * a ≤ EVM.twoPow 255 := by
  have h' := h
  ring_nf at h'
  have hcastArt : ((a * r : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    change Int.ofNat a * Int.ofNat r ≤ (2 : Int) ^ 255
    omega
  have hcast : ((r * a : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    rw [Nat.mul_comm]
    exact hcastArt
  change r * a ≤ 2 ^ 255
  apply Int.ofNat_le.mp
  have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by norm_num
  rw [hpow]
  exact hcast

theorem u256_size_eq_two_sign :
    UInt256.size = EVM.twoPow 255 + EVM.twoPow 255 := by
  decide

theorem fin_uint256_neg_one_val :
    ((-1 : Fin UInt256.size).val) = UInt256.size - 1 := by
  rw [Fin.val_neg]
  rw [if_neg]
  · rfl
  · intro hbad
    have hval := congrArg Fin.val hbad
    have hone : ((1 : Fin UInt256.size).val) = 1 := by
      show (Fin.ofNat UInt256.size 1).val = 1
      rw [Fin.ofNat]
      exact Nat.mod_eq_of_lt (by decide)
    rw [hone] at hval
    norm_num at hval

theorem nat_mul_pred_mod {a M : Nat} (ha0 : 0 < a) (haM : a < M) :
    a * (M - 1) % M = M - a := by
  have hmod : a * (M - 1) = (a - 1) * M + (M - a) := by
    apply Nat.cast_injective (R := Int)
    have h1 : ((a - 1 : Nat) : Int) = (a : Int) - 1 := by omega
    have h2 : ((M - 1 : Nat) : Int) = (M : Int) - 1 := by omega
    have h3 : ((M - a : Nat) : Int) = (M : Int) - (a : Int) := by omega
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, h1, h2, h3]
    ring
  rw [hmod, Nat.add_mod, Nat.mul_mod_left]
  simp [Nat.mod_eq_of_lt (by omega : M - a < M)]

theorem fin_uint256_mul_neg_one_val {w : UInt256} (hpos : 0 < w.toNat) :
    (w.val * (-1 : Fin UInt256.size)).val = UInt256.size - w.toNat := by
  rw [Fin.val_mul, fin_uint256_neg_one_val]
  exact nat_mul_pred_mod hpos w.val.isLt

theorem fin_uint256_mul_neg_one_high {w : UInt256}
    (hpos : 0 < w.toNat) (hle : w.toNat ≤ EVM.twoPow 255) :
    EVM.twoPow 255 ≤ (w.val * (-1 : Fin UInt256.size)).val := by
  rw [fin_uint256_mul_neg_one_val (w := w) hpos]
  rw [u256_size_eq_two_sign]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left hle (EVM.twoPow 255))

theorem fin_uint256_mul_neg_one_val_low_contra {q art : UInt256}
    (hqLe : q.toNat ≤ EVM.twoPow 255)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hnegVal : (q.val * (-1 : Fin UInt256.size)).val = art.toNat) : False := by
  by_cases hqZero : q = ⟨0⟩
  · have hartZero : art.toNat = 0 := by
      rw [← hnegVal]
      rw [hqZero]
      rfl
    exact hartNe (uint256_toNat_eq_zero hartZero)
  · have hqPos : 0 < q.toNat := by
      have hqNatNe : q.toNat ≠ 0 := by
        intro hz
        exact hqZero (uint256_toNat_eq_zero hz)
      exact Nat.pos_of_ne_zero hqNatNe
    have hartHigh : EVM.twoPow 255 ≤ art.toNat := by
      rw [← hnegVal]
      exact fin_uint256_mul_neg_one_high hqPos hqLe
    omega

theorem u256_abs_high_toNat {w : UInt256}
    (hhi : 2 ^ 255 ≤ w.toNat) (hpos : 0 < w.toNat) :
    (UInt256.abs w).toNat = UInt256.size - w.toNat := by
  cases w with
  | mk val =>
      change (UInt256.abs { val := val }).toNat = UInt256.size - val.val
      unfold UInt256.abs
      simp only [UInt256.toNat] at hhi hpos ⊢
      rw [if_pos hhi]
      change (val * (-1 : Fin UInt256.size)).val = UInt256.size - val.val
      exact fin_uint256_mul_neg_one_val (w := { val := val }) hpos

theorem slt_zero_eq_zero_to_nonneg (w : UInt256)
    (h : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    0 ≤
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · simp [hlow]
  · have hhi : 2 ^ 255 ≤ w.toNat := by
      simpa [EVM.twoPow] using le_of_not_gt hlow
    have hone : UInt256.slt w (UInt256.ofNat 0) = ⟨1⟩ :=
      slt_lit_one_high (a := w) (m := 0) (by norm_num) hhi
    have hzero : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ := by
      simpa using h
    have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
      rw [← hone, hzero]
    exact False.elim ((by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)

theorem uintWordLeMaxInt256_of_slt_zero {w : UInt256}
    (hmax : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    Int.ofNat w.toNat ≤ maxInt256 := by
  have hnonneg := slt_zero_eq_zero_to_nonneg w hmax
  unfold maxInt256
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hlt : (w.toNat : Int) < (2 : Int) ^ 255 := by
      exact_mod_cast (by simpa [EVM.twoPow] using hlow)
    change (w.toNat : Int) ≤ (2 : Int) ^ 255 - 1
    omega
  · have hltInt : (w.toNat : Int) < (EVM.wordModulus : Int) := by
      exact_mod_cast w.val.isLt
    have hbad : ¬ 0 ≤
        (if w.toNat < EVM.twoPow 255 then Int.ofNat w.toNat
         else Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
      simp [hlow]; omega
    exact False.elim (hbad hnonneg)

theorem u256_toNat_lt_sign_of_slt_zero {w : UInt256}
    (hslt : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    w.toNat < EVM.twoPow 255 := by
  have hle := uintWordLeMaxInt256_of_slt_zero hslt
  have hltInt : (w.toNat : Int) < (2 : Int) ^ 255 := by
    have hmaxLt : maxInt256 < (2 : Int) ^ 255 := by
      unfold maxInt256
      omega
    exact lt_of_le_of_lt hle hmaxLt
  change w.toNat < 2 ^ 255
  exact Int.ofNat_lt.mp (by
    have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by norm_num
    rw [hpow]
    exact hltInt)

theorem u256_slt_zero_ne_zero_of_high {w : UInt256}
    (hhi : EVM.twoPow 255 ≤ w.toNat) : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩ := by
  have hcond : w.val.val ≥ 2 ^ 255 := by
    simpa [EVM.twoPow, UInt256.toNat] using hhi
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  simp only [UInt256.toNat]
  rw [if_pos hcond]
  rw [if_neg (by decide : ¬ ((0 : Fin UInt256.size).val ≥ 2 ^ 255))]
  decide

theorem u256_abs_div_eq_bound_to_sign {rate prod art : UInt256} {rabs : Nat}
    (hrabs : (UInt256.abs rate).toNat = rabs)
    (hprodHigh : EVM.twoPow 255 ≤ prod.toNat)
    (hprodPos : 0 < prod.toNat)
    (hdiv : UInt256.div (UInt256.abs prod) (UInt256.abs rate) = art) :
    rabs * art.toNat ≤ EVM.twoPow 255 := by
  have hAbsProdToNat : (UInt256.abs prod).toNat = UInt256.size - prod.toNat :=
    u256_abs_high_toNat hprodHigh hprodPos
  have hdivNat : (UInt256.abs prod).toNat / (UInt256.abs rate).toNat = art.toNat := by
    have h := congrArg UInt256.toNat hdiv
    simpa [udiv_toNat] using h
  have hleDiv : art.toNat ≤ (UInt256.abs prod).toNat / (UInt256.abs rate).toNat := by
    rw [hdivNat]
  have hpLeAbs : rabs * art.toNat ≤ (UInt256.abs prod).toNat := by
    have hle := Nat.mul_le_of_le_div (UInt256.abs rate).toNat art.toNat
      (UInt256.abs prod).toNat hleDiv
    rw [hrabs] at hle
    simpa [Nat.mul_comm] using hle
  have hAbsLe : (UInt256.abs prod).toNat ≤ EVM.twoPow 255 := by
    rw [hAbsProdToNat, u256_size_eq_two_sign]
    omega
  exact le_trans hpLeAbs hAbsLe

theorem int_eq_signed_word_of_range_mod {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat) :
    i =
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  have hsignLtM : (2 : Int) ^ 255 < Int.ofNat EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow]
  by_cases hnonneg : 0 ≤ i
  · have hiM : i < Int.ofNat EVM.wordModulus := lt_trans hhi hsignLtM
    have hi : i = Int.ofNat w.toNat := by
      rw [Int.emod_eq_of_lt hnonneg hiM] at hmod
      exact hmod
    rw [hi]
    have hlow : w.toNat < EVM.twoPow 255 := by
      apply Int.ofNat_lt.mp
      have hpow : ((EVM.twoPow 255 : Nat) : Int) = (2 : Int) ^ 255 := by
        norm_num [EVM.twoPow]
      rw [hpow]
      simpa [hi] using hhi
    rw [if_pos hlow]
  · have hneg : i < 0 := not_le.mp hnonneg
    have hshiftNonneg : 0 ≤ i + Int.ofNat EVM.wordModulus := by
      have hloM : -Int.ofNat EVM.wordModulus < i := by
        have h : -Int.ofNat EVM.wordModulus < -((2 : Int) ^ 255) := by
          norm_num [EVM.wordModulus, EVM.twoPow]
        exact lt_of_lt_of_le h hlo
      omega
    have hshiftLt : i + Int.ofNat EVM.wordModulus < Int.ofNat EVM.wordModulus := by
      omega
    have hmodShift :
        i % Int.ofNat EVM.wordModulus = i + Int.ofNat EVM.wordModulus := by
      rw [Int.emod_eq_add_self_emod]
      exact Int.emod_eq_of_lt hshiftNonneg hshiftLt
    have hwi : Int.ofNat w.toNat = i + Int.ofNat EVM.wordModulus := by
      rw [hmodShift] at hmod
      exact hmod.symm
    have hhigh : ¬ w.toNat < EVM.twoPow 255 := by
      intro hlow
      have hwlt : Int.ofNat w.toNat < (2 : Int) ^ 255 := by
        exact_mod_cast (by simpa [EVM.twoPow] using hlow)
      have hwge : (2 : Int) ^ 255 ≤ Int.ofNat w.toNat := by
        rw [hwi]
        have hM :
            Int.ofNat EVM.wordModulus = (2 : Int) ^ 255 + (2 : Int) ^ 255 := by
          norm_num [EVM.wordModulus, EVM.twoPow]
        rw [hM]
        omega
      omega
    rw [if_neg hhigh]
    omega

theorem int_nonneg_of_word_slt_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hslt : UInt256.slt w ⟨0⟩ = ⟨0⟩) : 0 ≤ i := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact slt_zero_eq_zero_to_nonneg w hslt

theorem sgt_zero_eq_zero_to_nonpos (w : UInt256)
    (h : UInt256.sgt w ⟨0⟩ = ⟨0⟩) :
    (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) ≤ 0 := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · by_cases hzero : w.toNat = 0
    · have hpow : 0 < EVM.twoPow 255 := by norm_num [EVM.twoPow]
      simp [hzero, hpow]
    · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hzero
      have hone : UInt256.sgt w (UInt256.ofNat 0) = ⟨1⟩ :=
        sgt_lit_one (a := w) (m := 0) (by norm_num) (by simpa using hpos)
          (by simpa [EVM.twoPow] using hlow)
      have hzero' : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
        simpa using h
      have hbad : (⟨1⟩ : UInt256) = ⟨0⟩ := by
        rw [← hone, hzero']
      exact False.elim ((by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hbad)
  · simp [hlow]
    have hleNat : w.toNat ≤ EVM.wordModulus := Nat.le_of_lt w.val.isLt
    have hleInt : (w.toNat : Int) ≤ (EVM.wordModulus : Int) := by
      exact_mod_cast hleNat
    omega

theorem int_nonpos_of_word_sgt_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hsgt : UInt256.sgt w ⟨0⟩ = ⟨0⟩) : i ≤ 0 := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact sgt_zero_eq_zero_to_nonpos w hsgt

theorem slt_zero_ne_zero_to_neg (w : UInt256)
    (h : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) :
    (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) < 0 := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hslt0 : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ :=
      slt_lit_zero (a := w) (m := 0) (by norm_num) (by omega)
        (by simpa [EVM.twoPow] using hlow)
    exact False.elim (h (by simpa using hslt0))
  · simp [hlow]
    have hltNat : w.toNat < EVM.wordModulus := w.val.isLt
    have hltInt : (w.toNat : Int) < (EVM.wordModulus : Int) := by
      exact_mod_cast hltNat
    omega

theorem int_neg_of_word_slt_ne_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hslt : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) : i < 0 := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact slt_zero_ne_zero_to_neg w hslt

theorem sgt_zero_ne_zero_to_pos (w : UInt256)
    (h : UInt256.sgt w ⟨0⟩ ≠ ⟨0⟩) :
    0 <
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · by_cases hzero : w.toNat = 0
    · have hsgt0 : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
        have hw : w = UInt256.ofNat 0 := by
          apply u256_inj
          simpa using hzero
        subst w
        decide
      exact False.elim (h (by simpa using hsgt0))
    · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hzero
      simp [hlow]
      exact_mod_cast hpos
  · have hsgt0 : UInt256.sgt w (UInt256.ofNat 0) = ⟨0⟩ := by
      unfold UInt256.sgt UInt256.sgtBool UInt256.fromBool Bool.toUInt256
      have hhi : w.toNat ≥ 2 ^ 255 := by
        simpa [EVM.twoPow] using le_of_not_gt hlow
      have hzeroLow : ¬ (UInt256.ofNat 0).toNat ≥ 2 ^ 255 := by
        decide
      rw [if_pos hhi, if_neg hzeroLow]
      rfl
    exact False.elim (h (by simpa using hsgt0))

theorem int_pos_of_word_sgt_ne_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hsgt : UInt256.sgt w ⟨0⟩ ≠ ⟨0⟩) : 0 < i := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact sgt_zero_ne_zero_to_pos w hsgt

theorem ugt_eq_zero_to_le {a b : UInt256} (h : UInt256.gt a b = ⟨0⟩) :
    a.toNat ≤ b.toNat := by
  by_contra hle
  have hgt : b.toNat < a.toNat := Nat.lt_of_not_ge hle
  have hone : UInt256.gt a b = ⟨1⟩ := ugt_one hgt
  rw [hone] at h
  contradiction

theorem signedAddGuardNegCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hneg :
      UInt256.slt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt new old = ⟨0⟩) :
    0 ≤ i ∨ new.toNat ≤ old.toNat := by
  cases hneg with
  | inl hslt => exact Or.inl (int_nonneg_of_word_slt_zero hlo hhi hmod hslt)
  | inr hgt => exact Or.inr (ugt_eq_zero_to_le hgt)

theorem signedAddGuardPosCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hpos :
      UInt256.sgt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt new old = ⟨0⟩) :
    i ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases hpos with
  | inl hsgt => exact Or.inl (int_nonpos_of_word_sgt_zero hlo hhi hmod hsgt)
  | inr hlt => exact Or.inr (ult_eq_zero_to_le hlt)

theorem ugt_ne_zero_to_gt {a b : UInt256}
    (h : UInt256.gt a b ≠ ⟨0⟩) : b.toNat < a.toNat := by
  by_contra hnot
  exact h (ugt_zero (by omega))

theorem signedAddGuardNegFalseCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hnegFail :
      ¬ (UInt256.slt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt new old = ⟨0⟩)) :
    i < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact int_neg_of_word_slt_ne_zero hlo hhi hmod (by
      intro hslt
      exact hnegFail (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact hnegFail (Or.inr hgt))

theorem signedAddGuardPosFalseCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hposFail :
      ¬ (UInt256.sgt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt new old = ⟨0⟩)) :
    0 < i ∧ new.toNat < old.toNat := by
  constructor
  · exact int_pos_of_word_sgt_ne_zero hlo hhi hmod (by
      intro hsgt
      exact hposFail (Or.inl hsgt))
  · exact ult_ne_zero_toNat_lt (by
      intro hlt
      exact hposFail (Or.inr hlt))

theorem uintCheckedMulFail_to_overflow {a b : UInt256}
    (hfail :
      ¬ (b = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩)) :
    UInt256.size ≤ a.toNat * b.toNat := by
  by_contra hnot
  have hfit : a.toNat * b.toNat < UInt256.size := by omega
  by_cases hbzeroNat : b.toNat = 0
  · exact hfail (Or.inl (uint256_toNat_eq_zero hbzeroNat))
  · have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hbzeroNat
    let prod := UInt256.mul a b
    have hprodNat : prod.toNat = a.toNat * b.toNat := by
      dsimp [prod]
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
    have hdivNat : (UInt256.div prod b).toNat = a.toNat := by
      rw [udiv_toNat, hprodNat]
      simpa [Nat.mul_comm] using Nat.mul_div_right a.toNat hbpos
    have hdivWord : UInt256.div prod b = a := by
      rw [← u256_ofNat_toNat (UInt256.div prod b), hdivNat, u256_ofNat_toNat]
    have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩ := by
      rw [show UInt256.div (UInt256.mul a b) b = a by simpa [prod] using hdivWord]
      rw [uInt256_eq_self]
      exact one_ne_zero_uint
    exact hfail (Or.inr heq)

theorem uintCheckedMulGuard_to_fit_and_source_guard {a b : UInt256}
    (hguard :
      b = ⟨0⟩ ∨
        UInt256.eq (UInt256.div (UInt256.mul a b) b) a ≠ ⟨0⟩) :
    a.toNat * b.toNat < UInt256.size ∧
      (b.toNat = 0 ∨ (UInt256.mul a b).toNat / b.toNat = a.toNat) := by
  let prod := UInt256.mul a b
  by_cases hbzeroNat : b.toNat = 0
  · constructor
    · rw [hbzeroNat, Nat.mul_zero]
      decide
    · exact Or.inl hbzeroNat
  · have hbzeroWord : b ≠ ⟨0⟩ := by
      intro hzero
      exact hbzeroNat (by rw [hzero]; rfl)
    have hdivWord : UInt256.div prod b = a := by
      cases hguard with
      | inl hzero => exact False.elim (hbzeroWord hzero)
      | inr heq =>
          exact u256_eq_ne_zero_to_eq (by simpa [prod] using heq)
    have hdivNat : prod.toNat / b.toNat = a.toNat := by
      have h := congrArg UInt256.toNat hdivWord
      simpa [prod, udiv_toNat] using h
    have hleDiv : a.toNat ≤ prod.toNat / b.toNat := by
      rw [hdivNat]
    have hprodLe : a.toNat * b.toNat ≤ prod.toNat := by
      have hle := Nat.mul_le_of_le_div b.toNat a.toNat prod.toNat hleDiv
      simpa [Nat.mul_comm] using hle
    constructor
    · exact lt_of_le_of_lt hprodLe prod.val.isLt
    · exact Or.inr hdivNat

theorem u256_land_left_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  intro ha
  apply h
  rw [ha]
  exact u256_land_zero_left b

theorem u256_land_right_ne_zero_of_land_ne_zero {a b : UInt256}
    (h : UInt256.land a b ≠ ⟨0⟩) :
    b ≠ ⟨0⟩ := by
  intro hb
  apply h
  rw [hb]
  exact u256_land_zero_right a

theorem u256_isZero_ne_zero_to_eq_zero {a : UInt256}
    (h : UInt256.isZero a ≠ ⟨0⟩) :
    a = ⟨0⟩ := by
  by_contra hne
  have hz : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne hne
  exact h hz

theorem u256_lor_left_ne_zero_of_lor_ne_zero_right_zero {a b : UInt256}
    (h : UInt256.lor a b ≠ ⟨0⟩) (hb : b = ⟨0⟩) :
    a ≠ ⟨0⟩ := by
  rw [hb, u256_lor_zero] at h
  exact h

theorem u256_lor_one_left_ne_zero (w : UInt256) :
    UInt256.lor (⟨1⟩ : UInt256) w ≠ ⟨0⟩ := by
  intro h
  have hbit := congrArg (fun x : UInt256 => x.toNat % 2) h
  simp [UInt256.lor, Fin.lor, UInt256.size] at hbit
  change (Nat.lor 1 w.toNat % UInt256.size) % 2 = 0 at hbit
  rw [Nat.mod_mod_of_dvd _ (by norm_num [UInt256.size] : 2 ∣ UInt256.size)] at hbit
  have hlorOdd : Nat.lor 1 w.toNat % 2 = 1 := by
    have htest : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
      change Nat.testBit (1 ||| w.toNat) 0 = true
      rw [Nat.testBit_or]
      simp
    simpa [Nat.testBit_zero] using htest
  omega


theorem signedAddGuardNegCond_of_not {i : Int} {old new : Nat}
    (h : ¬ (0 ≤ i ∨ new ≤ old)) :
    i < 0 ∧ old < new := by
  omega

theorem signedAddGuardPosCond_of_not {i : Int} {old new : Nat}
    (h : ¬ (i ≤ 0 ∨ old ≤ new)) :
    0 < i ∧ new < old := by
  omega

theorem nat_lor_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.lor a b < 2 ^ k := by
  refine Nat.lt_of_testBit k ?_ ?_ ?_
  · change (a ||| b).testBit k = false
    rw [Nat.testBit_lor]
    rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
    rfl
  · simp
  · intro j hj
    change (a ||| b).testBit j = (2 ^ k).testBit j
    rw [Nat.testBit_lor]
    have ha' : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (le_of_lt hj))
    have hb' : b < 2 ^ j := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (le_of_lt hj))
    rw [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']
    symm
    exact Nat.testBit_two_pow_of_ne (show k ≠ j by omega)

theorem u256_lor_eq_zero_left {a b : UInt256}
    (h : UInt256.lor a b = ⟨0⟩) :
    a = ⟨0⟩ := by
  have hlorLt :
      Nat.lor a.toNat b.toNat < UInt256.size := by
    simpa [UInt256.size] using
      nat_lor_lt_two_pow
        (a := a.toNat) (b := b.toNat) (k := 256)
        (by change a.val.val < UInt256.size; exact a.val.isLt)
        (by change b.val.val < UInt256.size; exact b.val.isLt)
  have hlorZero : Nat.lor a.toNat b.toNat = 0 := by
    have hnat := congrArg UInt256.toNat h
    change (Nat.lor a.toNat b.toNat % UInt256.size) = 0 at hnat
    rwa [Nat.mod_eq_of_lt hlorLt] at hnat
  apply u256_inj
  have hbit : ∀ i, Nat.testBit a.toNat i = false := by
    intro i
    have hcongr : Nat.testBit (Nat.lor a.toNat b.toNat) i = false := by
      rw [hlorZero]
      simp
    change (a.toNat ||| b.toNat).testBit i = false at hcongr
    rw [Nat.testBit_lor] at hcongr
    cases ha : Nat.testBit a.toNat i
    · rfl
    · cases hb : Nat.testBit b.toNat i <;> simp [ha, hb] at hcongr
  have haNat : a.toNat = 0 := Nat.zero_of_testBit_eq_false hbit
  simpa [haNat]

theorem u256_lor_eq_zero_right {a b : UInt256}
    (h : UInt256.lor a b = ⟨0⟩) :
    b = ⟨0⟩ := by
  have hcomm : UInt256.lor b a = ⟨0⟩ := by
    rw [u256_lor_comm]
    exact h
  exact u256_lor_eq_zero_left hcomm


theorem signedSubGuardNegCond_of_word {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    dtab ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (int_nonpos_of_word_sgt_zero hlo hhi hmod hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem signedSubGuardPosCond_of_word {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ dtab ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (int_nonneg_of_word_slt_zero hlo hhi hmod hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem signedSubGuardNegFailCond_of_word {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < dtab ∧ old.toNat < new.toNat := by
  constructor
  · exact int_pos_of_word_sgt_ne_zero hlo hhi hmod (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem signedSubGuardPosFailCond_of_word {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    dtab < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact int_neg_of_word_slt_ne_zero hlo hhi hmod (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_toNat_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem u256_add_one_ne_self (x : UInt256) : x + ⟨1⟩ ≠ x := by
  intro h
  have ht := congrArg UInt256.toNat h
  rw [uadd_toNat] at ht
  have hsumLe : x.toNat + 1 ≤ UInt256.size := by
    have hxlt : x.toNat < UInt256.size := x.val.isLt
    omega
  by_cases hlt : x.toNat + 1 < UInt256.size
  · have hmod : (x.toNat + (⟨1⟩ : UInt256).toNat) % UInt256.size = x.toNat + 1 := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
      exact Nat.mod_eq_of_lt hlt
    rw [hmod] at ht
    omega
  · have hsum : x.toNat + 1 = UInt256.size := by omega
    have hmod : (x.toNat + (⟨1⟩ : UInt256).toNat) % UInt256.size = 0 := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide, hsum]
      exact Nat.mod_self UInt256.size
    rw [hmod] at ht
    have hsize : 1 < UInt256.size := by decide
    omega

theorem signedSubWrap (old sub : UInt256) (subInt : Int)
    (hsub : subInt % (Int.ofNat EVM.wordModulus) = Int.ofNat sub.toNat) :
    (Int.ofNat old.toNat - subInt) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (UInt256.sub old sub).toNat := by
  have holdLt : old.toNat < EVM.wordModulus := by
    change old.val.val < EVM.twoPow 256
    exact old.val.isLt
  have hold :
      (Int.ofNat old.toNat) % (Int.ofNat EVM.wordModulus) = Int.ofNat old.toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr holdLt)
  rw [Int.sub_emod, hold, hsub]
  by_cases hle : sub.toNat ≤ old.toNat
  · have hdiff : (UInt256.sub old sub).toNat = old.toNat - sub.toNat :=
      usub_toNat hle
    have hsubInt :
        (Int.ofNat old.toNat - Int.ofNat sub.toNat) =
          Int.ofNat (old.toNat - sub.toNat) := by
      exact (Int.ofNat_sub hle).symm
    have hlt : (old.toNat - sub.toNat) < EVM.wordModulus := by
      omega
    rw [hsubInt]
    calc
      Int.ofNat (old.toNat - sub.toNat) % Int.ofNat EVM.wordModulus =
          Int.ofNat (old.toNat - sub.toNat) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt)
      _ = Int.ofNat (UInt256.sub old sub).toNat := by rw [hdiff]
  · have hlt : old.toNat < sub.toNat := Nat.lt_of_not_ge hle
    have hdiff : (UInt256.sub old sub).toNat = UInt256.size + old.toNat - sub.toNat :=
      usub_toNat_underflow hlt
    have hwordMod : EVM.wordModulus = UInt256.size := by rfl
    have hpos : 0 < sub.toNat - old.toNat := by omega
    have hdiffLt : sub.toNat - old.toNat < EVM.wordModulus := by
      have hsubLt : sub.toNat < EVM.wordModulus := by
        change sub.val.val < EVM.twoPow 256
        exact sub.val.isLt
      omega
    have hneg :
        (Int.ofNat old.toNat - Int.ofNat sub.toNat) =
          -Int.ofNat (sub.toNat - old.toNat) := by
      have hsubOld :
          Int.ofNat sub.toNat - Int.ofNat old.toNat =
            Int.ofNat (sub.toNat - old.toNat) := by
        exact (Int.ofNat_sub (Nat.le_of_lt hlt)).symm
      calc
        Int.ofNat old.toNat - Int.ofNat sub.toNat =
            -(Int.ofNat sub.toNat - Int.ofNat old.toNat) := by omega
        _ = -Int.ofNat (sub.toNat - old.toNat) := by rw [hsubOld]
    rw [hneg]
    have hshift :
        (-Int.ofNat (sub.toNat - old.toNat)) % Int.ofNat EVM.wordModulus =
          Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) := by
      have hMpos : 0 < (Int.ofNat EVM.wordModulus) := by
        change (0 : Int) < (2 : Int) ^ 256
        norm_num
      have hdpos : 0 < (Int.ofNat (sub.toNat - old.toNat)) :=
        Int.natCast_pos.mpr hpos
      have hdlt : (Int.ofNat (sub.toNat - old.toNat)) < Int.ofNat EVM.wordModulus :=
        Int.ofNat_lt.mpr hdiffLt
      rw [Int.emod_eq_add_self_emod]
      rw [show -Int.ofNat (sub.toNat - old.toNat) + Int.ofNat EVM.wordModulus =
          Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) by omega]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hshift, hdiff]
    have hdle : sub.toNat - old.toNat ≤ EVM.wordModulus := by omega
    have hnat :
        EVM.wordModulus - (sub.toNat - old.toNat) =
          UInt256.size + old.toNat - sub.toNat := by
      rw [hwordMod]
      omega
    calc
      Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) =
          Int.ofNat (EVM.wordModulus - (sub.toNat - old.toNat)) := by
        exact (Int.ofNat_sub hdle).symm
      _ = Int.ofNat (UInt256.size + old.toNat - sub.toNat) := by rw [hnat]

theorem signedAddWrap (old wad : UInt256) (wadInt : Int)
    (hwad : wadInt % (Int.ofNat EVM.wordModulus) = Int.ofNat wad.toNat) :
    (Int.ofNat old.toNat + wadInt) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (wad + old).toNat := by
  have holdLt : old.toNat < EVM.wordModulus := by
    change old.val.val < EVM.twoPow 256
    exact old.val.isLt
  have hold :
      (Int.ofNat old.toNat) % (Int.ofNat EVM.wordModulus) = Int.ofNat old.toNat :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _) (Int.ofNat_lt.mpr holdLt)
  have hsumNat : (old.toNat + wad.toNat) % EVM.wordModulus = (wad + old).toNat := by
    rw [show EVM.wordModulus = UInt256.size by rfl]
    rw [uadd_toNat, Nat.add_comm]
  rw [Int.add_emod, hold, hwad]
  change ((↑(old.toNat + wad.toNat) : Int) % Int.ofNat EVM.wordModulus) =
    Int.ofNat (wad + old).toNat
  exact (Int.natCast_emod (old.toNat + wad.toNat) EVM.wordModulus).symm.trans
    (congrArg Int.ofNat hsumNat)

theorem accountAddress_of_word_val_tail (a : AccountAddress) :
    AccountAddress.ofUInt256 (EVM.word a.val) = a := by
  exact accountAddress_roundtrip a


theorem u256_add_zero (K : UInt256) : K + ⟨0⟩ = K := by
  apply u256_inj
  rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.mod_eq_of_lt K.val.isLt

theorem clearCursor_toNat (K : UInt256) (oldWords i : Nat)
    (hK : K.toNat + oldWords < UInt256.size) (hi : i ≤ oldWords) :
    (K + UInt256.ofNat i).toNat = K.toNat + i := by
  rw [uadd_toNat, ulit_toNat' i (by omega), Nat.mod_eq_of_lt (by omega)]

theorem uadd_assoc (a b c : UInt256) : a + b + c = a + (b + c) := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, uadd_toNat, uadd_toNat, Nat.mod_add_mod, Nat.add_mod_mod,
    Nat.add_assoc]

theorem clearCursor_succ (K : UInt256) (a : Nat) :
    (⟨1⟩ : UInt256) + (K + UInt256.ofNat a) = K + UInt256.ofNat (a + 1) := by
  rw [← u256_one_add_ofNat, ← uadd_assoc, ← uadd_assoc, u256_add_comm (⟨1⟩ : UInt256) K]


theorem land255_double (x : UInt256) :
    UInt256.land (UInt256.land ⟨255⟩ x) ⟨255⟩ = UInt256.land x ⟨255⟩ := by
  apply u256_inj
  have h255 : (⟨255⟩ : UInt256).toNat = 255 := by decide
  rw [uland_toNat, uland_toNat, uland_toNat, h255]
  rw [Nat.and_comm 255 x.toNat, Nat.and_assoc, Nat.and_self]

/-- `~0 + Z = Z - 1` (the long-flag mask arithmetic equals a `sub … 1`). -/
theorem lnot_zero_add (Z : UInt256) : UInt256.lnot ⟨0⟩ + Z = UInt256.sub Z ⟨1⟩ := by
  apply u256_inj
  have hlnot : (UInt256.lnot ⟨0⟩).toNat = 2 ^ 256 - 1 := by unfold UInt256.lnot; decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hZ : Z.toNat < UInt256.size := Z.val.isLt
  rw [show UInt256.size = 2 ^ 256 from by decide] at hZ
  rcases Nat.eq_zero_or_pos Z.toNat with hz | hz
  · rw [uadd_toNat, hlnot, usub_toNat_underflow (by rw [hz, h1]; omega), hz, h1,
      show UInt256.size = 2 ^ 256 from by decide]; omega
  · rw [uadd_toNat, hlnot, usub_toNat (by rw [h1]; omega), h1,
      show UInt256.size = 2 ^ 256 from by decide]; omega


theorem paddedSize_of_pos_le32 (r : ℕ) (h1 : 0 < r) (h2 : r ≤ 32) : ABI.paddedSize r = 32 := by
  unfold ABI.paddedSize; rw [show (r + 31) / 32 = 1 from by omega]

theorem uadd_zero_r (a : UInt256) : a + ⟨0⟩ = a := by
  apply u256_inj
  rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem ofNat_toNat_mod (k : ℕ) : (UInt256.ofNat k).toNat = k % UInt256.size := rfl

theorem uadd_ofNat_succ (b : UInt256) (k : ℕ) :
    (⟨1⟩ : UInt256) + (b + UInt256.ofNat k) = b + UInt256.ofNat (k + 1) := by
  apply u256_inj
  simp only [uadd_toNat, ofNat_toNat_mod, show (⟨1⟩ : UInt256).toNat = 1 from rfl,
    Nat.add_mod_mod]
  congr 1
  omega

theorem longFuel_continue_nat {n i : Nat} (hn : 0 < n) (hi : i < (n - 1) / 32) :
    32 * i + 32 < n := by
  have hiSucc : i + 1 ≤ (n - 1) / 32 := Nat.succ_le_of_lt hi
  have hmul : 32 * (i + 1) ≤ 32 * ((n - 1) / 32) := Nat.mul_le_mul_left 32 hiSucc
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  omega

theorem longFuel_done_nat {n : Nat} (hn : 0 < n) : n ≤ 32 * ((n - 1) / 32) + 32 := by
  have hdecomp : n - 1 = (n - 1) / 32 * 32 + (n - 1) % 32 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (n - 1) 32).symm
  have hmod : (n - 1) % 32 < 32 := Nat.mod_lt _ (by decide)
  omega

theorem longFuel_bound {n : Nat} (hn : n < 2 ^ 255) :
    160 + 32 * ((n - 1) / 32) + 32 < UInt256.size := by
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  have hsize : (2 : Nat) ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
  omega

/-- Mask literal helper: `src ∧ ((1<<160)-1) = src` for a canonical (address-sized) `src`. -/
theorem addressMaskLiteral_clean_of_canonical {src : UInt256}
    (hsrc : src.toNat < EVM.addressModulus) :
    UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = src := by
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
  exact solcAddrMask_clean hsrc

theorem u256_lnot_zero_toNat : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
  unfold UInt256.lnot; decide

/-- `wordOfInt (a − b) = a ⊖ b` (the wrapping `-=` truncation on store, valid when `b ≤ a`). -/
theorem wordOfInt_sub_words {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  have hcast : (Int.ofNat a.toNat - Int.ofNat b.toNat) = Int.ofNat (a.toNat - b.toNat) :=
    (Int.ofNat_sub h).symm
  rw [hcast, wordOfInt_ofNat_toNat_gen]
  apply u256_inj
  rw [usub_toNat h]
  exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt)

/-- Wrapping `sub` on store, valid even on underflow (solc 0.5 `unchecked`). -/
theorem wordOfInt_sub_natCasts (a b : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  by_cases h : b.toNat ≤ a.toNat
  · exact wordOfInt_sub_words h
  · have h' : a.toNat < b.toNat := Nat.lt_of_not_le h
    have hsub : Int.ofNat (b.toNat - a.toNat) = Int.ofNat b.toNat - Int.ofNat a.toNat :=
      Int.ofNat_sub (le_of_lt h')
    have hcast : (Int.ofNat a.toNat - Int.ofNat b.toNat) = -(Int.ofNat (b.toNat - a.toNat)) := by
      rw [hsub]; ring
    have hd : b.toNat - a.toNat ≠ 0 := Nat.sub_ne_zero_of_lt h'
    have hb : b.toNat < UInt256.size := b.val.isLt
    have hwm : EVM.wordModulus = UInt256.size := rfl
    have hlt' : b.toNat - a.toNat < EVM.wordModulus := by rw [hwm]; omega
    have hneg : Int.ofNat a.toNat - Int.ofNat b.toNat < 0 := by
      have hlt : Int.ofNat a.toNat < Int.ofNat b.toNat := Int.ofNat_lt.mpr h'
      linarith
    apply u256_inj
    rw [usub_toNat_underflow h', EVM.wordOfInt, if_pos hneg, hcast]
    simp only [Int.natAbs_neg, Int.natAbs_ofNat', Nat.mod_eq_of_lt hlt', if_neg hd]
    show (EVM.uintN 256 (EVM.wordModulus - (b.toNat - a.toNat))).val
      = UInt256.size + a.toNat - b.toNat
    show (EVM.wordModulus - (b.toNat - a.toNat)) % EVM.twoPow 256
      = UInt256.size + a.toNat - b.toNat
    rw [hwm, show EVM.twoPow 256 = UInt256.size from rfl, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `wordOfInt (a - b) = a ⊖ b` when `b ≤ a` (the unchecked `-=` on store; `require(bal≥wad)` rules
    out underflow). -/
theorem wordOfInt_sub_words_of_le (a b : UInt256) (hle : b.toNat ≤ a.toNat) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  rw [show (Int.ofNat a.toNat - Int.ofNat b.toNat) = Int.ofNat (a.toNat - b.toNat) from
      (Nat.cast_sub hle).symm, wordOfInt_ofNat_toNat_gen]
  apply u256_inj
  rw [usub_toNat hle]
  exact ulit_toNat' _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt)

theorem high168Mask_toNat (old : UInt256) :
    (UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 168)) old).toNat =
      (old.toNat / 2 ^ 168) * 2 ^ 168 :=
  u256_land_high_mask_toNat old 168 (by norm_num)

/-- The `2^64 - 1` literal built by `PUSH1 1; PUSH1 1; PUSH1 0x40; SHL; SUB`. -/
theorem u64mask_toNat :
    (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩).toNat = 2 ^ 64 - 1 := by decide

/-- The length bound check `iszero(gt(n, 2^64-1))` is taken when the array length `n < 2^64`. -/
theorem decoderValidLen (n : ℕ) (hn : n < 2 ^ 64) :
    (UInt256.isZero (UInt256.gt (UInt256.ofNat n)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩))) ≠ ⟨0⟩ := by
  rw [ugt_zero (by rw [u64mask_toNat, ulit_toNat' _ (lt_of_lt_of_le hn (by decide))]; omega)]
  decide

/-- The decoded array head `0x80 + 0x20 = 0xa0`. -/
theorem arrayHead_eq : (⟨128⟩ + UInt256.ofNat 32 : UInt256) = UInt256.ofNat 160 := by
  apply u256_inj
  rw [uadd_toNat, show ((⟨128⟩ : UInt256)).toNat = 128 from by decide,
    ulit_toNat' _ (by decide : (32:ℕ) < UInt256.size),
    ulit_toNat' _ (by decide : (160:ℕ) < UInt256.size)]
  decide

theorem arrayHead_toNat : (⟨128⟩ + UInt256.ofNat 32 : UInt256).toNat = 160 := by
  rw [arrayHead_eq]; exact ulit_toNat' _ (by decide)

theorem u256_lor_one_ne_zero' (w : UInt256) :
    UInt256.lor ⟨1⟩ w ≠ ⟨0⟩ := by
  intro h
  have hval : (UInt256.lor ⟨1⟩ w).toNat = 0 := by
    simpa using congrArg UInt256.toNat h
  rw [u256_lor_toNat] at hval
  change Nat.lor 1 w.toNat % UInt256.size = 0 at hval
  have hlt : Nat.lor 1 w.toNat < UInt256.size := by
    have hw : w.toNat < 2 ^ 256 := by
      simp [UInt256.toNat, UInt256.size]
    simpa [UInt256.size] using Nat.or_lt_two_pow (by norm_num : 1 < 2 ^ 256) hw
  rw [Nat.mod_eq_of_lt hlt] at hval
  have hbitTrue : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
    change Nat.testBit (1 ||| w.toNat) 0 = true
    rw [Nat.testBit_lor]
    norm_num
  rw [hval] at hbitTrue
  simp at hbitTrue

theorem u256_add_ne_zero_of_right_ne_zero {a b : UInt256}
    (hb : b ≠ ⟨0⟩) (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.add a b ≠ ⟨0⟩ := by
  intro hzero
  have hnat : (UInt256.add a b).toNat = a.toNat + b.toNat := by
    change (a + b).toNat = _
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt hfit
  have hsum : a.toNat + b.toNat = 0 := by
    have hz := congrArg UInt256.toNat hzero
    simpa [hnat] using hz
  have hbNat : b.toNat = 0 := by omega
  exact hb (uint256_toNat_eq_zero hbNat)

theorem u256_add_one_ne_self' (a : UInt256) : a + ⟨1⟩ ≠ a := by
  intro h
  have hmod : (a.toNat + 1) % UInt256.size = a.toNat := by
    have hnat := congrArg UInt256.toNat h
    simpa [uadd_toNat] using hnat
  have ha : a.toNat < UInt256.size := a.val.isLt
  by_cases hlt : a.toNat + 1 < UInt256.size
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have hge : UInt256.size ≤ a.toNat + 1 := Nat.le_of_not_gt hlt
    have hle : a.toNat + 1 ≤ UInt256.size := Nat.succ_le_of_lt ha
    have heq : a.toNat + 1 = UInt256.size := le_antisymm hle hge
    rw [heq, Nat.mod_self] at hmod
    have hsize : 1 < UInt256.size := by norm_num [UInt256.size]
    omega

theorem u256_gt_add_right_of_overflow (target addend : UInt256)
    (hover : UInt256.size ≤ target.toNat + addend.toNat) :
    UInt256.gt target (addend + target) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ addend.toNat + target.toNat := by
    omega
  have hsum_lt2 : addend.toNat + target.toNat < 2 * UInt256.size := by
    have ht : target.toNat < UInt256.size := target.val.isLt
    have ha : addend.toNat < UInt256.size := addend.val.isLt
    omega
  have hmod : (addend.toNat + target.toNat) % UInt256.size =
      addend.toNat + target.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (addend + target).toNat = addend.toNat + target.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (target > addend + target)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show target.toNat > (addend + target).toNat
    rw [haddNat]
    have ha : addend.toNat < UInt256.size := addend.val.isLt
    omega


theorem u256_gt_add_right_of_overflow' (count weight : UInt256)
    (hover : UInt256.size ≤ count.toNat + weight.toNat) :
    UInt256.gt count (weight + count) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ weight.toNat + count.toNat := by
    omega
  have hsum_lt2 : weight.toNat + count.toNat < 2 * UInt256.size := by
    have hc : count.toNat < UInt256.size := count.val.isLt
    have hw : weight.toNat < UInt256.size := weight.val.isLt
    omega
  have hmod : (weight.toNat + count.toNat) % UInt256.size =
      weight.toNat + count.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (weight + count).toNat = weight.toNat + count.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (count > weight + count)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show count.toNat > (weight + count).toNat
    rw [haddNat]
    have hw : weight.toNat < UInt256.size := weight.val.isLt
    omega

theorem addressMask_div256_doubleMask (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask (UInt256.div w ⟨256⟩)) =
      UInt256.land (UInt256.div w ⟨256⟩) solcAddrMask := by
  rw [u256_land_comm solcAddrMask (UInt256.land solcAddrMask (UInt256.div w ⟨256⟩))]
  rw [u256_land_comm solcAddrMask (UInt256.div w ⟨256⟩)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (UInt256.div w ⟨256⟩))


theorem accountAddress_masked_ofNat_toNat (w : UInt256) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat =
      AccountAddress.ofUInt256 (UInt256.land w solcAddrMask) := by
  apply Fin.ext
  unfold AccountAddress.ofNat AccountAddress.ofUInt256
  simp [UInt256.toNat]

theorem evm_address_of_address_toNat (a : AccountAddress) :
    EVM.address a.toNat = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt a.isLt

theorem addressWord_toNat_val (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat = beneficiaryAddress.val := by
  exact ulit_toNat' _ (lt_of_lt_of_le beneficiaryAddress.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem accountAddress_of_addressWord_toNat (beneficiaryAddress : AccountAddress) :
    AccountAddress.ofNat (EVM.word beneficiaryAddress).toNat = beneficiaryAddress := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [addressWord_toNat_val, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt beneficiaryAddress.isLt

theorem addressWord_canonical_of_address (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat < EVM.addressModulus := by
  rw [addressWord_toNat_val]
  simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size]

theorem uint256Word_of_nonneg_int_toNat (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256)) :
    (EVM.word biddingTime.toNat).toNat = biddingTime.toNat :=
  constructorUInt256Word_toNat biddingTime h0 hlt

theorem uint256Word_of_nonneg_int_toNat' (revealTime : Int)
    (h0 : 0 ≤ revealTime)
    (hlt : revealTime < Int.ofNat (EVM.twoPow 256)) :
    (EVM.word revealTime.toNat).toNat = revealTime.toNat :=
  constructorUInt256Word_toNat revealTime h0 hlt

theorem add4_word_add31_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    (((⟨4⟩ : UInt256) + w) + ⟨31⟩).toNat = 4 + w.toNat + 31 := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd3_ofNat_toNat (a := 4) (b := w.toNat) (c := 31)
    (by norm_num [UInt256.size])
    w.val.isLt
    (by norm_num [UInt256.size])
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega)
    (by
      rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
      norm_num [UInt256.size]
      omega))

theorem add4_word_toNat (w : UInt256)
    (hle : w.toNat ≤ solcMaxU64) :
    ((⟨4⟩ : UInt256) + w).toNat = 4 + w.toNat := by
  rw [← u256_ofNat_toNat w]
  simpa [u256_ofNat_toNat] using
    (uadd_ofNat_toNat (a := 4) (b := w.toNat)
      (by norm_num [UInt256.size])
      w.val.isLt
      (by
        rw [show solcMaxU64 = 18446744073709551615 by rfl] at hle
        norm_num [UInt256.size]
        omega))

theorem calldataArrayElemAddr_toNat {off i : UInt256} {lim : Nat}
    (hbound : 4 + (off.toNat + 32 + 32 * i.toNat) + 32 ≤ lim)
    (hsize : lim < UInt256.size) :
    (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + off) + ⟨32⟩)).toNat =
      4 + (off.toNat + 32 + 32 * i.toNat) := by
  have hmul : (UInt256.mul (⟨32⟩ : UInt256) i).toNat = 32 * i.toNat := by
    unfold UInt256.mul
    change (((⟨32⟩ : UInt256).val * i.val).val) = 32 * i.toNat
    rw [Fin.val_mul]
    have hprod : 32 * i.toNat < UInt256.size := by omega
    rw [show (⟨32⟩ : UInt256).val.val = 32 by decide]
    exact Nat.mod_eq_of_lt hprod
  have h4off32 : (((⟨4⟩ : UInt256) + off) + ⟨32⟩).toNat =
      4 + off.toNat + 32 := by
    rw [← u256_ofNat_toNat off]
    simpa [u256_ofNat_toNat, Nat.add_assoc] using
      (uadd3_ofNat_toNat (a := 4) (b := off.toNat) (c := 32)
        (by norm_num [UInt256.size]) off.val.isLt (by norm_num [UInt256.size])
        (by omega) (by omega))
  rw [uadd_toNat, hmul, h4off32]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem not_mload64_oob_of_aw_ge3_small {aw : UInt256}
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size) :
    ¬ ((⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) := by
  intro h
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    rw [u256_mul_op_toNat]
    exact Nat.mod_eq_of_lt hawSmall
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  change (⟨64⟩ : UInt256).toNat ≥ (aw * ⟨32⟩ : UInt256).toNat at h
  rw [h64, hmul] at h
  omega

theorem word_ne_of_u256_eq_zero {a b : UInt256}
    (h : UInt256.eq a b = ⟨0⟩) : a ≠ b := by
  intro heq
  rw [heq, u256_eq_refl] at h
  have hnat := congrArg UInt256.toNat h
  change (1 : Nat) = 0 at hnat
  omega

theorem addressWord_canonical (a : AccountAddress) :
    (UInt256.ofNat a.val).toNat < EVM.addressModulus := by
  rw [UInt256.toNat_ofNat_of_lt
    (lt_of_lt_of_le a.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt

theorem checkedAddNoOverflowGt (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (b + a) = ⟨0⟩ := by
  have hsum : (b + a).toNat = b.toNat + a.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  exact ugt_zero (by rw [hsum]; omega)

theorem checkedAddOverflowGt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (b + a) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ b.toNat + a.toNat := by omega
  have hsum_lt2 : b.toNat + a.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (b.toNat + a.toNat) % UInt256.size =
      b.toNat + a.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : (b + a).toNat = b.toNat + a.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (a > b + a)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show a.toNat > (b + a).toNat
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega

/-- `wordOfInt (Int.ofNat k) = ofNat k` (a nonnegative literal round-trips through `ℤ`). -/
theorem wordOfInt_ofNat_eq (k : ℕ) : EVM.wordOfInt (Int.ofNat k) = UInt256.ofNat k := by
  rw [EVM.wordOfInt, if_neg (by simp)]; apply u256_inj
  show (Int.ofNat k).toNat % EVM.twoPow 256 = (UInt256.ofNat k).toNat
  rw [show (Int.ofNat k).toNat = k from rfl, show (UInt256.ofNat k).toNat = k % UInt256.size from
    rfl,
      show EVM.twoPow 256 = UInt256.size from by decide]

theorem ofNat_toNat_lt (n : ℕ) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  ulit_toNat' n h

theorem u256_min32_ofNat_toNat_of_ge32 (n : ℕ) (h1 : 32 ≤ n) (h2 : n < UInt256.size) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = 32
  rw [if_pos (show (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_)]
  · rfl
  · show (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ofNat_toNat_lt n h2]; omega

theorem u256_min32_ofNat_toNat_of_lt32 (n : ℕ) (h : n < 32) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg (show ¬ (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_), ofNat_toNat_lt n hnsize]
  · show ¬ (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ofNat_toNat_lt n (by omega)]; omega


theorem word_ofNat_add_one_eq (slot : UInt256) :
    EVM.word (slot.toNat + 1) = slot + (⟨1⟩ : UInt256) := by
  apply u256_inj
  rw [uadd_toNat]
  change (slot.toNat + 1) % UInt256.size = (slot.toNat + 1) % UInt256.size
  rfl

theorem divPow224_testBit (n i : Nat) (h224 : 224 ≤ i) :
    (n / 2 ^ 224).testBit (i - 224) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  change n / (2 ^ 224 * 2 ^ (i - 224)) % 2 = 1 ↔ n / 2 ^ i % 2 = 1
  rw [← Nat.pow_add, show 224 + (i - 224) = i by omega]

theorem natLandClearLow224 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ 224) = (n / 2 ^ 224) * 2 ^ 224 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ 224)).testBit i =
    ((n / 2 ^ 224) * 2 ^ 224).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ 224 = (2 ^ 32 - 1) <<< 224 by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]]
  rw [testBit_shiftLeft]
  rw [show (n / 2 ^ 224) * 2 ^ 224 = (n / 2 ^ 224) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft]
  by_cases hi224 : i < 224
  · simp [hi224]
  · simp [hi224]
    have h224 : 224 ≤ i := Nat.le_of_not_gt hi224
    by_cases hi256 : i < 256
    · have hlt : i - 224 < 32 := by omega
      change (n.testBit i && (((2 : Nat) ^ 32 - 1).testBit (i - 224))) =
        (n / 2 ^ 224).testBit (i - 224)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hlt]
      exact (divPow224_testBit n i h224).symm
    · have hnlt : ¬ i - 224 < 32 := by omega
      change (n.testBit i && (((2 : Nat) ^ 32 - 1).testBit (i - 224))) =
        (n / 2 ^ 224).testBit (i - 224)
      rw [Nat.testBit_two_pow_sub_one]
      simp [hnlt]
      change (n / 2 ^ 224).testBit (i - 224) = false
      have hq : n / 2 ^ 224 < 2 ^ 32 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact hn
      have hpow : n / 2 ^ 224 < 2 ^ (i - 224) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

theorem accountAddress_ofNat_zero_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0 ↔ w = ⟨0⟩ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    unfold AccountAddress.ofNat at hv
    simp only [Fin.val_ofNat] at hv
    have hwmod : w.toNat % AccountAddress.size = w.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
    rw [hwmod] at hv
    exact uint256_toNat_eq_zero hv
  · intro h
    rw [h]
    rfl

theorem maskedWord_ne_zero_of_canonical_ne_zero {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hnz : w ≠ ⟨0⟩) :
    UInt256.land solcAddrMask w ≠ ⟨0⟩ := by
  rw [solcAddrMask_clean_left hcanon]
  exact hnz

theorem maskedWord_eq_zero_of_zero {w : UInt256} (hzero : w = ⟨0⟩) :
    UInt256.land solcAddrMask w = ⟨0⟩ := by
  rw [hzero]
  decide

theorem boolCanonJump {word : UInt256}
    (hbool : word = ⟨0⟩ ∨ word = ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) ≠ ⟨0⟩ := by
  rcases hbool with rfl | rfl <;> decide

theorem boolNoncanonJump {word : UInt256}
    (hnz : word ≠ ⟨0⟩) (hno : word ≠ ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
  rw [isZero_eq_zero_of_ne hnz]
  have hone : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
  rw [hone]
  exact u256_eq_of_ne hno

theorem uint256_lnot_zero_max :
    UInt256.lnot (⟨0⟩ : UInt256) = UInt256.ofNat (UInt256.size - 1) := by
  decide

theorem u256_128_toNat : (⟨128⟩ : UInt256).toNat = 128 := by
  show (Fin.ofNat _ 128).val = 128; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt
    (lt_size_of_lt256 (by norm_num))

/-- `ADD` of two literals (toNat). -/
theorem add128_32_toNat : ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 := by
  rw [uadd_toNat, u256_128_toNat, u256_32_toNat]; show (160:ℕ) % UInt256.size = 160; exact
    Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- `EVM.word` and `UInt256.ofNat` agree (both are `⟨n % 2^256⟩`). -/
theorem evm_word_eq_ofNat (n : ℕ) : EVM.word n = UInt256.ofNat n := rfl

theorem cDiv_mul2 {v : UInt256} (h : 2 * v.toNat < UInt256.size) :
    UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩ = v := by
  apply u256_inj
  unfold UInt256.div UInt256.toNat
  simp
  change (UInt256.mul v ⟨2⟩).toNat / 2 = v.toNat
  rw [mul2_toNat h]
  exact Nat.mul_div_right v.toNat (by norm_num)

theorem cMul2_wrap_toNat {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat - UInt256.size := by
  show (v.val * (⟨2⟩ : UInt256).val).val = 2 * v.toNat - UInt256.size
  rw [Fin.val_mul]
  change (v.toNat * 2) % UInt256.size = 2 * v.toNat - UInt256.size
  rw [Nat.mul_comm]
  have hlt : 2 * v.toNat < 2 * UInt256.size := by
    have hvlt : v.toNat < UInt256.size := v.val.isLt
    omega
  rw [Nat.mod_eq_sub_mod hover]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem cDiv_mul2_overflow_lt {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩).toNat < v.toNat := by
  have hprod : (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat - UInt256.size :=
    cMul2_wrap_toNat hover
  have hdiv : (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩).toNat =
      (2 * v.toNat - UInt256.size) / 2 := by
    unfold Ethereum.UInt256.div Ethereum.UInt256.toNat
    simp only
    change (UInt256.mul v ⟨2⟩).toNat / (⟨2⟩ : UInt256).toNat = _
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide, hprod]
    change (2 * v.toNat - UInt256.size) / 2 = (2 * v.toNat - UInt256.size) / 2
    rfl
  rw [hdiv]
  apply Nat.lt_of_not_ge
  intro hge
  have hm := Nat.le_div_two_iff_mul_two_le.mp hge
  have hpos : 0 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem cEq_mul2_div_overflow {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    UInt256.eq v (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩) = ⟨0⟩ := by
  apply u256_eq_of_ne
  intro heqv
  have hlt := cDiv_mul2_overflow_lt hover
  have hnat := congrArg UInt256.toNat heqv
  omega

theorem cAdd1_overflow_gt {v : UInt256} (hover : UInt256.size ≤ v.toNat + 1) :
    UInt256.gt ⟨1⟩ (v + ⟨1⟩) = ⟨1⟩ := by
  have hvlt : v.toNat < UInt256.size := v.val.isLt
  have hle : v.toNat + 1 ≤ UInt256.size := by
    omega
  have hv : v.toNat + 1 = UInt256.size := by
    omega
  have hsum : (v + ⟨1⟩).toNat = 0 := by
    rw [uadd_toNat]
    change (v.toNat + 1) % UInt256.size = 0
    rw [hv, Nat.mod_self]
  show UInt256.fromBool (decide ((⟨1⟩ : UInt256) > (v + ⟨1⟩))) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show (⟨1⟩ : UInt256).toNat > (v + ⟨1⟩).toNat
    rw [hsum]
    decide

theorem solcAddrMask_literal_eval :
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
  decide

theorem ctorCheckedAddOverflowLt (timestamp biddingTime : UInt256)
    (hover : UInt256.size ≤ timestamp.toNat + biddingTime.toNat) :
    UInt256.lt (biddingTime + timestamp) timestamp = ⟨1⟩ :=
  constructorCheckedAddOverflowLt timestamp biddingTime hover

theorem ctorCheckedAddNoOverflowLt (timestamp biddingTime : UInt256)
    (hno : ¬ UInt256.size ≤ timestamp.toNat + biddingTime.toNat) :
    UInt256.lt (biddingTime + timestamp) timestamp = ⟨0⟩ :=
  constructorCheckedAddNoOverflowLt timestamp biddingTime hno


theorem wordMul32_not_le64_of_ge3 {aw : UInt256}
    (hge : 3 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h64 : (⟨64⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h64
  change 64 ≥ aw.toNat * 32 at h64
  nlinarith

theorem set_Mul32_not_le128_of_ge5 {aw : UInt256}
    (hge : 5 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h128 : (⟨128⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h128
  change 128 ≥ aw.toNat * 32 at h128
  nlinarith

theorem u256_div2_toNat_lt_sign {header len : UInt256}
    (hlen : len = UInt256.div header ⟨2⟩) :
    len.toNat < 2 ^ 255 := by
  have hlenNat : len.toNat = header.toNat / 2 := by
    rw [hlen, udiv_toNat]
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [hlenNat]
  apply Nat.div_lt_of_lt_mul
  have hheader : header.toNat < UInt256.size := header.val.isLt
  norm_num [UInt256.size] at hheader ⊢
  exact hheader

theorem land_one_eq_one_of_ne_zero {w : UInt256}
    (h : UInt256.land w ⟨1⟩ ≠ ⟨0⟩) :
    UInt256.land w ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  change (UInt256.land w ⟨1⟩).toNat = 1
  have hbit := uInt256_land_one_toNat w
  have hlt : (UInt256.land w ⟨1⟩).toNat < 2 := by
    rw [hbit]
    exact Nat.mod_lt _ (by decide)
  have hne : (UInt256.land w ⟨1⟩).toNat ≠ 0 := by
    intro hz
    exact h (uint256_toNat_eq_zero hz)
  omega

theorem ult_eq_one_of_ne_zero {a b : UInt256}
    (h : UInt256.lt a b ≠ ⟨0⟩) :
    UInt256.lt a b = ⟨1⟩ := by
  have hlt := ult_ne_zero_toNat_lt h
  exact ult_one hlt

theorem solidityBytesLongValid_gt31 {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
  have hland : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    land_one_eq_one_of_ne_zero hflag
  have hnotLt32 : UInt256.lt len ⟨32⟩ = ⟨0⟩ := by
    by_contra hltNotZero
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_eq_one_of_ne_zero hltNotZero
    exact hvalid (by simp [hland, hltOne, UInt256.sub])
  have hge32 : 32 ≤ len.toNat := by
    by_contra hlt
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_one (by
        have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
        simpa only [h32] using Nat.lt_of_not_ge hlt)
    rw [hltOne] at hnotLt32
    contradiction
  rw [show UInt256.lt ⟨31⟩ len = ⟨1⟩ from
    ult_one (by
      rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      omega)]
  decide

theorem solidityBytesLongValid_nonzero {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len ≠ ⟨0⟩ := by
  have hgt := solidityBytesLongValid_gt31 (header := header) (len := len) hflag hvalid
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt
  intro hzero
  rw [hzero] at hgtNat
  contradiction


theorem ceil32_eq_pred_div_add_one {n : Nat} (hn : 0 < n) :
    (31 + n) / 32 = (n - 1) / 32 + 1 := by
  omega

theorem u256_gt31_eq_zero_of_lt32 {len : UInt256} (hlt32 : len.toNat < 32) :
    UInt256.lt ⟨31⟩ len = ⟨0⟩ := by
  exact ult_zero (by
    rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    omega)

theorem set_Mul32_not_le64_of_ge5 {aw : UInt256}
    (hge : 5 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h64 : (⟨64⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h64
  change 64 ≥ aw.toNat * 32 at h64
  nlinarith

theorem shortPackedHeader_mask_of_short {len : UInt256}
    (hshort : len.toNat < 32) :
    UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len)) =
      UInt256.ofNat (2 ^ 256 - 2 ^ (256 - 8 * len.toNat)) := by
  let n := len.toNat
  have hlen : len = UInt256.ofNat n := (u256_ofNat_toNat len).symm
  rw [hlen]
  rw [ulit_toNat' n (by
    have : n < 32 := hshort
    norm_num [UInt256.size] at this ⊢
    omega)]
  change UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ (UInt256.ofNat n))) =
    UInt256.ofNat (2 ^ 256 - 2 ^ (256 - 8 * n))
  change n < 32 at hshort
  interval_cases n <;> decide

theorem solidityBytesHeaderWord_long_flag {len : Nat}
    (hlong : ¬ len < 32) (hlenMax : len ≤ ABI.solcMaxU64) :
    UInt256.land (solidityBytesHeaderWord len) ⟨1⟩ ≠ ⟨0⟩ := by
  have hwordLt : len * 2 + 1 < UInt256.size := by
    have hmax : ABI.solcMaxU64 * 2 + 1 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  have hmod : (solidityBytesHeaderWord len).toNat % 2 = 1 := by
    have htoNat : (UInt256.ofNat (len * 2 + 1)).toNat = len * 2 + 1 := by
      exact ulit_toNat' (len * 2 + 1) hwordLt
    rw [solidityBytesHeaderWord, if_neg hlong, htoNat]
    omega
  intro hzero
  have hbit := uInt256_land_one_toNat (solidityBytesHeaderWord len)
  rw [hmod] at hbit
  have hzeroNat := congrArg UInt256.toNat hzero
  simp [hbit] at hzeroNat

theorem uint256_land_zero_left (x : UInt256) :
    UInt256.land ⟨0⟩ x = ⟨0⟩ := by
  apply u256_inj
  change (0 &&& x.val.val) % UInt256.size = 0
  rw [Nat.zero_and]
  decide

theorem uint256_land_zero_right (x : UInt256) :
    UInt256.land x ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  change (x.val.val &&& 0) % UInt256.size = 0
  rw [Nat.and_zero]
  decide

theorem uint256_lor_zero_left (x : UInt256) :
    UInt256.lor ⟨0⟩ x = x := by
  apply u256_inj
  change (0 ||| x.val.val) % UInt256.size = x.val.val
  rw [Nat.zero_or]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_lor_zero_right (x : UInt256) :
    UInt256.lor x ⟨0⟩ = x := by
  apply u256_inj
  change (x.val.val ||| 0) % UInt256.size = x.val.val
  rw [Nat.or_zero]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_add_zero_right (x : UInt256) : x + ⟨0⟩ = x := by
  apply u256_inj
  rw [uadd_toNat]
  change (x.toNat + 0) % UInt256.size = x.toNat
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_sub_zero_right (x : UInt256) : UInt256.sub x ⟨0⟩ = x := by
  apply u256_inj
  have hle : (⟨0⟩ : UInt256).toNat ≤ x.toNat := by
    change 0 ≤ x.toNat
    exact Nat.zero_le _
  rw [usub_toNat (a := x) (b := (⟨0⟩ : UInt256)) hle]
  rfl

theorem nat_ceil32_le_ceil32 {a b : Nat} (h : a ≤ b) :
    (a + 31) / 32 ≤ (b + 31) / 32 := by
  exact Nat.div_le_div_right (Nat.add_le_add_right h 31)

theorem nat_ceil32_eq_div_of_mod_zero {n : Nat} (hmod : n % 32 = 0) :
    (n + 31) / 32 = n / 32 := by
  have hdiv := Nat.div_add_mod n 32
  omega

theorem u256_div_add31_toNat_of_lt_sign {x : UInt256} (hx : x.toNat < 2 ^ 255) :
    (UInt256.div (x + ⟨31⟩) ⟨32⟩).toNat = (x.toNat + 31) / 32 := by
  have hadd : (x + (⟨31⟩ : UInt256)).toNat = x.toNat + 31 := by
    rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hsize' : (2 : Nat) ^ 255 + 31 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]

theorem u256_div_add31_toNat_of_u64 {x : UInt256}
    (hx : x.toNat ≤ ABI.solcMaxU64) :
    (UInt256.div (x + ⟨31⟩) ⟨32⟩).toNat = (x.toNat + 31) / 32 := by
  exact u256_div_add31_toNat_of_lt_sign (x := x) (by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega)

theorem ugt_eq_one_toNat_lt {a b : UInt256} (h : UInt256.gt a b = ⟨1⟩) :
    b.toNat < a.toNat := by
  by_contra hlt
  have hle : a.toNat ≤ b.toNat := Nat.le_of_not_gt hlt
  have hzero : UInt256.gt a b = ⟨0⟩ := ugt_zero hle
  rw [hzero] at h
  contradiction

theorem u256_32_add_ofNat (n : Nat) :
    (⟨32⟩ : UInt256) + UInt256.ofNat n = UInt256.ofNat (n + 32) := by
  apply u256_inj
  rw [uadd_toNat]
  change (32 + (Fin.ofNat UInt256.size n).val) % UInt256.size =
    (Fin.ofNat UInt256.size (n + 32)).val
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have h32 : 32 % UInt256.size = 32 := by norm_num [UInt256.size]
  rw [← h32, ← Nat.add_mod]
  congr 1
  omega

theorem u256_base_one_add_ofNat (base : UInt256) (i : Nat) :
    (⟨1⟩ : UInt256) + (base + UInt256.ofNat i) =
      base + UInt256.ofNat (i + 1) := by
  rw [u256_add_comm (⟨1⟩ : UInt256) (base + UInt256.ofNat i)]
  rw [u256_add_assoc]
  rw [u256_add_comm (UInt256.ofNat i) (⟨1⟩ : UInt256)]
  rw [u256_one_add_ofNat]

theorem u256_add_left_cancel (a b c : UInt256) (h : a + b = a + c) : b = c := by
  cases a with
  | mk av =>
      cases b with
      | mk bv =>
          cases c with
          | mk cv =>
              simp [HAdd.hAdd, Add.add, UInt256.add] at h ⊢
              exact add_left_cancel h

theorem u256_base_ofNat_ne_of_ne {base : UInt256} {i j : Nat}
    (hi : i < UInt256.size) (hj : j < UInt256.size) (hne : i ≠ j) :
    base + UInt256.ofNat i ≠ base + UInt256.ofNat j := by
  intro h
  have hij : UInt256.ofNat i = UInt256.ofNat j := u256_add_left_cancel base _ _ h
  have hnat := congrArg UInt256.toNat hij
  rw [ulit_toNat' i hi, ulit_toNat' j hj] at hnat
  exact hne hnat

theorem u256_stride32_succ_ofNat (i : Nat) :
    (⟨32⟩ : UInt256) + UInt256.ofNat (32 * (i + 1)) =
      UInt256.ofNat (32 * (i + 2)) := by
  rw [u256_32_add_ofNat]
  congr 1

theorem longDataWordsLoopReadAddr_tail_toNat {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (_hmod : len.toNat % 32 ≠ 0) :
    ((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))).toNat =
      160 + 32 * (len.toNat / 32) := by
  rw [uadd_toNat]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  have hstrideLt : 32 * (len.toNat / 32 + 1) < UInt256.size := by
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmax : ABI.solcMaxU64 + 32 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [ulit_toNat' _ hstrideLt]
  have hsumLt : 128 + 32 * (len.toNat / 32 + 1) < UInt256.size := by
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmax : 128 + ABI.solcMaxU64 + 32 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]
  omega

theorem solidityBytesHeaderWord_eq_len_mul_two_add_one
    {len : UInt256} {n : Nat}
    (hsize : n = len.toNat)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    solidityBytesHeaderWord n = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
  subst n
  rw [solidityBytesHeaderWord, if_neg hlong]
  apply u256_inj
  rw [uadd_toNat]
  rw [umul_toNat (a := len) (b := (⟨2⟩ : UInt256)) (by
    have hmax : ABI.solcMaxU64 * 2 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    have htwo : (⟨2⟩ : UInt256).toNat = 2 := by decide
    rw [htwo]
    omega)]
  rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
  have hwordLt : len.toNat * 2 + 1 < UInt256.size := by
    have hmax : ABI.solcMaxU64 * 2 + 1 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hwordLt]
  rw [ulit_toNat' (len.toNat * 2 + 1) hwordLt]

theorem u256_lnot_31_toNat :
    (UInt256.lnot (⟨31⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 5 := by
  decide

theorem nat_land_31_eq_mod_32 (n : Nat) :
    Nat.land n 31 = n % 32 := by
  have hmask : Nat.land n (2 ^ 5 - 1) = n % 2 ^ 5 := by
    apply Nat.eq_of_testBit_eq
    intro i
    show (n &&& (2 ^ 5 - 1)).testBit i = (n % 2 ^ 5).testBit i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases hi : i < 5
    · rw [decide_eq_true hi]
      simp
    · rw [decide_eq_false hi]
      simp
  simpa using hmask

theorem u256_land_31_toNat (len : UInt256) :
    (UInt256.land len ⟨31⟩).toNat = len.toNat % 32 := by
  rw [u256_land_toNat]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  rw [nat_land_31_eq_mod_32]
  exact Nat.mod_eq_of_lt (by
    have hlt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    norm_num [UInt256.size] at hlt ⊢
    omega)

theorem nat_land_high_mask5_eq_div_mul {n : Nat} (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 5) = (n / 32) * 32 := by
  have h32 : (32 : Nat) = 2 ^ 5 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 5)).testBit i = ((n / 32) * 32).testBit i
  rw [Nat.testBit_and]
  rw [show (n / 32) * 32 = (n / 2 ^ 5) <<< 5 by
    rw [h32, Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft]
  by_cases hi5 : i < 5
  · have hmask : (2 ^ 256 - 2 ^ 5).testBit i = false := by
      rw [show (2 : Nat) ^ 256 - 2 ^ 5 = (2 ^ (256 - 5) - 1) <<< 5 by
        rw [Nat.shiftLeft_eq]
        rw [Nat.sub_mul]
        simp]
      rw [testBit_shiftLeft]
      simp [hi5]
    rw [hmask]
    simp [hi5]
  · have h5i : 5 ≤ i := Nat.le_of_not_gt hi5
    by_cases hi256 : i < 256
    · have hmask :
          (2 ^ 256 - 2 ^ 5).testBit i = true := by
        rw [show (2 : Nat) ^ 256 - 2 ^ 5 = (2 ^ (256 - 5) - 1) <<< 5 by
          rw [Nat.shiftLeft_eq]
          rw [Nat.sub_mul]
          simp]
        rw [testBit_shiftLeft]
        simp [hi5]
        change (2 ^ (256 - 5) - 1).testBit (i - 5) = true
        rw [Nat.testBit_two_pow_sub_one]
        simp [show i - 5 < 256 - 5 by omega]
      rw [hmask]
      simp [hi5]
      simpa [h32] using (divPow_testBit n 5 i h5i).symm
    · have hmask :
          (2 ^ 256 - 2 ^ 5).testBit i = false := by
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by
          have hpos : 0 < 2 ^ 5 := by norm_num
          omega) (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hi256)))
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hi256)))
      have hdivbit : (n / 2 ^ 5).testBit (i - 5) = false := by
        rw [divPow_testBit n 5 i h5i, hnbit]
      rw [hmask, hdivbit]
      simp [hi5]

theorem longDataCutoff_toNat (len : UInt256) :
    (UInt256.land len (UInt256.lnot ⟨31⟩)).toNat = (len.toNat / 32) * 32 := by
  rw [u256_land_toNat, u256_lnot_31_toNat]
  have hlenLt : len.toNat < 2 ^ 256 := by
    change len.toNat < UInt256.size
    exact len.val.isLt
  have hland := nat_land_high_mask5_eq_div_mul (n := len.toNat) hlenLt
  rw [hland]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self len.toNat 32) len.val.isLt)

theorem longDataNoTail (len : UInt256) (hmod : len.toNat % 32 = 0) :
    UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨0⟩ := by
  apply ult_zero
  rw [longDataCutoff_toNat]
  have hdiv := Nat.div_add_mod len.toNat 32
  omega

theorem longDataTail (len : UInt256) (hmod : len.toNat % 32 ≠ 0) :
    UInt256.isZero (UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len) = ⟨0⟩ := by
  have hltWord : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨1⟩ := by
    apply ult_one
    rw [longDataCutoff_toNat]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmodPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  rw [hltWord]
  decide

theorem accountAddress_ofNat_toNat (a : AccountAddress) :
    AccountAddress.ofNat a.toNat = a := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt a.isLt

theorem accountAddress_ofNat_val (a : AccountAddress) :
    AccountAddress.ofNat (↑a : Nat) = a :=
  accountAddress_ofNat_toNat a

set_option maxHeartbeats 1000000 in
theorem natLandClearMiddle112_224 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224) =
      n % 2 ^ 112 + (n / 2 ^ 224) * 2 ^ 224 := by
  have hlowLt : n % 2 ^ 112 < 2 ^ 224 := by
    exact lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 112)) (by norm_num)
  have hmaskLowLt : 2 ^ 112 - 1 < 2 ^ 224 := by norm_num
  have hmaskEq :
      Nat.lor (2 ^ 112 - 1) ((2 ^ 32 - 1) * 2 ^ 224) =
        (2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224 := by
    rw [nat_lor_shift_add (2 ^ 112 - 1) (2 ^ 32 - 1) 224 hmaskLowLt]
  have hrhsEq :
      Nat.lor (n % 2 ^ 112) ((n / 2 ^ 224) * 2 ^ 224) =
        n % 2 ^ 112 + (n / 2 ^ 224) * 2 ^ 224 := by
    rw [nat_lor_shift_add (n % 2 ^ 112) (n / 2 ^ 224) 224 hlowLt]
  rw [← hmaskEq, ← hrhsEq]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 112 - 1) ||| ((2 ^ 32 - 1) * 2 ^ 224))).testBit i =
    ((n % 2 ^ 112) ||| (n / 2 ^ 224 * 2 ^ 224)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (2 ^ 32 - 1) * 2 ^ 224 = (2 ^ 32 - 1) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [show n / 2 ^ 224 * 2 ^ 224 = (n / 2 ^ 224) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi112 : i < 112
  · have hi224 : i < 224 := by omega
    simp [hi112, hi224]
  · by_cases hi224 : i < 224
    · simp [hi112, hi224]
    · have h224le : 224 ≤ i := Nat.le_of_not_gt hi224
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi256 : i < 256
      · have hsub32 : i - 224 < 32 := by omega
        rw [show decide (i - 224 < 32) = true by simp [hsub32]]
        rw [divPow_testBit n 224 i h224le]
        simp [hi112, hi224]
      · have hsub32 : ¬ (i - 224 < 32) := by omega
        rw [show decide (i - 224 < 32) = false by simp [hsub32]]
        have hnfalse : n.testBit i = false := by
          have hpow : n < 2 ^ i :=
            lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
          exact Nat.testBit_lt_two_pow hpow
        rw [divPow_testBit n 224 i h224le, hnfalse]
        simp [hi112, hi224]

theorem decodeLenCheckOk_4_32_lt {sz : ℕ}
    (hsz36 : 36 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨32⟩ : UInt256)) (by simpa using hsz36) hsize

theorem decodeLenCheckOk_4_64_lt {sz : ℕ}
    (hsz68 : 68 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨64⟩ : UInt256)) (by simpa using hsz68) hsize

theorem decodeLenCheckOk_4_96_lt {sz : ℕ}
    (hsz100 : 100 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨96⟩ : UInt256)) (by simpa using hsz100) hsize


theorem accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero {n : Nat}
    (hn : n < UInt256.size)
    (hmask : UInt256.land (UInt256.ofNat n) solcAddrMask = ⟨0⟩) :
    AccountAddress.ofNat n = AccountAddress.ofNat 0 := by
  have hmaskNat :
      Nat.land n (2 ^ 160 - 1) = 0 := by
    have htoNat := congrArg UInt256.toNat hmask
    rw [u256_land_toNat, UInt256.toNat_ofNat_of_lt hn,
      show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide] at htoNat
    have hlandLt : Nat.land n (2 ^ 160 - 1) < UInt256.size := by
      exact lt_of_le_of_lt (nat_land_le_right n (2 ^ 160 - 1))
        (by decide : 2 ^ 160 - 1 < UInt256.size)
    have hlandLt' :
        Nat.land n 1461501637330902918203684832716283019655932542975 < UInt256.size := by
      simpa using hlandLt
    simpa [Nat.mod_eq_of_lt hlandLt'] using htoNat
  apply Fin.ext
  unfold AccountAddress.ofNat
  simp only [Fin.val_ofNat]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [← nat_land_mask_eq_mod n 160, hmaskNat]
  rfl

theorem accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero {n : Nat}
    (hn : n < UInt256.size)
    (hmask : UInt256.land (UInt256.ofNat n) solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat n ≠ AccountAddress.ofNat 0 := by
  intro haddr
  apply hmask
  apply u256_inj
  rw [u256_land_toNat, UInt256.toNat_ofNat_of_lt hn,
    show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide]
  have hmod : n % 2 ^ 160 = 0 := by
    have hval := congrArg Fin.val haddr
    unfold AccountAddress.ofNat at hval
    simpa [AccountAddress.size] using hval
  rw [nat_land_mask_eq_mod, hmod]
  rfl

theorem wordOfInt_toNat_lt_of_int_lt
    (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) :
    (UInt256.ofNat rootKLast.toNat).toNat < (UInt256.ofNat rootK.toNat).toNat := by
  have hrootKPos : 0 < rootK := by omega
  have hlastSize : rootKLast.toNat < UInt256.size := by
    have hlastLe : rootKLast.toNat ≤ rootK.toNat :=
      Int.toNat_le_toNat (by omega)
    exact lt_of_le_of_lt hlastLe hrootKSize
  rw [ulit_toNat' _ hlastSize, ulit_toNat' _ hrootKSize]
  exact (Int.toNat_lt_toNat hrootKPos).mpr hroot

theorem wordOfInt_toNat_le_of_int_not_gt
    (rootK rootKLast : Int)
    (hroot : ¬ rootK > rootKLast)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastSize : rootKLast.toNat < UInt256.size) :
    (UInt256.ofNat rootK.toNat).toNat ≤ (UInt256.ofNat rootKLast.toNat).toNat := by
  rw [ulit_toNat' _ hrootKSize, ulit_toNat' _ hrootKLastSize]
  exact Int.toNat_le_toNat (by omega)

theorem sqrtLoop_step_add_le_y_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    y / x + x ≤ y := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hdiv3 : y / x ≤ y / 3 := Nat.div_le_div_left (a := y) hx3 (by norm_num)
    omega

theorem sqrtLoop_step_next_low_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    2 ≤ (y / x + x) / 2 := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hxLeY : x ≤ y := by omega
    have hdivPos : 0 < y / x := Nat.div_pos hxLeY (by omega)
    omega

theorem sqrtLoop_step_next_high_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    (y / x + x) / 2 ≤ y / 2 + 1 := by
  have hsum := sqrtLoop_step_add_le_y_of_bounds y x hy hxLow hxHigh
  have hdiv : (y / x + x) / 2 ≤ y / 2 := Nat.div_le_div_right hsum
  omega

theorem intOfNat_toNat_ne_zero_of_u256_ne_zero (w : UInt256) (h : w ≠ ⟨0⟩) :
    Int.ofNat w.toNat ≠ 0 := by
  intro hzero
  apply h
  apply u256_inj
  have hnat : w.toNat = 0 := by
    exact Int.ofNat_eq_zero.mp hzero
  simpa using hnat

theorem accountAddress_ofNat_toNat_eq_mask (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land solcAddrMask w).toNat := by
  have hkey := keyValueToWord_address_ofNat_mask w
  rw [keyValueToWord_address] at hkey
  have hto := congrArg UInt256.toNat hkey
  have hleft : (UInt256.ofNat (AccountAddress.ofNat w.toNat).val).toNat =
      (AccountAddress.ofNat w.toNat).val := by
    exact UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide))
  rw [hleft] at hto
  exact hto

theorem uint256_mul_div_eq_zero_of_overflow {a b : UInt256}
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨0⟩ := by
  have hbNat : b.toNat ≠ 0 := by
    intro hb
    have hprod : a.toNat * b.toNat = 0 := by simp [hb]
    have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  apply u256_eq_of_ne
  intro heq
  have hnat := congrArg UInt256.toNat heq
  have hdivNat : (UInt256.div (UInt256.mul a b) b).toNat =
      ((a.toNat * b.toNat) % UInt256.size) / b.toNat := by
    unfold UInt256.div UInt256.toNat
    simp only
    change (UInt256.mul a b).toNat / b.toNat =
      (a.toNat * b.toNat) % UInt256.size / b.toNat
    rw [u256_mul_toNat]
  have hdivEq : ((a.toNat * b.toNat) % UInt256.size) / b.toNat = a.toNat := by
    simpa [hdivNat] using hnat
  have hle : a.toNat * b.toNat ≤ (a.toNat * b.toNat) % UInt256.size := by
    calc
      a.toNat * b.toNat =
          (((a.toNat * b.toNat) % UInt256.size) / b.toNat) * b.toNat := by
        rw [hdivEq]
      _ ≤ (a.toNat * b.toNat) % UInt256.size := Nat.div_mul_le_self _ _
  have hmodLt : (a.toNat * b.toNat) % UInt256.size < a.toNat * b.toNat := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num [UInt256.size])) hover
  omega

theorem accountAddressOfNat_word_eq_mask (w : UInt256) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).val = UInt256.land solcAddrMask w := by
  apply u256_inj
  rw [u256_land_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_comm, nat_land_mask_eq_mod]
  have hleft :
      (UInt256.ofNat (AccountAddress.ofNat w.toNat).val).toNat = w.toNat % 2 ^ 160 := by
    simp only [AccountAddress.ofNat, UInt256.ofNat, UInt256.toNat, Fin.ofNat]
    change (w.toNat % AccountAddress.size) % UInt256.size = w.toNat % 2 ^ 160
    have hlt : w.toNat % AccountAddress.size < UInt256.size := by
      exact lt_of_lt_of_le (Nat.mod_lt w.toNat (show 0 < AccountAddress.size by decide))
        (show AccountAddress.size ≤ UInt256.size by decide)
    rw [Nat.mod_eq_of_lt hlt]
    simp [AccountAddress.size]
  have hright : w.toNat % 2 ^ 160 % UInt256.size = w.toNat % 2 ^ 160 := by
    rw [Nat.mod_eq_of_lt]
    exact lt_trans (Nat.mod_lt w.toNat (show 0 < 2 ^ 160 by norm_num))
      (by norm_num [UInt256.size])
  rw [hright]
  exact hleft


theorem u256_lor_one_right_ne_zero (w : UInt256) :
    UInt256.lor w ⟨1⟩ ≠ ⟨0⟩ := by
  rw [u256_lor_comm]
  exact u256_lor_one_ne_zero' w


theorem calldataSizeGuard68 {n : Nat} (hsz68 : 68 ≤ n) (hsize : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) ⟨68⟩ = ⟨0⟩ := by
  have hnot : ¬ (UInt256.ofNat n < (⟨68⟩ : UInt256)) := by
    intro hlt
    have hltNat : (UInt256.ofNat n).toNat < (⟨68⟩ : UInt256).toNat := hlt
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    rw [hn] at hltNat
    change n < 68 at hltNat
    omega
  unfold UInt256.lt UInt256.fromBool Bool.toUInt256
  rw [show decide (UInt256.ofNat n < (⟨68⟩ : UInt256)) = false from by
    exact decide_eq_false hnot]
  decide

theorem u256_shiftRight160_zero_of_lt (w : UInt256)
    (h : w.toNat < EVM.addressModulus) :
    UInt256.shiftRight w ⟨160⟩ = ⟨0⟩ := by
  apply u256_inj
  cases w with
  | mk val =>
    unfold UInt256.shiftRight
    simp
    change (val >>> 160).val = 0
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    simpa [EVM.addressModulus] using h

theorem u256_xor_ne_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.xor a b ≠ ⟨0⟩ := by
  cases a with
  | mk av =>
      cases b with
      | mk bv =>
          simp [UInt256.xor] at h ⊢
          intro hx
          apply h
          apply Fin.ext
          have hxv := congrArg Fin.val hx
          have hxv' : (av.val ^^^ bv.val) % UInt256.size = 0 := by
            simpa [Fin.xor] using hxv
          have hlt : av.val ^^^ bv.val < UInt256.size := by
            simpa [UInt256.size] using Nat.xor_lt_two_pow (n := 256) av.isLt bv.isLt
          have hx0 : av.val ^^^ bv.val = 0 := by
            rwa [Nat.mod_eq_of_lt hlt] at hxv'
          exact Nat.xor_eq_zero_iff.mp hx0

theorem u256_lor_ne_zero_right {a b : UInt256} (hb : b ≠ ⟨0⟩) :
    UInt256.lor a b ≠ ⟨0⟩ := by
  intro hzero
  have hlt : Nat.lor a.toNat b.toNat < UInt256.size := by
    simpa [UInt256.size] using Nat.or_lt_two_pow (n := 256) a.val.isLt b.val.isLt
  have hle : b.toNat ≤ (UInt256.lor a b).toNat := by
    rw [u256_lor_toNat, Nat.mod_eq_of_lt hlt]
    exact Nat.right_le_or
  have hlor0 : (UInt256.lor a b).toNat = 0 := by
    rw [hzero]
    rfl
  have hb0 : b.toNat = 0 := by omega
  exact hb (u256_inj hb0)


theorem shiftLeft1_ofNat_eq {n : Nat} (h : 2 * n < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat n) ⟨1⟩ = UInt256.ofNat (2 * n) := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨1⟩ : UInt256).val ≥ 256))]
  change (((UInt256.ofNat n).val.val <<< 1) % UInt256.size) = (UInt256.ofNat (2 * n)).val.val
  have hn : n < UInt256.size := by
    omega
  rw [show (UInt256.ofNat n).val.val = n by exact ulit_toNat' n hn]
  rw [show (UInt256.ofNat (2 * n)).val.val = 2 * n by exact ulit_toNat' (2 * n) h]
  rw [Nat.shiftLeft_eq]
  simpa [Nat.mul_comm] using (Nat.mod_eq_of_lt h)

theorem calldataSizeGuardOk {n m : Nat}
    (hm : m ≤ n) (hsize : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨0⟩ := by
  exact ult_zero (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    have hm' : (UInt256.ofNat m).toNat = m := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt hm hsize)
    rw [hn, hm']
    exact hm)

theorem calldataSizeGuardShort {n m : Nat}
    (hsize : n < UInt256.size) (hmlt : m < UInt256.size) (hshort : n < m) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨1⟩ := by
  exact ult_one (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    have hm : (UInt256.ofNat m).toNat = m := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hmlt
    rw [hn, hm]
    exact hshort)

theorem u256_lt_addressModulus_of_shiftRight160_zero (w : UInt256)
    (h : UInt256.shiftRight w ⟨160⟩ = ⟨0⟩) :
    w.toNat < EVM.addressModulus := by
  cases w with
  | mk val =>
    unfold UInt256.shiftRight at h
    simp at h
    have hdiv : val.val / 2 ^ 160 = 0 := by
      have hval := congrArg Fin.val h
      simpa [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow] using hval
    unfold UInt256.toNat
    change val.val < 2 ^ 160
    by_contra hnot
    have hge : 2 ^ 160 ≤ val.val := by omega
    have hpos : 0 < val.val / 2 ^ 160 := Nat.div_pos hge (by positivity)
    omega

theorem calldataSizeGuard68_short {n : Nat}
    (hsize : n < UInt256.size) (hshort : n < 68) :
    UInt256.lt (UInt256.ofNat n) ⟨68⟩ = ⟨1⟩ := by
  exact ult_one (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    rw [hn]
    change n < 68
    exact hshort)

theorem u256_sign_lt_size : EVM.twoPow 255 < UInt256.size := by
  rw [u256_size_eq_two_sign]
  exact Nat.lt_add_of_pos_right (by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255)

theorem uintWordGtMaxInt256_of_slt_ne_zero {w : UInt256}
    (hmax : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) :
    maxInt256 < Int.ofNat w.toNat := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hslt0 : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ :=
      slt_lit_zero (a := w) (m := 0) (by norm_num) (Nat.zero_le _) hlow
    exact False.elim (hmax (by simpa using hslt0))
  · unfold maxInt256
    have hge : EVM.twoPow 255 ≤ w.toNat := by omega
    have hgeInt : (2 : Int) ^ 255 ≤ Int.ofNat w.toNat := by
      exact_mod_cast (by simpa [EVM.twoPow] using hge)
    omega

theorem nat_sub_mul_mod {r a M : Nat} (hr0 : 0 < r) (ha0 : 0 < a)
    (hprod : r * a < M) :
    (M - r) * a % M = M - r * a := by
  have hrleM : r ≤ M := by nlinarith
  have hmod : (M - r) * a = (a - 1) * M + (M - r * a) := by
    apply Nat.cast_injective (R := Int)
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
    rw [Nat.cast_sub hrleM, Nat.cast_sub (by omega : 1 ≤ a),
      Nat.cast_sub (le_of_lt hprod)]
    rw [Nat.cast_mul]
    ring
  rw [hmod, Nat.add_mod, Nat.mul_mod_left]
  simp [Nat.mod_eq_of_lt (by
    have hp : 0 < r * a := Nat.mul_pos hr0 ha0
    omega : M - r * a < M)]


end Reasoning.Theory
