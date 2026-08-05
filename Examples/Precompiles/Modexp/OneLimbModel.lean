import Examples.Precompiles.Modexp.Bridge

/-!
# Mathematical model for the single-limb ModExp path

The deployed helper scans arbitrary-length base and exponent byte strings but uses EVM `MULMOD`
once the modulus fits one word.  This file connects the helper-friendly left-to-right invariant to
the unchanged trusted right-to-left `Model.modPow` definition.
-/

namespace Modexp

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem model_modPowAux_lt (base acc modulus e : Nat)
    (hm : 0 < modulus) (hacc : acc < modulus) :
    Model.modPowAux base acc modulus e < modulus := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | h e ih =>
      rw [Model.modPowAux]
      split
      next => exact hacc
      next he =>
        apply ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))
        by_cases hbit : e % 2 = 1
        · simp only [hbit, ↓reduceIte]
          exact Nat.mod_lt _ hm
        · simp only [hbit, ↓reduceIte]
          exact hacc

private theorem model_modPowAux_modEq (base acc modulus e : Nat) :
    Model.modPowAux base acc modulus e ≡ acc * base ^ e [MOD modulus] := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | h e ih =>
      rw [Model.modPowAux]
      split
      next he =>
        simpa [he] using (Nat.ModEq.refl acc : acc ≡ acc [MOD modulus])
      next he =>
        let base' := (base * base) % modulus
        let acc' := if e % 2 = 1 then (acc * base) % modulus else acc
        have hrec := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))
          base' acc'
        have hbase : base' ≡ base * base [MOD modulus] := by
          exact Nat.mod_modEq _ _
        have hpow : base' ^ (e / 2) ≡ (base * base) ^ (e / 2) [MOD modulus] :=
          hbase.pow _
        by_cases hbit : e % 2 = 1
        · have hacc : acc' ≡ acc * base [MOD modulus] := by
            simp only [acc', hbit, ↓reduceIte]
            exact Nat.mod_modEq _ _
          have hcombined := hacc.mul hpow
          have heq : e = 2 * (e / 2) + 1 := by
            have hrem : e % 2 < 2 := Nat.mod_lt _ (by decide)
            have hdecomp := (Nat.mod_add_div e 2).symm
            omega
          have halgEq : acc * base * (base * base) ^ (e / 2) = acc * base ^ e := by
            calc
              _ = acc * base ^ (2 * (e / 2) + 1) := by
                rw [pow_add, pow_mul, pow_two, pow_one]
                ring
              _ = acc * base ^ e := congrArg (fun n => acc * base ^ n) heq.symm
          have halg : acc * base * (base * base) ^ (e / 2) ≡
              acc * base ^ e [MOD modulus] := halgEq ▸ Nat.ModEq.rfl
          exact hrec.trans (hcombined.trans halg)
        · have hrem : e % 2 = 0 := by
            have hlt : e % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          have hacc : acc' ≡ acc [MOD modulus] := by
            simpa [acc', hbit] using (Nat.ModEq.refl acc : acc ≡ acc [MOD modulus])
          have hcombined := hacc.mul hpow
          have heq : e = 2 * (e / 2) := by
            have hdecomp := (Nat.mod_add_div e 2).symm
            omega
          have halgEq : acc * (base * base) ^ (e / 2) = acc * base ^ e := by
            calc
              _ = acc * base ^ (2 * (e / 2)) := by rw [pow_mul, pow_two]
              _ = acc * base ^ e := congrArg (fun n => acc * base ^ n) heq.symm
          have halg : acc * (base * base) ^ (e / 2) ≡ acc * base ^ e [MOD modulus] :=
            halgEq ▸ Nat.ModEq.rfl
          exact hrec.trans (hcombined.trans halg)

/-- The trusted square-and-multiply kernel is ordinary modular exponentiation whenever its
accumulator is already reduced. -/
theorem model_modPowAux_eq_pow_mod (base acc modulus e : Nat)
    (hm : 0 < modulus) (hacc : acc < modulus) :
    Model.modPowAux base acc modulus e = (acc * base ^ e) % modulus := by
  have hlt := model_modPowAux_lt base acc modulus e hm hacc
  have hcong := model_modPowAux_modEq base acc modulus e
  change Model.modPowAux base acc modulus e % modulus =
    (acc * base ^ e) % modulus at hcong
  rw [Nat.mod_eq_of_lt hlt] at hcong
  exact hcong

/-- On the nontrivial-modulus branch used by `modexpWord`, the trusted model is exactly
`b^e mod m`. -/
theorem model_modPow_eq_pow_mod (b e modulus : Nat) (hm : 1 < modulus) :
    Model.modPow b e modulus = b ^ e % modulus := by
  unfold Model.modPow
  rw [if_neg (by omega : modulus ≠ 0), if_neg (by omega : modulus ≠ 1)]
  rw [model_modPowAux_eq_pow_mod (b % modulus) 1 modulus e (by omega) hm]
  have hcong : (b % modulus) ^ e ≡ b ^ e [MOD modulus] :=
    (Nat.mod_modEq b modulus).pow e
  change (b % modulus) ^ e % modulus = b ^ e % modulus at hcong
  simpa using hcong

/-- One left-to-right exponent bit: square, then optionally multiply by the reduced base. -/
def wordBitStep (base modulus acc : Nat) (bit : Bool) : Nat :=
  let squared := (acc * acc) % modulus
  if bit then (squared * base) % modulus else squared

theorem wordBitStep_eq_pow (base modulus acc pfx : Nat) (bit : Bool)
    (hm : 0 < modulus) (hacc : acc = base ^ pfx % modulus) :
    wordBitStep base modulus acc bit =
      base ^ (2 * pfx + if bit then 1 else 0) % modulus := by
  subst acc
  unfold wordBitStep
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show 2 * pfx + 0 = 2 * pfx by omega, pow_mul, pow_two, mul_pow]
    exact (Nat.mul_mod (base ^ pfx) (base ^ pfx) modulus).symm
  · simp only [↓reduceIte]
    rw [pow_add, pow_mul, pow_two, pow_one, mul_pow]
    have hsquare := (Nat.mul_mod (base ^ pfx) (base ^ pfx) modulus).symm
    calc
      _ = ((base ^ pfx * base ^ pfx) % modulus * base) % modulus :=
        congrArg (fun z => (z * base) % modulus) hsquare
      _ = (base ^ pfx * base ^ pfx * base) % modulus := by
        rw [Nat.mul_mod ((base ^ pfx * base ^ pfx) % modulus) base modulus,
          Nat.mod_mod]
        exact (Nat.mul_mod (base ^ pfx * base ^ pfx) base modulus).symm

def wordBitNat (byte t : Nat) : Nat :=
  if t = 0 then 0 else (byte / 2 ^ (t - 1)) % 2

def appendWordBits (byte : Nat) : Nat → Nat → Nat
  | 0, pfx => pfx
  | t + 1, pfx => appendWordBits byte t (2 * pfx + wordBitNat byte (t + 1))

def wordBitLoop (base modulus byte : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | t + 1, acc =>
      let bit := decide (wordBitNat byte (t + 1) = 1)
      wordBitLoop base modulus byte t (wordBitStep base modulus acc bit)

private theorem wordBitNat_le_one (byte t : Nat) : wordBitNat byte t ≤ 1 := by
  unfold wordBitNat
  split
  · omega
  · have h := Nat.mod_lt (byte / 2 ^ (t - 1)) (by decide : 0 < 2)
    omega

private theorem boolBit_eq_wordBitNat (byte t : Nat) :
    (if decide (wordBitNat byte t = 1) then 1 else 0) = wordBitNat byte t := by
  have hle := wordBitNat_le_one byte t
  by_cases h : wordBitNat byte t = 1
  · simp [h]
  · have hz : wordBitNat byte t = 0 := by omega
    simp [h, hz]

theorem wordBitLoop_eq_pow (base modulus byte t acc pfx : Nat)
    (hm : 0 < modulus) (hacc : acc = base ^ pfx % modulus) :
    wordBitLoop base modulus byte t acc =
      base ^ (appendWordBits byte t pfx) % modulus := by
  induction t generalizing acc pfx with
  | zero => simpa [wordBitLoop, appendWordBits] using hacc
  | succ t ih =>
      rw [wordBitLoop, appendWordBits]
      apply ih
      rw [wordBitStep_eq_pow base modulus acc pfx
        (decide (wordBitNat byte (t + 1) = 1)) hm hacc]
      rw [boolBit_eq_wordBitNat]

theorem appendWordBits_eight (byte pfx : Nat) (hbyte : byte < 256) :
    appendWordBits byte 8 pfx = pfx * 256 + byte := by
  simp only [appendWordBits, wordBitNat]
  interval_cases byte <;> norm_num <;> omega

/-- Processing one byte appends its eight bits to the numeric exponent prefix. -/
theorem wordBitLoop_eight_eq_pow (base modulus byte acc pfx : Nat)
    (hm : 0 < modulus) (hbyte : byte < 256)
    (hacc : acc = base ^ pfx % modulus) :
    wordBitLoop base modulus byte 8 acc = base ^ (pfx * 256 + byte) % modulus := by
  rw [wordBitLoop_eq_pow base modulus byte 8 acc pfx hm hacc,
    appendWordBits_eight byte pfx hbyte]

def appendExponentBytes (pfx : Nat) : List UInt8 → Nat
  | [] => pfx
  | b :: bs => appendExponentBytes (pfx * 256 + b.toNat) bs

def wordExponentBytes (base modulus acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: bs =>
      wordExponentBytes base modulus
        (wordBitLoop base modulus b.toNat 8 acc) bs

theorem wordExponentBytes_eq_pow (base modulus acc pfx : Nat) (bs : List UInt8)
    (hm : 0 < modulus) (hacc : acc = base ^ pfx % modulus) :
    wordExponentBytes base modulus acc bs =
      base ^ (appendExponentBytes pfx bs) % modulus := by
  induction bs generalizing acc pfx with
  | nil => simpa [wordExponentBytes, appendExponentBytes] using hacc
  | cons b bs ih =>
      rw [wordExponentBytes, appendExponentBytes]
      apply ih
      exact wordBitLoop_eight_eq_pow base modulus b.toNat acc pfx hm
        (by exact UInt8.toNat_lt b) hacc

theorem appendExponentBytes_zero_eq_model (bs : ByteArray) :
    appendExponentBytes 0 bs.toList = Model.bytesToBigEndianNat bs := by
  unfold Model.bytesToBigEndianNat
  change appendExponentBytes 0 bs.toList =
    bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
  have aux (l : List UInt8) (pfx : Nat) :
      appendExponentBytes pfx l = l.foldl (fun acc b => acc * 256 + b.toNat) pfx := by
    induction l generalizing pfx with
    | nil => rfl
    | cons b bs ih => simpa [appendExponentBytes] using ih (pfx * 256 + b.toNat)
  exact aux bs.toList 0

/-- The full byte-oriented left-to-right loop computes the trusted exponent value. -/
theorem wordExponentBytes_eq_model (base modulus : Nat) (bs : ByteArray)
    (hm : 1 < modulus) :
    wordExponentBytes base modulus 1 bs.toList =
      base ^ (Model.bytesToBigEndianNat bs) % modulus := by
  rw [wordExponentBytes_eq_pow base modulus 1 0 bs.toList (by omega)
      (by simp [Nat.mod_eq_of_lt hm]),
    appendExponentBytes_zero_eq_model]

end Modexp
