import Benchmarks.Morpho.MetaMorphoV1_1.FullMulTwos
import Mathlib.Data.ZMod.Basic

/-! Six Newton refinements compute the inverse of an odd denominator modulo 2^256. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def wordResidue (w : UInt256) : ZMod UInt256.size := w.val

theorem wordResidue_injective : Function.Injective wordResidue := by
  intro a b h
  apply u256_inj
  exact congrArg ZMod.val h

@[simp] theorem wordResidue_mul (a b : UInt256) :
    wordResidue (UInt256.mul a b) = wordResidue a * wordResidue b := rfl

@[simp] theorem wordResidue_sub (a b : UInt256) :
    wordResidue (UInt256.sub a b) = wordResidue a - wordResidue b := rfl

@[simp] theorem wordResidue_ofNat (n : Nat) : wordResidue (UInt256.ofNat n) = n := rfl

theorem wordResidue_natCast (w : UInt256) : (w.toNat : ZMod UInt256.size) = wordResidue w :=
  ZMod.natCast_zmod_val (wordResidue w)

def fullDivInverse (d : UInt256) : Nat → UInt256
  | 0 => UInt256.xor (UInt256.mul ⟨3⟩ d) ⟨2⟩
  | n + 1 => UInt256.mul (UInt256.sub ⟨2⟩ (UInt256.mul d (fullDivInverse d n)))
      (fullDivInverse d n)

theorem fullDivInverse_error (d : UInt256) (n : Nat) :
    1 - wordResidue d * wordResidue (fullDivInverse d n) =
      (1 - wordResidue d * wordResidue (fullDivInverse d 0)) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = (1 - wordResidue d * wordResidue (fullDivInverse d n)) ^ 2 := by
          simp only [fullDivInverse, wordResidue_mul, wordResidue_sub]
          change 1 - wordResidue d * ((2 - wordResidue d * _) * _) = _
          ring
        _ = _ := by rw [ih, ← pow_mul, ← Nat.pow_succ]

theorem fullDivInverse_seed_mod (d : UInt256) :
    (fullDivInverse d 0).toNat % 16 = ((3 * (d.toNat % 16)) % 16) ^^^ 2 := by
  change ((((3 * d.toNat) % UInt256.size) ^^^ 2) % UInt256.size) % 16 = _
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ UInt256.size)]
  change (((3 * d.toNat) % UInt256.size) ^^^ 2) % 2 ^ 4 = _
  rw [Nat.xor_mod_two_pow]
  change ((3 * d.toNat) % UInt256.size % 16) ^^^ 2 = _
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ UInt256.size), Nat.mul_mod]

theorem fullDivInverse_seed_product (d : UInt256) (hd : Odd d.toNat) :
    (d.toNat * (fullDivInverse d 0).toNat) % 16 = 1 := by
  have finite : ∀ x : Fin 16, x.val % 2 = 1 →
      (x.val * ((3 * x.val) % 16 ^^^ 2)) % 16 = 1 := by decide +kernel
  rw [Nat.mul_mod, fullDivInverse_seed_mod]
  apply finite ⟨d.toNat % 16, Nat.mod_lt _ (by decide)⟩
  change d.toNat % 16 % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)]
  exact Nat.odd_iff.mp hd

theorem fullDivInverse_seed_factor (d : UInt256) (hd : Odd d.toNat) :
    ∃ z : ZMod UInt256.size,
      1 - wordResidue d * wordResidue (fullDivInverse d 0) = 16 * z := by
  have hp := congrArg (fun n : Nat ↦ (n : ZMod UInt256.size))
    (Nat.mod_add_div (d.toNat * (fullDivInverse d 0).toNat) 16)
  simp only [fullDivInverse_seed_product d hd, Nat.cast_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, wordResidue_natCast] at hp
  refine ⟨-((d.toNat * (fullDivInverse d 0).toNat / 16 : Nat) : ZMod UInt256.size), ?_⟩
  linear_combination hp

theorem fullDivInverse_correct (d : UInt256) (hd : Odd d.toNat) :
    UInt256.mul d (fullDivInverse d 6) = ⟨1⟩ := by
  obtain ⟨z, hz⟩ := fullDivInverse_seed_factor d hd
  have hp : (16 : ZMod UInt256.size) ^ 64 = 0 := by
    change ((16 : Nat) : ZMod UInt256.size) ^ 64 = 0
    rw [← Nat.cast_pow, show (16 : Nat) ^ 64 = UInt256.size from by decide, ZMod.natCast_self]
  have he := fullDivInverse_error d 6
  rw [hz] at he
  change 1 - wordResidue d * wordResidue (fullDivInverse d 6) = (16 * z) ^ 64 at he
  rw [mul_pow, hp, zero_mul] at he
  apply wordResidue_injective
  rw [wordResidue_mul]
  change wordResidue d * wordResidue (fullDivInverse d 6) = 1
  linear_combination -he

end Benchmarks.Morpho.MetaMorphoV1_1
