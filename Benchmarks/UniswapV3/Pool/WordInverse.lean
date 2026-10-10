import Benchmarks.UniswapV3.Pool.WordXor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
open scoped Fin.IntCast Fin.CommRing

-- LIBRARY CANDIDATE: Newton iteration squares the error of a multiplicative inverse.
def inverseNewton {R : Type*} [CommRing R] (d seed : R) : Nat → R
  | 0 => seed
  | n + 1 => let i := inverseNewton d seed n; i * (2 - d * i)

theorem inverseNewton_error {R : Type*} [CommRing R] (d seed : R) (n : Nat) :
    1 - d * inverseNewton d seed n = (1 - d * seed) ^ (2 ^ n) := by
  induction n with
  | zero => simp [inverseNewton]
  | succ n ih =>
    calc
      _ = (1 - d * inverseNewton d seed n) ^ 2 := by simp only [inverseNewton]; ring
      _ = _ := by rw [ih, ← pow_mul, pow_succ]

def wordInverseSeed (d : UInt256) : UInt256 := UInt256.xor ⟨2⟩ (UInt256.mul ⟨3⟩ d)

-- LIBRARY CANDIDATE: the bitwise seed has four correct inverse bits for every odd word.
theorem wordInverseSeed_mod (d : UInt256) (hd : d.toNat % 2 = 1) :
    (d.toNat * (wordInverseSeed d).toNat) % 16 = 1 := by
  have hxor := wordXor_toNat
  have hs : (wordInverseSeed d).toNat % 16 = 2 ^^^ ((3 * (d.toNat % 16)) % 16) := by
    rw [wordInverseSeed, hxor]
    change ((2 : Nat) ^^^ (UInt256.mul ⟨3⟩ d).toNat) % 2 ^ 4 = _
    rw [Nat.xor_mod_two_pow, u256_mul_toNat,
      Nat.mod_mod_of_dvd _ (by decide : 16 ∣ UInt256.size)]
    change 2 ^^^ ((3 * d.toNat) % 16) = _
    rw [Nat.mul_mod]
  rw [Nat.mul_mod, hs]
  have hlt : d.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have ho : (d.toNat % 16) % 2 = 1 := by omega
  generalize d.toNat % 16 = r at *
  interval_cases r <;> omega

def wordInverse (d : UInt256) : UInt256 :=
  ⟨inverseNewton d.val (wordInverseSeed d).val 6⟩

theorem wordInverse_mul (d : UInt256) (hd : d.toNat % 2 = 1) :
    UInt256.mul d (wordInverse d) = ⟨1⟩ := by
  have hs := wordInverseSeed_mod d hd
  have herr : (16 : Int) ∣ 1 - (d.toNat : Int) * (wordInverseSeed d).toNat := by
    apply (Nat.modEq_iff_dvd).mp
    exact hs
  obtain ⟨t, ht⟩ := herr
  have hcast : 1 - d.val * (wordInverseSeed d).val = (16 : Fin UInt256.size) * (t : Fin UInt256.size) := by
    have h := congrArg (fun z : Int ↦ (z : Fin UInt256.size)) ht
    simpa only [Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_natCast,
      UInt256.toNat, Fin.cast_val_eq_self, Int.cast_ofNat] using h
  have hz : (1 - d.val * (wordInverseSeed d).val) ^ 64 = 0 := by
    rw [hcast, mul_pow]
    have h16 : (16 : Fin UInt256.size) ^ 64 = 0 := by decide +kernel
    rw [h16, zero_mul]
  have hi := inverseNewton_error d.val (wordInverseSeed d).val 6
  change 1 - d.val * inverseNewton d.val (wordInverseSeed d).val 6 =
    (1 - d.val * (wordInverseSeed d).val) ^ 64 at hi
  rw [hz, sub_eq_zero] at hi
  apply u256_inj
  exact congrArg Fin.val hi.symm

end Benchmarks.UniswapV3.Pool
