import Reasoning.WordArithmetic

open Ethereum Reasoning.Theory

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: natural-to-word conversion commutes with modular arithmetic.
theorem ofNat_add_words (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  change (a % UInt256.size + b % UInt256.size) % UInt256.size = (a + b) % UInt256.size
  exact (Nat.add_mod _ _ _).symm

theorem ofNat_mul_words (a b : Nat) :
    UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a * b) := by
  apply u256_inj
  change (a % UInt256.size * (b % UInt256.size)) % UInt256.size = (a * b) % UInt256.size
  exact (Nat.mul_mod _ _ _).symm

theorem ofNat_sub_words {a b : Nat} (h : b ≤ a) (ha : a < UInt256.size) :
    UInt256.sub (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a - b) := by
  apply u256_inj
  rw [usub_ofNat_lit_toNat h ha, ulit_toNat' _ (by omega)]

-- LIBRARY CANDIDATE: the compiler represents a negative literal modulo the word size.
theorem ofNat_size_sub_add {c n : Nat} (hpos : 0 < c) (hc : c ≤ n)
    (hn : n < UInt256.size) :
    UInt256.ofNat (UInt256.size - c) + UInt256.ofNat n = UInt256.ofNat (n - c) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' _ (by omega : UInt256.size - c < UInt256.size),
    ulit_toNat' _ hn, ulit_toNat' _ (by omega : n - c < UInt256.size),
    show UInt256.size - c + n = UInt256.size + (n - c) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

end Reasoning.Theory
