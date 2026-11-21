import Reasoning.WordArithmetic

/-! Constant subtraction expressed as addition of a complemented word. -/

open Ethereum Reasoning.Theory

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: solc's complement-of-predecessor representation of subtraction.
theorem wordAddLnotOfNat (a : UInt256) (n : Nat) (hn : n + 1 < UInt256.size) :
    a + UInt256.lnot (UInt256.ofNat n) = UInt256.sub a (UInt256.ofNat (n + 1)) := by
  apply u256_inj
  have ha := a.val.isLt
  change a.toNat < UInt256.size at ha
  have hn0 : (UInt256.ofNat n).toNat = n := Nat.mod_eq_of_lt (by omega)
  have hn1 : (UInt256.ofNat (n + 1)).toNat = n + 1 := Nat.mod_eq_of_lt hn
  rw [uadd_toNat, lnot_toNat_gen, hn0]
  by_cases hb : n + 1 ≤ a.toNat
  · rw [usub_toNat (by rw [hn1]; exact hb), hn1]
    simp only [UInt256.size] at ha hn ⊢
    omega
  · rw [usub_toNat_underflow (by rw [hn1]; omega), hn1]
    simp only [UInt256.size] at ha hn ⊢
    omega

end Benchmarks.Midnight
