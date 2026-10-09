import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES uadd_ofNat_toNat to equality of the resulting words.
theorem wordOfNatAdd (a b : Nat) (hab : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [ulit_toNat' _ hab]
  exact uadd_ofNat_toNat (by omega) (by omega) hab

-- LIBRARY CANDIDATE: signed greater-than reverses signed less-than.
theorem wordSgtReverse (a b : UInt256) : UInt256.sgt a b = UInt256.slt b a := by
  unfold UInt256.sgt UInt256.slt UInt256.sgtBool UInt256.sltBool
  by_cases ha : a.toNat ≥ 2 ^ 255 <;> by_cases hb : b.toNat ≥ 2 ^ 255 <;>
    simp only [ha, hb, if_true, if_false]

end Benchmarks.Safe
