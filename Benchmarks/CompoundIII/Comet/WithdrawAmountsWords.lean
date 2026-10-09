import Benchmarks.CompoundIII.Comet.WithdrawAmountsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

attribute [local irreducible] signed104

-- LIBRARY CANDIDATE: the unsigned low field of a nonnegative signed principal.
theorem mask104_positivePrincipal {w : UInt256} (hp : 0 ≤ signed104 w) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
      (UInt256.ofNat 1)) w = positivePrincipal w := by
  apply u256_inj
  rw [uland_toNat, Nat.land_comm]
  change Nat.land w.toNat (2^104 - 1) = _
  rw [nat_land_mask_eq_mod w.toNat 104, positivePrincipal_toNat]
  have hs := signed104_bitvec w
  rw [BitVec.toInt_eq_toNat_cond] at hs
  change signed104 w = if 2 * (w.toNat % 2^104) < 2^104 then
    Int.ofNat (w.toNat % 2^104) else Int.ofNat (w.toNat % 2^104) - Int.ofNat (2^104) at hs
  have hm : w.toNat % 2^104 < 2^104 := Nat.mod_lt _ (by decide)
  split_ifs at hs <;> simp only [Int.ofNat_eq_natCast] at hs <;> omega

theorem withdrawSupplyAmount_lt (old next : UInt256) :
    (withdrawSupplyAmount old next).toNat < 2^104 := by
  unfold withdrawSupplyAmount
  split_ifs
  · decide
  · exact principalDecrease_lt _ _
  · decide
  · exact lt_trans (positivePrincipal_lt _) (by decide)

theorem withdrawBorrowAmount_lt {old next : UInt256} (hf : WithdrawAmountsFits old next) :
    (withdrawBorrowAmount old next).toNat < 2^104 := by
  unfold withdrawBorrowAmount
  split_ifs with hi hn ho
  · decide
  · decide
  · exact principalDecrease_lt _ _
  · have hm : -(2^103 : Int) < signed104 next := by
      simpa only [WithdrawAmountsFits, if_neg hi, if_neg hn, if_neg ho] using hf
    exact lt_trans (negativePrincipal_lt hm) (by decide)

end Benchmarks.CompoundIII.Comet
