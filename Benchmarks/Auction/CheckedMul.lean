import Benchmarks.Auction.CheckedAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the division check used by checked uint256 multiplication.
theorem checkedMul_div_eq {a b : UInt256} (ha : a ≠ ⟨0⟩)
    (hb : b.toNat * a.toNat < UInt256.size) : UInt256.div (UInt256.mul b a) a = b := by
  have hp : 0 < a.toNat := by
    by_contra hn
    exact ha (uint256_toNat_eq_zero (by omega))
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hb, Nat.mul_div_cancel _ hp]

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

def checkedMulCondition (a b : UInt256) : UInt256 :=
  UInt256.lor (UInt256.eq b (UInt256.div (UInt256.mul b a) a)) (UInt256.isZero a)

theorem checkedMulCondition_ok {a b : UInt256} (hb : b.toNat * a.toNat < UInt256.size) :
    checkedMulCondition a b = ⟨1⟩ := by
  by_cases ha : a = ⟨0⟩
  · have hm : UInt256.mul b ⟨0⟩ = ⟨0⟩ := by
      apply u256_inj
      rw [u256_mul_toNat]
      simp
    rw [checkedMulCondition, ha, hm]
    change UInt256.lor (UInt256.eq b ⟨0⟩) ⟨1⟩ = ⟨1⟩
    by_cases hz : b = ⟨0⟩
    · rw [hz]; decide
    · rw [u256_eq_of_ne hz]; decide
  · rw [checkedMulCondition, checkedMul_div_eq ha hb, uInt256_eq_self,
      isZero_eq_zero_of_ne ha, u256_lor_zero]

theorem checkedMulCondition_fail {a b : UInt256} (hb : UInt256.size ≤ b.toNat * a.toNat) :
    checkedMulCondition a b = ⟨0⟩ := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hb
    change UInt256.size ≤ b.toNat * 0 at hb
    simp only [Nat.mul_zero] at hb
    exact (by decide : ¬ UInt256.size ≤ 0) hb
  rw [checkedMulCondition, u256_eq_of_ne (Ne.symm (checkedMul_div_ne hb)),
    isZero_eq_zero_of_ne ha, u256_lor_zero]

theorem checkedMulPrefix {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5650⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5665⟩
      (⟨4886⟩ :: checkedMulCondition a b :: UInt256.mul b a :: a :: b :: ret :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [jumpdest, dup1, dup3, mul, dup2, iszero, dup3, dup3, div,
    dup5, eq, or, push2 ⟨4886⟩]⟩

theorem checkedMulOk {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5650⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hno : b.toNat * a.toNat < UInt256.size)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (UInt256.mul b a :: R) mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5665⟩ := checkedMulPrefix h hov
  have rd4886 := evm_run rd5665 with [jumpiT (by rw [checkedMulCondition_ok hno]; decide)
    (by jump_dest)]
  exact arithmeticReturn rd4886 hret (by evm_ov)

theorem checkedMulOverflow {I g s0 a b ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5650⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ b.toNat * a.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, rd5665⟩ := checkedMulPrefix h hov
  have rd5630 := evm_run rd5665 with [jumpiNT (checkedMulCondition_fail hover),
    push2 ⟨4886⟩, push2 ⟨5630⟩, jump (by jump_dest)]
  exact arithmeticPanic rd5630 (by evm_ov)

end Auction
