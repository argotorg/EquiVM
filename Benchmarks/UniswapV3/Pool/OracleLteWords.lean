import Benchmarks.UniswapV3.Pool.OracleLteSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem oracleAdjusted_lt (time value : UInt256) (hv : value.toNat < 2 ^ 32) :
    oracleAdjusted time value < 2 ^ 40 := by
  unfold oracleAdjusted
  split <;> omega

theorem oracleAdjustedWord_toNat (time value : UInt256) (hv : value.toNat < 2 ^ 32) :
    (UInt256.ofNat (oracleAdjusted time value)).toNat = oracleAdjusted time value :=
  ulit_toNat' _ (lt_trans (oracleAdjusted_lt time value hv) (by decide))

theorem oracleAdjustedWord_clean (time value : UInt256) (hv : value.toNat < 2 ^ 32) :
    UInt256.land (UInt256.ofNat 1099511627775)
      (UInt256.ofNat (oracleAdjusted time value)) = UInt256.ofNat (oracleAdjusted time value) := by
  rw [u256_land_comm]
  apply u256LandMaskCleanOfToNat _ _ (bits := 40) (by decide)
  rw [oracleAdjustedWord_toNat time value hv]
  exact oracleAdjusted_lt time value hv

theorem oracleAdjustedWord_eq (time value : UInt256) (hv : value.toNat < 2 ^ 32) :
    UInt256.ofNat (oracleAdjusted time value) =
      if time.toNat < value.toNat then value else UInt256.ofNat 4294967296 + value := by
  by_cases h : time.toNat < value.toNat
  · simp only [oracleAdjusted, if_pos h, u256_ofNat_toNat]
  · rw [if_neg h]
    apply u256_inj
    rw [oracleAdjustedWord_toNat time value hv, uadd_toNat]
    change oracleAdjusted time value = (4294967296 + value.toNat) % UInt256.size
    rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    simp only [oracleAdjusted, if_neg h]
    omega

-- LIBRARY CANDIDATE: the EVM's unsigned less-or-equal idiom as a Boolean word.
theorem isZero_gt_le_word (a b : UInt256) :
    UInt256.isZero (UInt256.gt a b) = if a.toNat ≤ b.toNat then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : a.toNat ≤ b.toNat
  · rw [if_pos h, ugt_zero h]
    rfl
  · rw [if_neg h, ugt_one (by omega)]
    rfl

end Benchmarks.UniswapV3.Pool
