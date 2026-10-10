import Benchmarks.UniswapV4PoolManager.MemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an enormous base length makes modular exponentiation unaffordable for any EVM gas word.
theorem expmodCost_large_base {base modulus iterations : Nat}
    (hb : 2^132 ≤ base) (hi : 1 ≤ iterations) :
    UInt256.size ≤ ((max base modulus+7)/8)^2*iterations/3 := by
  have hm : base ≤ max base modulus := Nat.le_max_left _ _
  have hd : 2^129 ≤ (max base modulus+7)/8 := by omega
  have hp := Nat.pow_le_pow_left hd 2
  have hi' : ((max base modulus+7)/8)^2 ≤ ((max base modulus+7)/8)^2*iterations :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hdiv : (2^129)^2/3 ≤ ((max base modulus+7)/8)^2*iterations/3 :=
    Nat.div_le_div_right (hp.trans hi')
  exact (show UInt256.size ≤ (2^129)^2/3 from by decide +kernel).trans hdiv

theorem precompile_EXPMOD_large_base {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hb : 2^132 ≤ nat_of_slice I.calldata 0 32) :
    Ξ_EXPMOD σ g A I = (∅, ⟨0⟩, A, .empty) := by
  have hgas (n : Nat) : g.toNat < max 200
      (((max (nat_of_slice I.calldata 0 32) (nat_of_slice I.calldata 64 32)+7)/8)^2*
        max n 1/3) :=
    Nat.lt_of_lt_of_le g.val.isLt
      ((expmodCost_large_base hb (Nat.le_max_right _ _)).trans (Nat.le_max_right _ _))
  simp only [Ξ_EXPMOD, hgas, if_true]

end Benchmarks.UniswapV4PoolManager
