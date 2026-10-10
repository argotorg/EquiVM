import Benchmarks.UniswapV4PoolManager.WordSar

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: setting every bit above a field preserves exactly its low residue.
theorem natOrFillHigh {n k width : Nat} (hk : k ≤ width) (hn : n < 2^width) :
    n ||| (2^width-2^k) = (2^width-2^k) + n % 2^k := by
  have hm : 2^width-2^k = 2^k * (2^(width-k)-1) := by
    rw [Nat.mul_sub, mul_one, ← Nat.pow_add, Nat.add_sub_of_le hk]
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
    Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · simp only [hik, if_true, show ¬i ≥ k by omega, decide_false, Bool.false_and, Bool.or_false,
      Nat.testBit_mod_two_pow, decide_true, Bool.true_and]
  · rw [if_neg hik]
    by_cases hiw : i < width
    · simp only [show i ≥ k by omega, show i-k < width-k by omega,
        decide_true, Bool.true_and, Bool.or_true]
    · have hbit : n.testBit i = false := Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [hbit, show ¬i-k < width-k by omega, decide_false, Bool.and_false, Bool.false_or]

end Benchmarks.UniswapV4PoolManager
