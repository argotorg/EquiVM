import Benchmarks.UniswapV3.Pool.TickSqrtModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- This closed finite check bounds the concrete TickMath factor table over its valid domain.
private theorem tickSqrtRatio_valid_table :
    (List.range 887273).all (fun n ↦ decide
      (2 ^ 64 < (tickSqrtRatio (UInt256.ofNat n)).toNat)) = true := by native_decide

theorem tickSqrtRatio_valid_lower (n : Nat) (hn : n ≤ 887272) :
    2 ^ 64 < (tickSqrtRatio (UInt256.ofNat n)).toNat := by
  have h := List.all_eq_true.mp tickSqrtRatio_valid_table n (List.mem_range.mpr (by omega))
  exact of_decide_eq_true h

end Benchmarks.UniswapV3.Pool
