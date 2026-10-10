import Benchmarks.UniswapV3.Pool.TickLogMsbWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the accumulated count in a binary scan is bounded by its steps.
theorem tickLogMsbStep_count_le (state : Nat × UInt256) (bits : Nat) :
    (tickLogMsbStep state bits).1 ≤ state.1 + bits := by
  unfold tickLogMsbStep
  split <;> omega

theorem tickLogMsbFold_count_le (state : Nat × UInt256) (bits : List Nat) :
    (bits.foldl tickLogMsbStep state).1 ≤ state.1 + bits.sum := by
  induction bits generalizing state with
  | nil => simp only [List.foldl_nil, List.sum_nil, Nat.add_zero, le_refl]
  | cons b bs ih =>
    have hs := tickLogMsbStep_count_le state b
    have ht := ih (tickLogMsbStep state b)
    simp only [List.foldl_cons, List.sum_cons]
    omega

theorem tickLogMsbFold_eq (x : UInt256) :
    tickLogMsbBits.foldl tickLogMsbStep (0, x) =
      (tickLogMsbCount x, tickLogMsbScan x 8) := by
  simp only [tickLogMsbBits, List.foldl_cons, List.foldl_nil, tickLogMsbStep_eq, Nat.zero_add]
  rfl

end Benchmarks.UniswapV3.Pool
