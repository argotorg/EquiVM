import Benchmarks.UniswapV4PoolManager.TickSqrtWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

/-- Concrete range audit of the pinned TickMath constants over every accepted absolute tick. -/
private theorem tickSqrtRangeCheck : (List.range 887273).all (fun n =>
    let p := tickSqrtRatio (UInt256.ofNat n)
    decide (0 < p.toNat ∧ (tickSqrtRound p).toNat < 2^160 ∧
      (tickSqrtRound (UInt256.div (UInt256.ofNat (2^256-1)) p)).toNat < 2^160)) = true := by
  native_decide

private theorem tickSqrtRangeAudit (n : Fin 887273) :
    let p := tickSqrtRatio (UInt256.ofNat n.val)
    0 < p.toNat ∧ (tickSqrtRound p).toNat < 2^160 ∧
      (tickSqrtRound (UInt256.div (UInt256.ofNat (2^256-1)) p)).toNat < 2^160 :=
  of_decide_eq_true (List.all_eq_true.mp tickSqrtRangeCheck n.val (List.mem_range.mpr n.isLt))

theorem tickSqrtRatio_pos {n : Nat} (hn : n ≤ 887272) :
    0 < (tickSqrtRatio (UInt256.ofNat n)).toNat :=
  (tickSqrtRangeAudit ⟨n, by omega⟩).1

theorem tickSqrtPrice_lt_160 {tick : Int} (ht : tick.natAbs ≤ 887272) :
    (tickSqrtPrice tick).toNat < 2^160 := by
  have h := (tickSqrtRangeAudit ⟨tick.natAbs, by omega⟩).2
  unfold tickSqrtPrice
  split
  · exact h.2
  · exact h.1

end Benchmarks.UniswapV4PoolManager
