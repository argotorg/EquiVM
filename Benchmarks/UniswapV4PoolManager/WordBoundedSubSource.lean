import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: subtraction followed by a narrow unsigned cast, with no underflow or truncation.
theorem evalBoundedWordSub {cfg : Config} {f : Frame} {evm : EVM.State} {ea eb : Expr} {a b : UInt256}
    (bits : BitWidth) (ho : b.toNat ≤ a.toNat) (hb : a.toNat < 2^bits.val)
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (he : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .sub ea eb) (.elem (.int (.uint bits)))) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  have hsub : evalExpr? cfg f evm (.binary .sub ea eb) =
      .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, he]
    rfl
  have hn : Int.ofNat a.toNat - Int.ofNat b.toNat = Int.ofNat (a.toNat-b.toNat) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_sub ho]
  have hc := evalExpr_cast_int (intType := .uint bits) hsub
  have hnrm := normalizeInt_uint_eq_self bits (Int.ofNat (a.toNat-b.toNat))
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (show a.toNat-b.toNat < 2^bits.val by omega))
  simpa only [hn, hnrm, usub_toNat ho] using hc

end Benchmarks.UniswapV4PoolManager
