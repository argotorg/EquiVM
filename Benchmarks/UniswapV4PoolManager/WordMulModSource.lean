import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: MULMOD takes the remainder of the full mathematical product.
theorem wordMulMod_toNat (a b c : UInt256) (hc : c ≠ ⟨0⟩) :
    (UInt256.mulMod a b c).toNat = (a.toNat*b.toNat)%c.toNat := by
  have hn : c.toNat ≠ 0 := fun h => hc (uint256_toNat_eq_zero h)
  have he : UInt256.eq0 c = false := beq_eq_false_iff_ne.mpr hc
  simp only [UInt256.mulMod, he, Bool.false_eq_true, if_false]
  exact UInt256.toNat_ofNat_of_lt (lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hn)) c.val.isLt)

-- LIBRARY CANDIDATE: an unbounded source multiplication followed by modulo agrees with MULMOD.
theorem evalWordMulMod {cfg : Config} {f : Frame} {evm : EVM.State} {ea eb ec : Expr} {a b c : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hc : evalExpr? cfg f evm ec = .ok (.int (Int.ofNat c.toNat))) (hn : c ≠ ⟨0⟩) :
    evalExpr? cfg f evm (.binary .mod (.binary .mul ea eb) ec) =
      .ok (.int (Int.ofNat (UInt256.mulMod a b c).toNat)) := by
  have he : evalExpr? cfg f evm (.binary .mul ea eb) = .ok (.int (Int.ofNat a.toNat * Int.ofNat b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
    rfl
  have hz : c.toNat ≠ 0 := fun h => hn (uint256_toNat_eq_zero h)
  rw [evalExpr_binary_nonshort (by decide) (by decide), he, hc]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Int.natCast_eq_zero, hz, if_false, wordMulMod_toNat a b c hn, Int.natCast_mod, Int.natCast_mul]

end Benchmarks.UniswapV4PoolManager
