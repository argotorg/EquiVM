import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.evalExpr_wrappingSub256_word_ok to arbitrary expressions and frames.
theorem evalWordSub {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .sub a b) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
  have he : evalExpr? cfg f evm (.binary .sub a b) =
      .ok (.int (Int.ofNat x.toNat - Int.ofNat y.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) he
  have hn : normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat x.toNat - Int.ofNat y.toNat) =
      Int.ofNat (UInt256.sub x y).toNat := by
    change (Int.ofNat x.toNat - Int.ofNat y.toNat) % (2^256 : Int) = _
    rw [← wordOfIntResidue, wordOfInt_sub_natCasts]
  simpa only [hn] using hc

end Benchmarks.UniswapV4PoolManager
