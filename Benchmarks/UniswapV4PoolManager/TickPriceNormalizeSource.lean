import Benchmarks.UniswapV4PoolManager.TickPriceWords
import Benchmarks.UniswapV4PoolManager.WordWrappingSource
import Benchmarks.UniswapV4PoolManager.WordShiftSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceNormalizeSource {f : Frame} {evm : EVM.State} {price msb : UInt256} {oldR : Value}
    (hm : msb.toNat < 256)
    (hp : f.locals.get? "price" = some (.int (Int.ofNat price.toNat)))
    (hb : f.locals.get? "msb" = some (.int (Int.ofNat msb.toNat)))
    (hr : f.locals.get? "r" = some oldR) :
    ExecStmt config f evm tickPriceFunction.body[5]!
      (.ok {f with locals := f.locals.insert "r" (.int (Int.ofNat (tickPriceNormalize price msb).toNat))} evm) := by
  have hcond : evalExpr? config f evm (.binary .ge (.var "msb") (.intLit 128)) =
      .ok (.bool (decide (128 ≤ msb.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hb]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    simp only [show ((msb.toNat : Int) ≥ 128) ↔ 128 ≤ msb.toNat by omega]
  by_cases hh : 128 ≤ msb.toNat
  · have hsub := evalWordSub (evalLocalValue (cfg := config) (evm := evm) hb)
      (show evalExpr? config f evm (.intLit 127) = .ok (.int (Int.ofNat (UInt256.ofNat 127).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    have he := evalWordShrWord (evalLocalValue hp) hsub
    simp only [tickPriceNormalize, if_pos hh]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hh] using hcond)
      (execBlock_singleton (ExecStmt.assign he (assignLocalValue hr)))
  · have hsub := evalWordSub
      (show evalExpr? config f evm (.intLit 127) = .ok (.int (Int.ofNat (UInt256.ofNat 127).toNat)) by
        simp only [evalExpr?, pure]; rfl)
      (evalLocalValue (cfg := config) (evm := evm) hb)
    have hshift : (UInt256.sub (UInt256.ofNat 127) msb).toNat < 256 := by
      rw [usub_toNat (by change msb.toNat ≤ 127; omega)]
      change 127-msb.toNat < 256
      omega
    have he := evalWordShl hshift (evalLocalValue hp) hsub
    rw [u256_ofNat_toNat] at he
    simp only [tickPriceNormalize, if_neg hh]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hh] using hcond)
      (execBlock_singleton (ExecStmt.assign he (assignLocalValue hr)))

theorem tickPriceLogStartSource {f : Frame} {evm : EVM.State} {msb : UInt256}
    (hb : f.locals.get? "msb" = some (.int (Int.ofNat msb.toNat))) :
    ExecStmt config f evm tickPriceFunction.body[6]!
      (.ok {f with locals := f.locals.insert "log_2" (.int (EVM.signed (tickPriceLogStart msb)))} evm) := by
  have hcast := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
    (evalLocalValue (cfg := config) (evm := evm) hb)
  have hn : normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat msb.toNat) = EVM.signed msb :=
    normalizeInt_sint256_word msb
  rw [hn] at hcast
  have hsub := evalSignedWordSub hcast
    (show evalExpr? config f evm (.intLit 128) = .ok (.int (EVM.signed (UInt256.ofNat 128))) by
      simp only [evalExpr?, pure]; rfl)
  exact ExecStmt.letDecl (evalSignedWordShl (n := 64) (b := .intLit 64) (by decide) hsub
    (by simp only [evalExpr?, pure]; rfl))

end Benchmarks.UniswapV4PoolManager
