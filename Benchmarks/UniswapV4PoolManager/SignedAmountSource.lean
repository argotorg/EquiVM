import Benchmarks.UniswapV4PoolManager.LiquidityMagnitude
import Benchmarks.UniswapV4PoolManager.CheckedAmountPath

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def signedAmountRound (delta : Int) : Bool := if delta < 0 then false else true
def signedAmountBranch (name : Ident) (liquidity : Expr) (roundUp : Bool) : List Stmt :=
  .internalCall name [.var "sqrtPriceAX96", .var "sqrtPriceBX96", liquidity, .boolLit roundUp] "amount" ::
    checkedAmountReturnBlock roundUp
def signedAmountBodyStmts (name : Ident) : List Stmt :=
  [.ite (.binary .lt (.var "liquidity") (.intLit 0))
    (signedAmountBranch name (.cast (.cast (.binary .sub (.intLit 0) (.var "liquidity"))
      (.elem (.int (.sint ⟨128, by decide⟩)))) (.elem (.int (.uint ⟨128, by decide⟩)))) false)
    (signedAmountBranch name (.cast (.var "liquidity") (.elem (.int (.uint ⟨128, by decide⟩)))) true)]

theorem signedAmountBody {f : Frame} {evm : EVM.State} {delta : Int} {name : Ident}
    {fits : Bool → Prop} [∀ b, Decidable (fits b)] {word : Bool → UInt256}
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hed : f.locals.get? "liquidity" = some (.int delta))
    (hpath : ∀ el roundUp, evalExpr? config f evm el = .ok (.int (Int.ofNat (liquidityMagnitude delta).toNat)) →
      ∃ f', ExecBlock config f evm (signedAmountBranch name el roundUp)
        (if fits roundUp ∧ (word roundUp).toNat < 2^255 then
          .returned f' evm (some [.int (EVM.signed (checkedAmountReturnWord (word roundUp) roundUp))]) else .reverted)) :
    ∃ f', ExecFuncBody config f evm (signedAmountBodyStmts name)
      (if fits (signedAmountRound delta) ∧ (word (signedAmountRound delta)).toNat < 2^255 then
        .returned f' evm (some [.int (EVM.signed (checkedAmountReturnWord (word (signedAmountRound delta)) (signedAmountRound delta)))])
       else .reverted) := by
  have hguard : evalExpr? config f evm (.binary .lt (.var "liquidity") (.intLit 0)) =
      .ok (.bool (decide (delta < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hed]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hz : delta < 0
  · have hc := evalLiquidityMagnitudeNegative hdlo hdhi hz (evalLocalValue (cfg := config) (f := f) (evm := evm) hed)
    obtain ⟨f', hp⟩ := hpath _ false hc
    simp only [signedAmountRound, if_pos hz]
    by_cases hfit : fits false ∧ (word false).toNat < 2^255
    · rw [if_pos hfit] at hp
      simp only [if_pos hfit]
      exact ⟨f', ExecFuncBody.execBlockRet (ExecBlock.consReturn
        (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hguard) hp))⟩
    · rw [if_neg hfit] at hp
      simp only [if_neg hfit]
      exact ⟨f', ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hguard) hp))⟩
  · have hc := evalLiquidityMagnitudePositive hdlo hdhi hz (evalLocalValue (cfg := config) (f := f) (evm := evm) hed)
    obtain ⟨f', hp⟩ := hpath _ true hc
    simp only [signedAmountRound, if_neg hz]
    by_cases hfit : fits true ∧ (word true).toNat < 2^255
    · rw [if_pos hfit] at hp
      simp only [if_pos hfit]
      exact ⟨f', ExecFuncBody.execBlockRet (ExecBlock.consReturn
        (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hguard) hp))⟩
    · rw [if_neg hfit] at hp
      simp only [if_neg hfit]
      exact ⟨f', ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hguard) hp))⟩

end Benchmarks.UniswapV4PoolManager
