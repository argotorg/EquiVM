import Benchmarks.UniswapV4PoolManager.NextAmount1Words
import Benchmarks.UniswapV4PoolManager.FullMathRoundSource
import Benchmarks.UniswapV4PoolManager.DivRoundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount1ShiftExpr : Expr := .binary (.shl (.uint ⟨256, by decide⟩)) (.var "amount") (.intLit 96)
def nextAmount1QuotientStmt (add : Bool) : Stmt :=
  .ite (.binary .le (.var "amount") (.intLit (2^160-1)))
    (if add then [.assign .localVar {base := "quotient"} (.binary .div nextAmount1ShiftExpr (.var "liquidity"))]
     else [.internalCall "UnsafeMath_divRoundingUp" [nextAmount1ShiftExpr, .var "liquidity"] "product",
       .assign .localVar {base := "quotient"} (.var "product")])
    [.internalCall (if add then "FullMath_mulDiv" else "FullMath_mulDivRoundingUp")
       [.var "amount", .intLit 79228162514264337593543950336, .var "liquidity"] "product",
     .assign .localVar {base := "quotient"} (.var "product")]

def nextAmount1QuotientFrame (f : Frame) (liquidity amount : UInt256) (add : Bool) : Frame :=
  {f with locals :=
    ((if amount.toNat < 2^160 ∧ add = true then f.locals
     else f.locals.insert "product" (.int (Int.ofNat (nextAmount1Quotient liquidity amount add).toNat))).insert
       "quotient" (.int (Int.ofNat (nextAmount1Quotient liquidity amount add).toNat)))}

theorem nextAmount1QuotientFrame_get (f : Frame) (liquidity amount : UInt256) (add : Bool) (name : Ident)
    (hq : ("quotient" == name) = false) (hp : ("product" == name) = false) :
    (nextAmount1QuotientFrame f liquidity amount add).locals.get? name = f.locals.get? name := by
  simp only [nextAmount1QuotientFrame, store_get_ne _ _ hq]
  split
  · rfl
  · exact store_get_ne _ _ hp

theorem nextAmount1QuotientSource {f : Frame} {evm : EVM.State} {liquidity amount : UInt256} {old : Value}
    (add : Bool) (hf : f.contract = contract) (hn : liquidity ≠ ⟨0⟩)
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hq : f.locals.get? "quotient" = some old) :
    ExecStmt config f evm (nextAmount1QuotientStmt add)
      (if nextAmount1QuotientFits liquidity amount add then
        .ok (nextAmount1QuotientFrame f liquidity amount add) evm else .reverted) := by
  have hguard : evalExpr? config f evm (.binary .le (.var "amount") (.intLit (2^160-1))) =
      .ok (.bool (decide (amount.toNat < 2^160))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue ha]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
    have heq : (Int.ofNat amount.toNat ≤ (2^160-1 : Int)) ↔ amount.toNat < 2^160 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [heq]
  have hshift := evalWordShl (n := 96) (b := .intLit 96) (by decide)
    (evalLocalValue (cfg := config) (f := f) (evm := evm) ha)
    (by simp only [evalExpr?, pure]; rfl)
  have hproduct (w : UInt256) : ExecStmt config (wordLocal f "product" w) evm
      (.assign .localVar {base := "quotient"} (.var "product"))
      (.ok (wordLocal (wordLocal f "product" w) "quotient" w) evm) :=
    ExecStmt.assign wordLocal_eval (assignLocalValue
      ((store_get_ne _ _ (by decide : ("product" == "quotient") = false)).trans hq))
  by_cases hs : amount.toNat < 2^160
  · cases add with
    | false =>
      simp only [nextAmount1QuotientFits, hs, if_true, nextAmount1QuotientStmt,
        Bool.false_eq_true, if_false]
      have hc := divRoundCall hf hshift (evalLocalValue hl) "product"
      convert ExecStmt.iteTrue (by simpa only [decide_eq_true hs] using hguard)
        (ExecBlock.consNormal hc (execBlock_singleton (hproduct _))) using 1
      simp only [nextAmount1QuotientFrame, nextAmount1Quotient, hs, if_true,
        Bool.false_eq_true, and_false, if_false, wordLocal]
    | true =>
      simp only [nextAmount1QuotientFits, hs, if_true, nextAmount1QuotientStmt]
      convert ExecStmt.iteTrue (by simpa only [decide_eq_true hs] using hguard)
        (execBlock_singleton (ExecStmt.assign (evalWordDiv hshift (evalLocalValue hl) hn)
          (assignLocalValue hq))) using 1
      simp only [nextAmount1QuotientFrame, nextAmount1Quotient, hs, if_true, and_self]
  · cases add with
    | false =>
      simp only [nextAmount1QuotientFits, hs, if_false, nextAmount1QuotientStmt, Bool.false_eq_true]
      have hc := fullMathRoundCall (evm := evm) (b := fullMathQ96) (eb := .intLit 79228162514264337593543950336) hf (evalLocalValue ha)
        (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hl) "product"
      by_cases hfit : fullMathRoundFits amount fullMathQ96 liquidity
      · rw [if_pos hfit] at hc ⊢
        convert ExecStmt.iteFalse (by simpa only [decide_eq_false hs] using hguard)
          (ExecBlock.consNormal hc (execBlock_singleton (hproduct _))) using 1
        simp only [nextAmount1QuotientFrame, nextAmount1Quotient, hs, if_false,
          Bool.false_eq_true, false_and, wordLocal]
      · rw [if_neg hfit] at hc ⊢
        exact ExecStmt.iteFalse (by simpa only [decide_eq_false hs] using hguard) (ExecBlock.consRevert hc)
    | true =>
      simp only [nextAmount1QuotientFits, hs, if_false, nextAmount1QuotientStmt, if_true]
      have hc := fullMathCall (evm := evm) (b := fullMathQ96) (eb := .intLit 79228162514264337593543950336) hf (evalLocalValue ha)
        (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hl) "product"
      by_cases hfit : fullMathFits amount fullMathQ96 liquidity
      · rw [if_pos hfit] at hc ⊢
        convert ExecStmt.iteFalse (by simpa only [decide_eq_false hs] using hguard)
          (ExecBlock.consNormal hc (execBlock_singleton (hproduct _))) using 1
        simp only [nextAmount1QuotientFrame, nextAmount1Quotient, hs, if_false,
          if_true, false_and, wordLocal]
      · rw [if_neg hfit] at hc ⊢
        exact ExecStmt.iteFalse (by simpa only [decide_eq_false hs] using hguard) (ExecBlock.consRevert hc)

end Benchmarks.UniswapV4PoolManager
