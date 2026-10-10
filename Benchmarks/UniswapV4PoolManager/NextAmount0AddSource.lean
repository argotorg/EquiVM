import Benchmarks.UniswapV4PoolManager.NextAmount0SubSource
import Benchmarks.UniswapV4PoolManager.NextAmount0FallbackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount0AddAfterProductStmts : List Stmt :=
  [.ite nextAmount0ProductGuardExpr
    [.letDecl "denominator" (some abiUInt256)
       (.cast (.binary .add (.var "numerator1") (.var "product")) (.elem (.int (.uint ⟨256, by decide⟩)))),
     .ite (.binary .ge (.var "denominator") (.var "numerator1")) (nextAmount0RoundStmts false) []] []] ++
  nextAmount0FallbackStmts
def nextAmount0AddStmts : List Stmt :=
  .letDecl "product" (some abiUInt256) nextAmount0ProductExpr :: nextAmount0AddAfterProductStmts

theorem nextAmount0AddAfterProductSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (hf : f.contract = contract) (hprice : price ≠ ⟨0⟩) (hamount : amount ≠ ⟨0⟩)
    (hn : f.locals.get? "numerator1" = some (.int (Int.ofNat (amount0Numerator1 liquidity).toNat)))
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hp : f.locals.get? "product" = some (.int (Int.ofNat (nextAmount0Product price amount).toNat))) :
    ∃ f', ExecBlock config f evm nextAmount0AddAfterProductStmts
      (if nextAmount0CoreFits price liquidity amount true then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0CoreWord price liquidity amount true).toNat)])
       else .reverted) := by
  let p := nextAmount0Product price amount
  let n := amount0Numerator1 liquidity
  have hg := evalEqWords (evalWordDiv (evalLocalValue (cfg := config) (f := f) (evm := evm) hp)
    (evalLocalValue ha) hamount) (evalLocalValue hs)
  by_cases hprod : UInt256.div p amount = price
  · rw [decide_eq_true hprod] at hg
    let f1 := wordLocal f "denominator" (n+p)
    have hd : ExecStmt config f evm (.letDecl "denominator" (some abiUInt256)
        (.cast (.binary .add (.var "numerator1") (.var "product")) (.elem (.int (.uint ⟨256, by decide⟩)))))
        (.ok f1 evm) := ExecStmt.letDecl (evalWordAdd (evalLocalValue hn) (evalLocalValue hp))
    have hn1 : f1.locals.get? "numerator1" = some (.int (Int.ofNat n.toNat)) :=
      (store_get_ne _ _ (by decide : ("denominator" == "numerator1") = false)).trans hn
    have hs1 : f1.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)) :=
      (store_get_ne _ _ (by decide : ("denominator" == "sqrtPX96") = false)).trans hs
    have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("denominator" == "amount") = false)).trans ha
    have hd1 : f1.locals.get? "denominator" = some (.int (Int.ofNat (n+p).toNat)) := store_get_self _ _ _
    have hbound : evalExpr? config f1 evm (.binary .ge (.var "denominator") (.var "numerator1")) =
        .ok (.bool (decide (n.toNat ≤ (n+p).toNat))) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hd1, evalLocalValue hn1]
      simp only [bind, EvalResult.bind, evalBinaryOp?]
      have he : (Int.ofNat (n+p).toNat ≥ Int.ofNat n.toNat) ↔ n.toNat ≤ (n+p).toNat := by
        simp only [Int.ofNat_eq_natCast]
        omega
      simp only [he]
    by_cases hb : n.toNat ≤ (n+p).toNat
    · have hdir : nextAmount0Direct price liquidity amount := ⟨hprod, hb⟩
      rw [decide_eq_true hb] at hbound
      obtain ⟨f2, hr⟩ := nextAmount0RoundSource (f := f1) (evm := evm) false hf hn1 hs1 hd1
      simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hdir]
      by_cases hfit : nextAmount0RoundFits n price (n+p) false
      · simp only [n, p] at hfit
        rw [if_pos hfit] at hr
        simp only [if_pos hfit]
        exact ⟨f2, ExecBlock.consReturn (ExecStmt.iteTrue hg
          (ExecBlock.consNormal hd (ExecBlock.consReturn (ExecStmt.iteTrue hbound hr))))⟩
      · simp only [n, p] at hfit
        rw [if_neg hfit] at hr
        simp only [if_neg hfit]
        exact ⟨f2, ExecBlock.consRevert (ExecStmt.iteTrue hg
          (ExecBlock.consNormal hd (ExecBlock.consRevert (ExecStmt.iteTrue hbound hr))))⟩
    · have hdir : ¬nextAmount0Direct price liquidity amount := fun hh => hb hh.2
      rw [decide_eq_false hb] at hbound
      obtain ⟨f2, hr⟩ := nextAmount0FallbackSource (f := f1) (evm := evm) hf hprice hn1 hs1 ha1
      simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hdir, if_false]
      exact ⟨f2, ExecBlock.consNormal (ExecStmt.iteTrue hg
        (ExecBlock.consNormal hd (execBlock_singleton (ExecStmt.iteFalse hbound ExecBlock.nil)))) hr⟩
  · have hdir : ¬nextAmount0Direct price liquidity amount := fun hh => hprod hh.1
    rw [decide_eq_false hprod] at hg
    obtain ⟨f1, hr⟩ := nextAmount0FallbackSource (f := f) (evm := evm) hf hprice hn hs ha
    simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hdir, if_false]
    exact ⟨f1, ExecBlock.consNormal (ExecStmt.iteFalse hg ExecBlock.nil) hr⟩

theorem nextAmount0AddSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (hf : f.contract = contract) (hprice : price ≠ ⟨0⟩) (hamount : amount ≠ ⟨0⟩)
    (hn : f.locals.get? "numerator1" = some (.int (Int.ofNat (amount0Numerator1 liquidity).toNat)))
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ∃ f', ExecBlock config f evm nextAmount0AddStmts
      (if nextAmount0CoreFits price liquidity amount true then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0CoreWord price liquidity amount true).toNat)])
       else .reverted) := by
  let f1 := wordLocal f "product" (nextAmount0Product price amount)
  have hp : ExecStmt config f evm (.letDecl "product" (some abiUInt256) nextAmount0ProductExpr) (.ok f1 evm) :=
    ExecStmt.letDecl (evalWordMul (evalLocalValue ha) (evalLocalValue hs))
  obtain ⟨f2, hr⟩ := nextAmount0AddAfterProductSource (f := f1) (evm := evm) hf hprice hamount
    ((store_get_ne _ _ (by decide : ("product" == "numerator1") = false)).trans hn)
    ((store_get_ne _ _ (by decide : ("product" == "sqrtPX96") = false)).trans hs)
    ((store_get_ne _ _ (by decide : ("product" == "amount") = false)).trans ha) (store_get_self _ _ _)
  exact ⟨f2, ExecBlock.consNormal hp hr⟩

end Benchmarks.UniswapV4PoolManager
