import Benchmarks.UniswapV4PoolManager.NextAmount0RoundSource
import Benchmarks.UniswapV4PoolManager.WordWrappingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount0ProductExpr : Expr :=
  .cast (.binary .mul (.var "amount") (.var "sqrtPX96")) (.elem (.int (.uint ⟨256, by decide⟩)))
def nextAmount0ProductGuardExpr : Expr :=
  .binary .eq (.binary .div (.var "product") (.var "amount")) (.var "sqrtPX96")
def nextAmount0SubStmts : List Stmt :=
  [.letDecl "product" (some abiUInt256) nextAmount0ProductExpr,
   .require (.binary .and nextAmount0ProductGuardExpr (.binary .gt (.var "numerator1") (.var "product"))),
   .letDecl "denominator" (some abiUInt256)
     (.cast (.binary .sub (.var "numerator1") (.var "product")) (.elem (.int (.uint ⟨256, by decide⟩))))] ++
  nextAmount0RoundStmts true

theorem nextAmount0SubSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (hf : f.contract = contract) (ha0 : amount ≠ ⟨0⟩)
    (hn : f.locals.get? "numerator1" = some (.int (Int.ofNat (amount0Numerator1 liquidity).toNat)))
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ∃ f', ExecBlock config f evm nextAmount0SubStmts
      (if nextAmount0CoreFits price liquidity amount false then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0CoreWord price liquidity amount false).toNat)])
       else .reverted) := by
  let p := nextAmount0Product price amount
  let n := amount0Numerator1 liquidity
  let f1 := wordLocal f "product" p
  have hprod : ExecStmt config f evm (.letDecl "product" (some abiUInt256) nextAmount0ProductExpr) (.ok f1 evm) :=
    ExecStmt.letDecl (evalWordMul (evalLocalValue ha) (evalLocalValue hs))
  have hn1 : f1.locals.get? "numerator1" = some (.int (Int.ofNat n.toNat)) :=
    (store_get_ne _ _ (by decide : ("product" == "numerator1") = false)).trans hn
  have hs1 : f1.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)) :=
    (store_get_ne _ _ (by decide : ("product" == "sqrtPX96") = false)).trans hs
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("product" == "amount") = false)).trans ha
  have hp1 : f1.locals.get? "product" = some (.int (Int.ofNat p.toNat)) := store_get_self _ _ _
  have heq := evalEqWords (evalWordDiv (evalLocalValue (cfg := config) (f := f1) (evm := evm) hp1)
    (evalLocalValue ha1) ha0) (evalLocalValue hs1)
  have hgt := evalWordGt (evalLocalValue (cfg := config) (f := f1) (evm := evm) hn1) (evalLocalValue hp1)
  have hg := evalAndBool heq hgt
  change evalExpr? config f1 evm (.binary .and nextAmount0ProductGuardExpr
    (.binary .gt (.var "numerator1") (.var "product"))) =
      .ok (.bool (decide (UInt256.div p amount = price) && decide (p.toNat < n.toNat))) at hg
  rw [← Bool.decide_and] at hg
  by_cases hguard : nextAmount0SubGuard price liquidity amount
  · have hg' := hg
    have hguard' : UInt256.div p amount = price ∧ p.toNat < n.toNat := hguard
    rw [decide_eq_true hguard'] at hg'
    let f2 := wordLocal f1 "denominator" (UInt256.sub n p)
    have hd : ExecStmt config f1 evm
        (.letDecl "denominator" (some abiUInt256)
          (.cast (.binary .sub (.var "numerator1") (.var "product")) (.elem (.int (.uint ⟨256, by decide⟩)))))
        (.ok f2 evm) := ExecStmt.letDecl (evalWordSub (evalLocalValue hn1) (evalLocalValue hp1))
    obtain ⟨f3, hr⟩ := nextAmount0RoundSource (f := f2) (evm := evm) true hf
      ((store_get_ne _ _ (by decide : ("denominator" == "numerator1") = false)).trans hn1)
      ((store_get_ne _ _ (by decide : ("denominator" == "sqrtPX96") = false)).trans hs1)
      (store_get_self _ _ _)
    simp only [nextAmount0CoreFits, nextAmount0CoreWord, Bool.false_eq_true, if_false, hguard, true_and]
    exact ⟨f3, ExecBlock.consNormal hprod (ExecBlock.consNormal (ExecStmt.requireTrue hg')
      (ExecBlock.consNormal hd hr))⟩
  · have hg' := hg
    have hguard' : ¬(UInt256.div p amount = price ∧ p.toNat < n.toNat) := hguard
    rw [decide_eq_false hguard'] at hg'
    simp only [nextAmount0CoreFits, Bool.false_eq_true, if_false, hguard, false_and]
    exact ⟨f1, ExecBlock.consNormal hprod (ExecBlock.consRevert (ExecStmt.requireFalse hg'))⟩

end Benchmarks.UniswapV4PoolManager
