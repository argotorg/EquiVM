import Benchmarks.UniswapV3.Pool.NextPriceModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextPriceZeroFrame (imms : Store) (input : Bool) (a : NextPriceArgs) : Frame :=
  {nextPriceFrame imms input a with
    locals := (nextPriceLocals input a).insert "sqrtQX96" (.int 0)}

def nextPriceReadyFrame (imms : Store) (input : Bool) (a : NextPriceArgs) : Frame :=
  {nextPriceZeroFrame imms input a with
    locals := (nextPriceZeroFrame imms input a).locals.insert "__cond2" (.int 0)}

macro "next_price_prefix_get" : tactic =>
  `(tactic| simp only [nextPriceReadyFrame, nextPriceZeroFrame, nextPriceFrame,
    nextPriceLocals, nextPriceAmountName, Bool.false_eq_true, if_false, if_true,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert])

theorem nextPriceZeroSource (imms : Store) (evm : EVM.State) (input : Bool) (a : NextPriceArgs) :
    ExecStmt config (nextPriceFrame imms input a) evm (nextPriceFunction input).body[0]!
      (.ok (nextPriceZeroFrame imms input a) evm) := by
  cases input <;> exact ExecStmt.letDecl (by simp only [evalExpr?, pure])

theorem evalNextPricePriceGuard (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) :
    evalExpr? config (nextPriceZeroFrame imms input a) evm
      (.binary .gt (.var "sqrtPX96") (.intLit 0)) =
      .ok (.bool (decide (0 < a.price.toNat))) := by
  apply evalExpr_word_gt (b := ⟨0⟩)
  · apply evalExpr_var_get
    cases input <;> next_price_prefix_get <;> rfl
  · simp only [evalExpr?, pure]; rfl

theorem evalNextPriceLiquidityGuard (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) :
    evalExpr? config (nextPriceZeroFrame imms input a) evm
      (.binary .gt (.var "liquidity") (.intLit 0)) =
      .ok (.bool (decide (0 < a.liquidity.toNat))) := by
  apply evalExpr_word_gt (b := ⟨0⟩)
  · apply evalExpr_var_get
    cases input <;> next_price_prefix_get <;> rfl
  · simp only [evalExpr?, pure]; rfl

theorem nextPricePrefixSource (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (hg : nextPriceGuard a) :
    ExecBlock config (nextPriceFrame imms input a) evm ((nextPriceFunction input).body.take 4)
      (.ok (nextPriceReadyFrame imms input a) evm) := by
  have hz := nextPriceZeroSource imms evm input a
  have hp := evalNextPricePriceGuard imms evm input a
  have hl := evalNextPriceLiquidityGuard imms evm input a
  cases input
  all_goals
    exact ExecBlock.consNormal hz
      (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hg.1, decide_true] using hp))
        (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hg.2, decide_true] using hl))
          (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)))

theorem nextPriceGuardReverts (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (hg : ¬nextPriceGuard a) :
    ExecFuncBody config (nextPriceFrame imms input a) evm (nextPriceFunction input).body
      .reverted := by
  have hz := nextPriceZeroSource imms evm input a
  have hp := evalNextPricePriceGuard imms evm input a
  have hl := evalNextPriceLiquidityGuard imms evm input a
  apply ExecFuncBody.execBlockRevert
  by_cases hprice : 0 < a.price.toNat
  · have hliq : ¬0 < a.liquidity.toNat := fun h ↦ hg ⟨hprice, h⟩
    cases input
    all_goals
      exact ExecBlock.consNormal hz
        (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hprice, decide_true] using hp))
          (ExecBlock.consRevert (ExecStmt.requireFalse
            (by simpa only [hliq, decide_false] using hl))))
  · cases input
    all_goals
      exact ExecBlock.consNormal hz (ExecBlock.consRevert
        (ExecStmt.requireFalse (by simpa only [hprice, decide_false] using hp)))

theorem nextPriceReadyGet (imms : Store) (input : Bool) (a : NextPriceArgs) :
    (nextPriceReadyFrame imms input a).locals.get? "sqrtPX96" =
        some (.int (Int.ofNat a.price.toNat)) ∧
      (nextPriceReadyFrame imms input a).locals.get? "liquidity" =
        some (.int (Int.ofNat a.liquidity.toNat)) ∧
      (nextPriceReadyFrame imms input a).locals.get? (nextPriceAmountName input) =
        some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextPriceReadyFrame imms input a).locals.get? "zeroForOne" = some (.bool a.zeroForOne) ∧
      (nextPriceReadyFrame imms input a).locals.get? "__cond2" = some (.int 0) := by
  cases input <;> next_price_prefix_get <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Benchmarks.UniswapV3.Pool
