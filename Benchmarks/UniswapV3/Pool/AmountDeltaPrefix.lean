import Benchmarks.UniswapV3.Pool.AmountDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def amountDeltaOutputName (second : Bool) : Ident := if second then "amount1" else "amount0"

def amountDeltaZeroFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaLocals a).insert (amountDeltaOutputName second) (.int 0)
  {amountDeltaFrame imms a with locals := locals}

def amountDeltaSwapBFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaZeroFrame imms second a).locals.insert "__t0" (.int (Int.ofNat a.sqrtB.toNat))
  {amountDeltaZeroFrame imms second a with locals := locals}

def amountDeltaSwapAFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaSwapBFrame imms second a).locals.insert "__t1" (.int (Int.ofNat a.sqrtA.toNat))
  {amountDeltaSwapBFrame imms second a with locals := locals}

def amountDeltaSwapLowerFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaSwapAFrame imms second a).locals.insert "sqrtRatioAX96"
    (.int (Int.ofNat a.sqrtB.toNat))
  {amountDeltaSwapAFrame imms second a with locals := locals}

def amountDeltaSwapReadyFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  let locals := (amountDeltaSwapLowerFrame imms second a).locals.insert "sqrtRatioBX96"
    (.int (Int.ofNat a.sqrtA.toNat))
  {amountDeltaSwapLowerFrame imms second a with locals := locals}

def amountDeltaSortedFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  if a.sqrtB.toNat < a.sqrtA.toNat then amountDeltaSwapReadyFrame imms second a
  else amountDeltaZeroFrame imms second a

macro "amount_delta_prefix_get" : tactic =>
  `(tactic| (simp only [amountDeltaSwapReadyFrame, amountDeltaSwapLowerFrame, amountDeltaSwapAFrame,
    amountDeltaSwapBFrame, amountDeltaZeroFrame, amountDeltaFrame, amountDeltaLocals,
    amountDeltaOutputName]; split_ifs <;>
      (simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)))

def amountDeltaSwapStmt : Stmt :=
  .ite (.binary .gt (.var "sqrtRatioAX96") (.var "sqrtRatioBX96"))
    [.letDecl "__t0" none (.var "sqrtRatioBX96"), .letDecl "__t1" none (.var "sqrtRatioAX96"),
      .assign .localVar ⟨"sqrtRatioAX96", []⟩ (.var "__t0"),
      .assign .localVar ⟨"sqrtRatioBX96", []⟩ (.var "__t1")] []

theorem amountDeltaPrefixBody (second : Bool) : (amountDeltaFunction second).body.take 2 =
    [.letDecl (amountDeltaOutputName second) (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.intLit 0), amountDeltaSwapStmt] := by cases second <;> rfl

theorem amountDeltaSwapSource (imms : Store) (evm : EVM.State) (second : Bool) (a : AmountDeltaArgs) :
    ExecStmt config (amountDeltaZeroFrame imms second a) evm amountDeltaSwapStmt
      (.ok (amountDeltaSortedFrame imms second a) evm) := by
  have ha : evalExpr? config (amountDeltaZeroFrame imms second a) evm (.var "sqrtRatioAX96") =
      .ok (.int (Int.ofNat a.sqrtA.toNat)) := evalExpr_var_get (by amount_delta_prefix_get)
  have hb : evalExpr? config (amountDeltaZeroFrame imms second a) evm (.var "sqrtRatioBX96") =
      .ok (.int (Int.ofNat a.sqrtB.toNat)) := evalExpr_var_get (by amount_delta_prefix_get)
  have hg := evalExpr_word_gt ha hb
  by_cases hs : a.sqrtB.toNat < a.sqrtA.toNat
  · simp only [amountDeltaSortedFrame, if_pos hs]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hs] using hg)
    refine ExecBlock.consNormal (solm' := amountDeltaSwapBFrame imms second a) (evm' := evm)
      (ExecStmt.letDecl hb) ?_
    refine ExecBlock.consNormal (solm' := amountDeltaSwapAFrame imms second a) (evm' := evm)
      (ExecStmt.letDecl (evalExpr_var_get (by amount_delta_prefix_get))) ?_
    refine ExecBlock.consNormal (solm' := amountDeltaSwapLowerFrame imms second a) (evm' := evm)
      (ExecStmt.assign (evalExpr_var_get (by amount_delta_prefix_get))
        (assignLocalVarBase_frame (by amount_delta_prefix_get))) ?_
    exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_var_get (by amount_delta_prefix_get))
      (assignLocalVarBase_frame (by amount_delta_prefix_get))) ExecBlock.nil
  · simp only [amountDeltaSortedFrame, if_neg hs]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hs] using hg) ExecBlock.nil

theorem amountDeltaPrefixSource (imms : Store) (evm : EVM.State) (second : Bool) (a : AmountDeltaArgs) :
    ExecBlock config (amountDeltaFrame imms a) evm ((amountDeltaFunction second).body.take 2)
      (.ok (amountDeltaSortedFrame imms second a) evm) := by
  rw [amountDeltaPrefixBody]
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (amountDeltaSwapSource imms evm second a) ExecBlock.nil)

theorem amountDeltaSortedGet (imms : Store) (second : Bool) (a : AmountDeltaArgs) :
    (amountDeltaSortedFrame imms second a).locals.get? "sqrtRatioAX96" =
        some (.int (Int.ofNat (amountDeltaLower a).toNat)) ∧
      (amountDeltaSortedFrame imms second a).locals.get? "sqrtRatioBX96" =
        some (.int (Int.ofNat (amountDeltaUpper a).toNat)) ∧
      (amountDeltaSortedFrame imms second a).locals.get? "liquidity" =
        some (.int (Int.ofNat a.liquidity.toNat)) ∧
      (amountDeltaSortedFrame imms second a).locals.get? "roundUp" = some (.bool a.roundUp) := by
  by_cases hs : a.sqrtB.toNat < a.sqrtA.toNat
  all_goals
    simp only [amountDeltaSortedFrame, amountDeltaLower, amountDeltaUpper, hs, if_true, if_false]
    exact ⟨by amount_delta_prefix_get, by amount_delta_prefix_get,
      by amount_delta_prefix_get, by amount_delta_prefix_get⟩

end Benchmarks.UniswapV3.Pool
