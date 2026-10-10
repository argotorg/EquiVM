import Benchmarks.UniswapV4PoolManager.PoolFeeInsidePrelude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolFeeInsideRegion (evm : EVM.State) (id : UInt256) (lower upper : Int) : FeeGrowthRegion :=
  if poolCurrentTick evm id < lower then .below else
    if poolCurrentTick evm id ≥ upper then .above else .inside

def poolFeeInsideWord (evm : EVM.State) (id : UInt256) (lower upper : Int) (second : Bool) : UInt256 :=
  poolFeeInsideRegionWord evm id lower upper (poolFeeInsideRegion evm id lower upper) second

def poolFeeInsideValues (evm : EVM.State) (id : UInt256) (lower upper : Int) : List Value :=
  [.int (Int.ofNat (poolFeeInsideWord evm id lower upper false).toNat),
   .int (Int.ofNat (poolFeeInsideWord evm id lower upper true).toNat)]

theorem poolFeeInsideBranch {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    {old0 old1 : Value} (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "lower" = some (tickRefValue id lower))
    (hu : f.locals.get? "upper" = some (tickRefValue id upper))
    (htl : f.locals.get? "tickLower" = some (.int lower))
    (htu : f.locals.get? "tickUpper" = some (.int upper))
    (hc : f.locals.get? "tickCurrent" = some (.int (poolCurrentTick evm id)))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some old0)
    (h1 : f.locals.get? "feeGrowthInside1X128" = some old1) :
    ExecStmt config f evm poolFeeInsideFunction.body[5]!
      (.ok (poolFeeInsideRegionFrame f evm id lower upper (poolFeeInsideRegion evm id lower upper)) evm) := by
  have hlt : evalExpr? config f evm (.binary .lt (.var "tickCurrent") (.var "tickLower")) =
      .ok (.bool (decide (poolCurrentTick evm id < lower))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hc, evalLocalValue htl]
    rfl
  have hge : evalExpr? config f evm (.binary .ge (.var "tickCurrent") (.var "tickUpper")) =
      .ok (.bool (decide (poolCurrentTick evm id ≥ upper))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hc, evalLocalValue htu]
    rfl
  unfold poolFeeInsideRegion
  by_cases hb : poolCurrentTick evm id < lower
  · rw [if_pos hb]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hb] using hlt)
      (poolFeeInsideRegionRun hs hl hu h0 h1 .below)
  · rw [if_neg hb]
    apply ExecStmt.iteFalse (by simpa only [decide_eq_false hb] using hlt)
    by_cases ha : poolCurrentTick evm id ≥ upper
    · rw [if_pos ha]
      exact execBlock_singleton (ExecStmt.iteTrue (by simpa only [decide_eq_true ha] using hge)
        (poolFeeInsideRegionRun hs hl hu h0 h1 .above))
    · rw [if_neg ha]
      exact execBlock_singleton (ExecStmt.iteFalse (by simpa only [decide_eq_false ha] using hge)
        (poolFeeInsideRegionRun hs hl hu h0 h1 .inside))

theorem poolFeeInsideBody {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "tickLower" = some (.int lower))
    (hu : f.locals.get? "tickUpper" = some (.int upper)) :
    ∃ f', ExecFuncBody config f evm poolFeeInsideFunction.body
      (.returned f' evm (some (poolFeeInsideValues evm id lower upper))) := by
  let f1 := poolFeeInsidePreludeFrame f evm id lower upper
  have hpre := poolFeeInsidePrelude (evm := evm) hf hs hl hu
  have hs1 : f1.locals.get? "self" = some (poolRefValue id) :=
    (poolFeeInsidePreludeFrame_get (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
  have htl : f1.locals.get? "tickLower" = some (.int lower) :=
    (poolFeeInsidePreludeFrame_get (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have htu : f1.locals.get? "tickUpper" = some (.int upper) :=
    (poolFeeInsidePreludeFrame_get (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu
  have hl1 : f1.locals.get? "lower" = some (tickRefValue id lower) :=
    (store_get_ne2 _ _ _ (by decide : ("upper" == "lower") = false)
      (by decide : ("tickCurrent" == "lower") = false)).trans (store_get_self _ _ _)
  have hu1 : f1.locals.get? "upper" = some (tickRefValue id upper) :=
    (store_get_ne _ _ (by decide : ("tickCurrent" == "upper") = false)).trans (store_get_self _ _ _)
  have hc1 : f1.locals.get? "tickCurrent" = some (.int (poolCurrentTick evm id)) := store_get_self _ _ _
  have h0 : f1.locals.get? "feeGrowthInside0X128" = some (.int 0) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("feeGrowthInside1X128" == "feeGrowthInside0X128") = false)
      (by decide : ("lower" == "feeGrowthInside0X128") = false)
      (by decide : ("upper" == "feeGrowthInside0X128") = false)
      (by decide : ("tickCurrent" == "feeGrowthInside0X128") = false)).trans (store_get_self _ _ _)
  have h1 : f1.locals.get? "feeGrowthInside1X128" = some (.int 0) :=
    (store_get_ne3 _ _ _ _ (by decide : ("lower" == "feeGrowthInside1X128") = false)
      (by decide : ("upper" == "feeGrowthInside1X128") = false)
      (by decide : ("tickCurrent" == "feeGrowthInside1X128") = false)).trans (store_get_self _ _ _)
  have hbranch := poolFeeInsideBranch hs1 hl1 hu1 htl htu hc1 h0 h1
  let f2 := poolFeeInsideRegionFrame f1 evm id lower upper (poolFeeInsideRegion evm id lower upper)
  refine ⟨f2, execFuncBody_prepend hpre ?_⟩
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal hbranch (ExecBlock.consReturn (ExecStmt.return ?_)))
  have h0' : f2.locals.get? "feeGrowthInside0X128" =
      some (.int (Int.ofNat (poolFeeInsideWord evm id lower upper false).toNat)) :=
    (store_get_ne _ _ (by decide : ("feeGrowthInside1X128" == "feeGrowthInside0X128") = false)).trans
      (store_get_self _ _ _)
  have h1' : f2.locals.get? "feeGrowthInside1X128" =
      some (.int (Int.ofNat (poolFeeInsideWord evm id lower upper true).toNat)) := store_get_self _ _ _
  change evalExprs? config f2 evm [.var "feeGrowthInside0X128", .var "feeGrowthInside1X128"] = _
  simp only [poolFeeInsideValues, evalExprs?, evalLocalValue (cfg := config) (f := f2) (evm := evm) h0',
    evalLocalValue (cfg := config) (f := f2) (evm := evm) h1', bind, EvalResult.bind, pure]

theorem poolFeeInsideCall {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    {es el eu : Expr} (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (hl : evalExpr? config f evm el = .ok (.int lower))
    (hu : evalExpr? config f evm eu = .ok (.int upper)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_getFeeGrowthInside" [es, el, eu] ret)
      (.ok {f with locals := f.locals.insert ret (.tuple (poolFeeInsideValues evm id lower upper))} evm) := by
  obtain ⟨f', hbody⟩ := poolFeeInsideBody
    (f := {f with locals := ((((∅ : Store).insert "tickUpper" (.int upper)).insert "tickLower" (.int lower)).insert
      "self" (poolRefValue id))}) (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "tickLower") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("tickLower" == "tickUpper") = false)
      (by decide : ("self" == "tickUpper") = false)).trans (store_get_self _ _ _))
  exact internalCallFunctionReturn (argVals := [poolRefValue id, .int lower, .int upper])
    (value := some (poolFeeInsideValues evm id lower upper))
    (by simp only [evalExprs?, hs, hl, hu, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolFeeInside_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
