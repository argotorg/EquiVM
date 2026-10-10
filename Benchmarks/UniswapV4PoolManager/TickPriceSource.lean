import Benchmarks.UniswapV4PoolManager.TickPriceNormalizeSource
import Benchmarks.UniswapV4PoolManager.TickPriceFinishSource
import Benchmarks.UniswapV4PoolManager.MostSignificantBitSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickPriceGuardExpr : Expr :=
  .binary .gt (.cast (.binary .sub (.var "sqrtPriceX96") (.intLit 4295128739))
    (.elem (.int (.uint ⟨160, by decide⟩))))
    (.inRange (.uint ⟨256, by decide⟩) (.binary .sub
      (.inRange (.uint ⟨256, by decide⟩) (.binary .sub
        (.intLit 1461446703485210103287273052203988822378723970342) (.intLit 4295128739))) (.intLit 1)))

theorem tickPriceGuardEval {f : Frame} {evm : EVM.State} {sqrtPrice : UInt256}
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) :
    evalExpr? config f evm tickPriceGuardExpr = .ok (.bool (decide (tickPriceOutside sqrtPrice))) := by
  simp only [tickPriceGuardExpr, evalExpr?, evalLocalValue hs, bind, EvalResult.bind, pure,
    evalBinaryOp?, castValue?, EvalResult.ofOption]
  rfl

theorem tickLogStageData_avoids_tick : ∀ stage ∈ tickLogStageData, "tick" ≠ stage.name := by
  have h : tickLogStageData.all (fun stage => decide ("tick" ≠ stage.name)) = true := by decide +kernel
  intro stage hs
  exact of_decide_eq_true ((List.all_eq_true.mp h) stage hs)

set_option maxHeartbeats 1000000 in
theorem tickPriceBlock {f : Frame} {evm : EVM.State} {sqrtPrice : UInt256}
    (hf : f.contract = contract)
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) :
    ∃ f', ExecBlock config f evm tickPriceFunction.body
      (signedWordResult f' evm (tickPriceResult sqrtPrice)) := by
  let f1 : Frame := {f with locals := f.locals.insert "tick" (.int 0)}
  have hinit : ExecStmt config f evm tickPriceFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hs1 : f1.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) :=
    (store_get_ne _ _ (by decide : ("tick" == "sqrtPriceX96") = false)).trans hs
  have hguard := tickPriceGuardEval (evm := evm) hs1
  by_cases hout : tickPriceOutside sqrtPrice
  · simp only [signedWordResult, tickPriceResult, if_pos hout]
    exact ⟨f1, (ExecBlock.consNormal hinit (ExecBlock.consRevert
      (ExecStmt.iteTrue (by simpa only [decide_eq_true hout] using hguard)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))⟩
  · let price := UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32)
    let msb := mostSignificantBit price
    let f2 : Frame := {f1 with locals := f1.locals.insert "price" (.int (Int.ofNat price.toNat))}
    let f3 : Frame := {f2 with locals := f2.locals.insert "r" (.int (Int.ofNat price.toNat))}
    have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
      (evalLocalValue (cfg := config) (evm := evm) hs1)
    rw [normalizeInt_uint256_word] at hcast
    have hprice := evalWordShl (n := 32) (b := .intLit 32) (by decide) hcast
      (by simp only [evalExpr?, pure]; rfl)
    have hp2 : f2.locals.get? "price" = some (.int (Int.ofNat price.toNat)) := store_get_self _ _ _
    have hpref : ExecBlock config f evm (tickPriceFunction.body.take 4) (.ok f3 evm) :=
      ExecBlock.consNormal hinit (ExecBlock.consNormal
        (ExecStmt.iteFalse (by simpa only [decide_eq_false hout] using hguard) ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.letDecl hprice)
          (ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue hp2)) ExecBlock.nil)))
    have hr3 : f3.locals.get? "r" = some (.int (Int.ofNat price.toNat)) := store_get_self _ _ _
    have hmsb := mostSignificantBitCall (f := f3) (evm := evm) (x := price) hf (evalLocalValue hr3) "msb"
    by_cases hz : price = ⟨0⟩
    · rw [if_pos hz] at hmsb
      have hz' : UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) = ⟨0⟩ := hz
      simp only [signedWordResult, tickPriceResult, if_neg hout, if_pos hz']
      exact ⟨f3, (execBlock_append_ok hpref (ExecBlock.consRevert hmsb))⟩
    · rw [if_neg hz] at hmsb
      let f4 : Frame := {f3 with locals := f3.locals.insert "msb" (.int (Int.ofNat msb.toNat))}
      let r := tickPriceNormalize price msb
      let log2 := tickPriceLogStart msb
      let f5 : Frame := {f4 with locals := f4.locals.insert "r" (.int (Int.ofNat r.toNat))}
      let f6 : Frame := {f5 with locals := f5.locals.insert "log_2" (.int (EVM.signed log2))}
      have hp4 : f4.locals.get? "price" = some (.int (Int.ofNat price.toNat)) :=
        (store_get_ne2 _ _ _ (by decide : ("r" == "price") = false)
          (by decide : ("msb" == "price") = false)).trans hp2
      have hm4 : f4.locals.get? "msb" = some (.int (Int.ofNat msb.toNat)) := store_get_self _ _ _
      have hr4 : f4.locals.get? "r" = some (.int (Int.ofNat price.toNat)) :=
        (store_get_ne _ _ (by decide : ("msb" == "r") = false)).trans hr3
      have hm5 : f5.locals.get? "msb" = some (.int (Int.ofNat msb.toNat)) :=
        (store_get_ne _ _ (by decide : ("r" == "msb") = false)).trans hm4
      have hsetup : ExecBlock config f3 evm ((tickPriceFunction.body.drop 4).take 3) (.ok f6 evm) :=
        ExecBlock.consNormal hmsb (ExecBlock.consNormal
          (tickPriceNormalizeSource (mostSignificantBit_lt_256 price) hp4 hm4 hr4)
          (ExecBlock.consNormal (tickPriceLogStartSource hm5) ExecBlock.nil))
      have hr6 : f6.locals.get? "r" = some (.int (Int.ofNat r.toNat)) :=
        (store_get_ne _ _ (by decide : ("log_2" == "r") = false)).trans (store_get_self _ _ _)
      have hl6 : f6.locals.get? "log_2" = some (.int (EVM.signed log2)) := store_get_self _ _ _
      obtain ⟨f7, hsteps, hr7, hl7, hc7, hk7⟩ := tickLogStagesExec (f := f6) (evm := evm)
        tickLogStageData tickLogStageData_valid hf hr6 hl6
      have hstmts : tickLogStageData.flatMap TickLogStage.statements =
          (tickPriceFunction.body.drop 7).take 42 := by decide +kernel
      rw [hstmts] at hsteps
      have hs6 : f6.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) :=
        (store_get_ne5 _ _ _ _ _ _ (by decide : ("price" == "sqrtPriceX96") = false)
          (by decide : ("r" == "sqrtPriceX96") = false)
          (by decide : ("msb" == "sqrtPriceX96") = false)
          (by decide : ("r" == "sqrtPriceX96") = false)
          (by decide : ("log_2" == "sqrtPriceX96") = false)).trans hs1
      have ht6 : f6.locals.get? "tick" = some (.int 0) :=
        (store_get_ne5 _ _ _ _ _ _ (by decide : ("price" == "tick") = false)
          (by decide : ("r" == "tick") = false)
          (by decide : ("msb" == "tick") = false)
          (by decide : ("r" == "tick") = false)
          (by decide : ("log_2" == "tick") = false)).trans (store_get_self _ _ _)
      have hs7 := (hk7 "sqrtPriceX96" (by decide) (by decide) tickLogStageData_avoids_sqrt).trans hs6
      have ht7 := (hk7 "tick" (by decide) (by decide) tickLogStageData_avoids_tick).trans ht6
      obtain ⟨f8, hfinish⟩ := tickPriceFinishSource (f := f7) (log2 := tickPriceLog sqrtPrice)
        (hc7.trans hf) hs7 hl7 ht7
      have hz' : UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) ≠ ⟨0⟩ := hz
      simp only [tickPriceResult, if_neg hout, if_neg hz']
      exact ⟨f8, execBlock_append_ok hpref
        (execBlock_append_ok hsetup (execBlock_append_ok hsteps hfinish))⟩

theorem tickPriceBody {f : Frame} {evm : EVM.State} {sqrtPrice : UInt256}
    (hf : f.contract = contract)
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) :
    ∃ f', ExecFuncBody config f evm tickPriceFunction.body
      (signedWordResult f' evm (tickPriceResult sqrtPrice)) :=
  execFuncBodySignedWordResult (tickPriceBlock hf hs)

theorem tickPriceCall {f : Frame} {evm : EVM.State} {e : Expr} {sqrtPrice : UInt256}
    (hf : f.contract = contract)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat sqrtPrice.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "TickMath_getTickAtSqrtPrice" [e] retVar)
      (match tickPriceResult sqrtPrice with
       | none => .reverted
       | some tick => .ok {f with locals := f.locals.insert retVar (.int (EVM.signed tick))} evm) := by
  obtain ⟨f', hb⟩ := tickPriceBody
    (f := {f with locals := (∅ : Store).insert "sqrtPriceX96" (.int (Int.ofNat sqrtPrice.toNat))})
    (evm := evm) hf (store_get_self _ _ _)
  have hl : lookupCallable? f.contract "TickMath_getTickAtSqrtPrice" = some tickPriceFunction.toCallable := by
    rw [hf]; exact tickPrice_lookup
  cases ht : tickPriceResult sqrtPrice with
  | none =>
    simp only [ht, signedWordResult] at hb
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hb
  | some tick =>
    simp only [ht, signedWordResult] at hb
    exact internalCallFunctionReturn (value := some [.int (EVM.signed tick)])
      (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
