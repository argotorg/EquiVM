import Benchmarks.UniswapV4PoolManager.PoolSwapCrossWords
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapTickSyntax
import Benchmarks.UniswapV4PoolManager.TickCrossSource
import Benchmarks.UniswapV4PoolManager.WordSignedCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapCrossCallFrame (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool) : Frame :=
  valueLocal (wordLocal (wordLocal f "feeGrowthGlobal0X128" (poolSwapCrossGrowth0 evm id s zeroForOne))
    "feeGrowthGlobal1X128" (poolSwapCrossGrowth1 evm id s zeroForOne)) poolSwapCrossAlias (poolRefValue id)

def poolSwapCrossNetFrame (f : Frame) (zeroForOne : Bool) (net : UInt256) : Frame :=
  if zeroForOne then valueLocal (valueLocal f "liquidityNet" (.int (EVM.signed net)))
    "liquidityNet" (.int (EVM.signed (poolSwapCrossDelta zeroForOne net)))
  else valueLocal f "liquidityNet" (.int (EVM.signed net))

def poolSwapCrossFrame (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) : Frame :=
  let f0 := poolSwapCrossCallFrame f evm id s zeroForOne
  let f1 := poolSwapCrossNetFrame f0 zeroForOne (poolSwapCrossNet evm id s zeroForOne)
  let liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity
  valueLocal (wordLocal f1 "__c22" liquidity) "result" (poolSwapResultValue {r with liquidity := liquidity})

def poolSwapCrossResult (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation
  else if liquidityAddFits r.liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne))) then
    .ok (poolSwapCrossFrame f evm id s r zeroForOne) (poolSwapCrossPost evm id s zeroForOne)
  else .reverted

theorem poolSwapCrossNegate {f : Frame} {evm : State} {net : UInt256} {zeroForOne : Bool}
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecStmt config (valueLocal f "liquidityNet" (.int (EVM.signed net))) evm poolSwapCrossStmts[4]!
      (.ok (poolSwapCrossNetFrame f zeroForOne net) evm) := by
  let f1 := valueLocal f "liquidityNet" (.int (EVM.signed net))
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool zeroForOne) :=
    (store_get_ne _ _ (by decide : ("liquidityNet" == "zeroForOne") = false)).trans hz
  cases zeroForOne with
  | false => exact ExecStmt.iteFalse (evalLocalValue hz1) ExecBlock.nil
  | true =>
    apply ExecStmt.iteTrue (evalLocalValue hz1)
    have he : evalExpr? config f1 evm (.binary .sub (.intLit 0) (.var "liquidityNet")) =
        .ok (.int (EVM.signed (⟨0⟩ : UInt256) - EVM.signed net)) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue (store_get_self _ _ _)]
      simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
      rfl
    have hn : normalizeInt (.sint ⟨128, by decide⟩) (EVM.signed (⟨0⟩ : UInt256) - EVM.signed net) =
        EVM.signed (poolSwapCrossDelta true net) := by
      rw [← normalizeSignedEncoded ⟨128, by decide⟩ _, normalizeSigned128Word, wordOfInt_signed_sub]
      rfl
    exact execBlock_singleton (ExecStmt.assign (by
      simpa only [hn] using evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) he)
      (assignLocalValue (store_get_self _ _ _)))

theorem poolSwapCrossSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecBlock config f evm poolSwapCrossStmts (poolSwapCrossResult f evm id s r zeroForOne) := by
  let g0 := poolSwapCrossGrowth0 evm id s zeroForOne
  let g1 := poolSwapCrossGrowth1 evm id s zeroForOne
  let f1 := wordLocal f "feeGrowthGlobal0X128" g0
  let f2 := wordLocal f1 "feeGrowthGlobal1X128" g1
  let f3 := poolSwapCrossCallFrame f evm id s zeroForOne
  let net := poolSwapCrossNet evm id s zeroForOne
  let post := poolSwapCrossPost evm id s zeroForOne
  let f5 := poolSwapCrossNetFrame f3 zeroForOne net
  have he0 : evalExpr? config f evm
      (.ite (.var "zeroForOne") (.field (.var "step") "feeGrowthGlobalX128")
        (.storage {base := "self", steps := [.field "feeGrowthGlobal0X128"]})) = .ok (.int (Int.ofNat g0.toNat)) := by
    rw [evalExpr?, evalLocalValue hz]
    cases zeroForOne
    · exact poolFeeGrowth_read hself false
    · exact evalStructField (evalLocalValue hs) rfl
  have hs1 : f1.locals.get? "step" = some (poolSwapStepValue s) :=
    (store_get_ne _ _ (by decide : ("feeGrowthGlobal0X128" == "step") = false)).trans hs
  have hself1 : f1.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("feeGrowthGlobal0X128" == "self") = false)).trans hself
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool zeroForOne) :=
    (store_get_ne _ _ (by decide : ("feeGrowthGlobal0X128" == "zeroForOne") = false)).trans hz
  have he1 : evalExpr? config f1 evm
      (.ite (.var "zeroForOne") (.storage {base := "self", steps := [.field "feeGrowthGlobal1X128"]})
        (.field (.var "step") "feeGrowthGlobalX128")) = .ok (.int (Int.ofNat g1.toNat)) := by
    rw [evalExpr?, evalLocalValue hz1]
    cases zeroForOne
    · exact evalStructField (evalLocalValue hs1) rfl
    · exact poolFeeGrowth_read hself1 true
  have hself2 : f2.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("feeGrowthGlobal1X128" == "self") = false)).trans hself1
  have hpre : ExecBlock config f evm (poolSwapCrossStmts.take 3) (.ok f3 evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl he0) (ExecBlock.consNormal (ExecStmt.letDecl he1)
      (execBlock_singleton (ExecStmt.letStorage (resolveStorageAlias hself2))))
  have hs3 : f3.locals.get? "step" = some (poolSwapStepValue s) :=
    (store_get_ne2 _ _ _ (by decide : ("feeGrowthGlobal1X128" == "step") = false)
      (by decide : (poolSwapCrossAlias == "step") = false)).trans hs1
  have hz3 : f3.locals.get? "zeroForOne" = some (.bool zeroForOne) :=
    (store_get_ne2 _ _ _ (by decide : ("feeGrowthGlobal1X128" == "zeroForOne") = false)
      (by decide : (poolSwapCrossAlias == "zeroForOne") = false)).trans hz1
  have hg03 : f3.locals.get? "feeGrowthGlobal0X128" = some (.int (Int.ofNat g0.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("feeGrowthGlobal1X128" == "feeGrowthGlobal0X128") = false)
      (by decide : (poolSwapCrossAlias == "feeGrowthGlobal0X128") = false)).trans (store_get_self _ _ _)
  have hg13 : f3.locals.get? "feeGrowthGlobal1X128" = some (.int (Int.ofNat g1.toNat)) :=
    (store_get_ne _ _ (by decide : (poolSwapCrossAlias == "feeGrowthGlobal1X128") = false)).trans (store_get_self _ _ _)
  have hf3 : f3.contract = contract := by
    simp only [f3, poolSwapCrossCallFrame, valueLocal_contract, wordLocal_contract, hf]
  have hcall := tickCrossCall (f := f3) (evm := evm) hf3 (evalLocalValue (name := poolSwapCrossAlias) (store_get_self _ _ _))
    (poolSwapStep_tick_eval hs3) (evalLocalValue hg03) (evalLocalValue hg13) "liquidityNet"
  simp only [tickCrossResult, resumeCallResult_ite, resumeCallResult_static, resumeCallResult_returned] at hcall
  unfold poolSwapCrossResult
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hcall ⊢
    exact execBlock_append hpre (ExecBlock.consStatic hcall)
  · rw [if_neg hp] at hcall ⊢
    have hneg := poolSwapCrossNegate (evm := post) (net := net) hz3
    have hr3 : f3.locals.get? "result" = some (poolSwapResultValue r) :=
      (store_get_ne3 _ _ _ _ (by decide : ("feeGrowthGlobal0X128" == "result") = false)
        (by decide : ("feeGrowthGlobal1X128" == "result") = false)
        (by decide : (poolSwapCrossAlias == "result") = false)).trans hr
    have hr5 : f5.locals.get? "result" = some (poolSwapResultValue r) := by
      cases zeroForOne
      · exact (store_get_ne _ _ (by decide : ("liquidityNet" == "result") = false)).trans hr3
      · exact (store_get_ne2 _ _ _ (by decide : ("liquidityNet" == "result") = false)
          (by decide : ("liquidityNet" == "result") = false)).trans hr3
    have hn5 : f5.locals.get? "liquidityNet" = some (.int (EVM.signed (poolSwapCrossDelta zeroForOne net))) := by
      cases zeroForOne <;> exact store_get_self _ _ _
    have hf5 : f5.contract = contract := by
      unfold f5 poolSwapCrossNetFrame
      split <;> simpa only [valueLocal_contract] using hf3
    have hadd := liquidityAddCall hf5 (evalStructField (field := "liquidity") (evalLocalValue (evm := post) hr5) rfl)
      (evalLocalValue hn5) "__c22"
    by_cases hfit : liquidityAddFits r.liquidity (EVM.signed (poolSwapCrossDelta zeroForOne net))
    · rw [if_pos hfit] at hadd ⊢
      rw [← liquidityAddResultWord_value hfit] at hadd
      have hstore : ExecStmt config
          (wordLocal f5 "__c22" (poolSwapCrossLiquidity evm id s zeroForOne r.liquidity)) post poolSwapCrossStmts[6]!
          (.ok (poolSwapCrossFrame f evm id s r zeroForOne) post) :=
        ExecStmt.assign wordLocal_eval (assignLocalField
          ((store_get_ne _ _ (by decide : ("__c22" == "result") = false)).trans hr5) rfl rfl)
      exact execBlock_append hpre (ExecBlock.consNormal hcall (ExecBlock.consNormal hneg
        (ExecBlock.consNormal hadd (execBlock_singleton hstore))))
    · rw [if_neg hfit] at hadd ⊢
      exact execBlock_append hpre (ExecBlock.consNormal hcall (ExecBlock.consNormal hneg (ExecBlock.consRevert hadd)))

end Benchmarks.UniswapV4PoolManager
