import Benchmarks.UniswapV4PoolManager.TickCrossWords
import Benchmarks.UniswapV4PoolManager.WordWrappingSource
import Benchmarks.UniswapV4PoolManager.ValueLocals
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickCrossFunction : FunctionDecl := contract.functions[106]!
theorem tickCross_lookup : lookupCallable? contract "Pool_crossTick" = some tickCrossFunction.toCallable := rfl

def tickCrossWriteStmts : List Stmt :=
  [.assign .storage {base := "info", steps := [.field "feeGrowthOutside0X128"]}
     (.cast (.binary .sub (.var "feeGrowthGlobal0X128")
       (.storage {base := "info", steps := [.field "feeGrowthOutside0X128"]})) (.elem (.int (.uint ⟨256, by decide⟩)))),
   .assign .storage {base := "info", steps := [.field "feeGrowthOutside1X128"]}
     (.cast (.binary .sub (.var "feeGrowthGlobal1X128")
       (.storage {base := "info", steps := [.field "feeGrowthOutside1X128"]})) (.elem (.int (.uint ⟨256, by decide⟩))))]

theorem tickCrossWriteSource {f : Frame} {evm : EVM.State} {id growth0 growth1 : UInt256} {tick : Int}
    (hi : f.locals.get? "info" = some (tickRefValue id tick))
    (h0 : f.locals.get? "feeGrowthGlobal0X128" = some (.int (Int.ofNat growth0.toNat)))
    (h1 : f.locals.get? "feeGrowthGlobal1X128" = some (.int (Int.ofNat growth1.toNat))) :
    ExecBlock config f evm tickCrossWriteStmts
      (if evm.executionEnv.perm = false then .staticViolation else .ok f (tickCrossPost evm id tick growth0 growth1)) := by
  have he0 := evalWordSub (evalLocalValue (cfg := config) (evm := evm) h0)
    (tickField_read hi .feeGrowthOutside0)
  have hw0 := tickField_write (evm := evm) hi .feeGrowthOutside0
    (UInt256.sub growth0 (tickFieldWord evm id tick .feeGrowthOutside0))
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact ExecBlock.consStatic (ExecStmt.assignStatic he0 hw0 hp)
  · rw [if_neg hp]
    have he1 := evalWordSub (evalLocalValue (cfg := config) (evm := tickCrossWrite0 evm id tick growth0) h1)
      (tickField_read hi .feeGrowthOutside1)
    have hw1 := tickField_write (evm := tickCrossWrite0 evm id tick growth0) hi .feeGrowthOutside1
      (UInt256.sub growth1 (tickFieldWord (tickCrossWrite0 evm id tick growth0) id tick .feeGrowthOutside1))
    exact ExecBlock.consNormal (ExecStmt.assign he0 hw0)
      (execBlock_singleton (ExecStmt.assign he1 hw1))

def tickCrossResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick : Int) (growth0 growth1 : UInt256) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else
    .returned f (tickCrossPost evm id tick growth0 growth1)
      (some [.int (EVM.signed (tickCrossNet evm id tick growth0 growth1))])

theorem tickCrossBody {f : Frame} {evm : EVM.State} {id growth0 growth1 : UInt256} {tick : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick))
    (h0 : f.locals.get? "feeGrowthGlobal0X128" = some (.int (Int.ofNat growth0.toNat)))
    (h1 : f.locals.get? "feeGrowthGlobal1X128" = some (.int (Int.ofNat growth1.toNat))) :
    ∃ f', ExecFuncBody config f evm tickCrossFunction.body (tickCrossResult f' evm id tick growth0 growth1) := by
  let f1 := valueLocal f "liquidityNet" (.int 0)
  let f2 := valueLocal f1 "info" (tickRefValue id tick)
  have hlet : ExecStmt config f evm tickCrossFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have href : ExecStmt config f1 evm tickCrossFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letStorage (tickMappingResolve
      ((store_get_ne _ _ (by decide : ("liquidityNet" == "self") = false)).trans hs)
      (evalLocalValue ((store_get_ne _ _ (by decide : ("liquidityNet" == "tick") = false)).trans ht)))
  have hpre : ExecBlock config f evm (tickCrossFunction.body.take 2) (.ok f2 evm) :=
    ExecBlock.consNormal hlet (execBlock_singleton href)
  have hi2 : f2.locals.get? "info" = some (tickRefValue id tick) := store_get_self _ _ _
  have h02 : f2.locals.get? "feeGrowthGlobal0X128" = some (.int (Int.ofNat growth0.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("liquidityNet" == "feeGrowthGlobal0X128") = false)
      (by decide : ("info" == "feeGrowthGlobal0X128") = false)).trans h0
  have h12 : f2.locals.get? "feeGrowthGlobal1X128" = some (.int (Int.ofNat growth1.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("liquidityNet" == "feeGrowthGlobal1X128") = false)
      (by decide : ("info" == "feeGrowthGlobal1X128") = false)).trans h1
  have hwrites := tickCrossWriteSource (evm := evm) hi2 h02 h12
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hwrites
    refine ⟨f2, ?_⟩
    rw [tickCrossResult, if_pos hp]
    apply execFuncBody_prepend hpre
    exact ExecFuncBody.execBlockStatic (execBlock_append_term hwrites (by intros; simp))
  · rw [if_neg hp] at hwrites
    let post := tickCrossPost evm id tick growth0 growth1
    let net := tickCrossNet evm id tick growth0 growth1
    let f3 := valueLocal f2 "liquidityNet" (.int (EVM.signed net))
    have hn : f2.locals.get? "liquidityNet" = some (.int 0) :=
      (store_get_ne _ _ (by decide : ("info" == "liquidityNet") = false)).trans (store_get_self _ _ _)
    have hnet : ExecStmt config f2 post tickCrossFunction.body[4]! (.ok f3 post) :=
      ExecStmt.assign (tickNet_eval (tickField_read hi2 .liquidityPacked)) (assignLocalValue hn)
    have htail : ExecFuncBody config f2 evm (tickCrossFunction.body.drop 2)
        (.returned f3 post (some [.int (EVM.signed net)])) :=
      ExecFuncBody.execBlockRet (execBlock_append_ok hwrites
        (ExecBlock.consNormal hnet (ABlock.start.returns (evalLocalValue (store_get_self _ _ _)))))
    exact ⟨f3, by rw [tickCrossResult, if_neg hp]; exact execFuncBody_prepend hpre htail⟩

theorem tickCrossCall {f : Frame} {evm : EVM.State} {id growth0 growth1 : UInt256} {tick : Int}
    {es et e0 e1 : Expr} (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (ht : evalExpr? config f evm et = .ok (.int tick))
    (h0 : evalExpr? config f evm e0 = .ok (.int (Int.ofNat growth0.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat growth1.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_crossTick" [es, et, e0, e1] ret)
      (resumeCallResult f ret (tickCrossResult f evm id tick growth0 growth1)) := by
  let fc : Frame := {f with locals :=
    (((((∅ : Store).insert "feeGrowthGlobal1X128" (.int (Int.ofNat growth1.toNat))).insert
      "feeGrowthGlobal0X128" (.int (Int.ofNat growth0.toNat))).insert "tick" (.int tick)).insert "self" (poolRefValue id))}
  obtain ⟨f', hb⟩ := tickCrossBody (f := fc) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "tick") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("tick" == "feeGrowthGlobal0X128") = false)
      (by decide : ("self" == "feeGrowthGlobal0X128") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("self" == "feeGrowthGlobal1X128") = false)).trans
      ((store_get_ne2 _ _ _ (by decide : ("feeGrowthGlobal0X128" == "feeGrowthGlobal1X128") = false)
        (by decide : ("tick" == "feeGrowthGlobal1X128") = false)).trans (store_get_self _ _ _)))
  have hc := internalCallFunctionExec (caller := f) (name := "Pool_crossTick") (retVar := ret)
    (args := [es, et, e0, e1]) (argVals := [poolRefValue id, .int tick, .int (Int.ofNat growth0.toNat), .int (Int.ofNat growth1.toNat)])
    (by simp only [evalExprs?, hs, ht, h0, h1, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickCross_lookup) rfl hb
  simpa only [tickCrossResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_static] using hc

end Benchmarks.UniswapV4PoolManager
