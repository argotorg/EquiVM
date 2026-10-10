import Benchmarks.UniswapV4PoolManager.PoolModifyTickAssignments
import Benchmarks.UniswapV4PoolManager.PoolUpdateTickResult
import Benchmarks.UniswapV4PoolManager.CallContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTickAlias (upper : Bool) : Ident :=
  if upper then "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.7"
  else "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.6"
def poolModifyTickAliasFrame (f : Frame) (id : UInt256) (upper : Bool) : Frame :=
  {f with locals := f.locals.insert (poolModifyTickAlias upper) (poolRefValue id)}

def poolModifyTickBlock (upper : Bool) : List Stmt :=
  .letStorage (poolModifyTickAlias upper) {base := "self"} ::
  .internalCall "Pool_updateTick" [.var (poolModifyTickAlias upper), .var (poolModifyTickName upper),
    .var "liquidityDelta", .boolLit upper] (poolModifyTickRet upper) :: poolModifyTickAssignBlock upper

def poolModifyTickResult (f : Frame) (evm : State) (id : UInt256) (tick delta : Int)
    (upper fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : ExecResult :=
  let packed := tickFieldWord evm id tick .liquidityPacked
  let fa := poolModifyTickAliasFrame f id upper
  continueCallResult (fun post values =>
    .ok (poolModifyTickFrame (resumeAfterInternalCall fa (poolModifyTickRet upper) values) upper
      (tickFlipped packed delta) (EVM.wordOfInt (tickGrossAfterInt packed delta)) fl gl fu gu) post)
    (poolUpdateTickResult fa evm id tick delta upper)

theorem poolModifyTick {f : Frame} {evm : State} {id : UInt256} {tick delta : Int}
    {upper fl fu : Bool} {gl gu : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? (poolModifyTickName upper) = some (.int tick))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta))
    (hstate : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) :
    ExecBlock config f evm (poolModifyTickBlock upper)
      (poolModifyTickResult f evm id tick delta upper fl gl fu gu) := by
  let fa := poolModifyTickAliasFrame f id upper
  have ha : ExecStmt config f evm (.letStorage (poolModifyTickAlias upper) {base := "self"}) (.ok fa evm) :=
    ExecStmt.letStorage (resolveStorageAlias hs)
  have hat : fa.locals.get? (poolModifyTickName upper) = some (.int tick) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyTickAlias upper == poolModifyTickName upper) = false)).trans ht
  have had : fa.locals.get? "liquidityDelta" = some (.int delta) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyTickAlias upper == "liquidityDelta") = false)).trans hd
  have has : fa.locals.get? "state" = some (poolModifyStateValue fl gl fu gu) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyTickAlias upper == "state") = false)).trans hstate
  have hc := poolUpdateTickCall (f := fa) (evm := evm) hf (evalLocalValue (store_get_self _ _ _))
    (evalLocalValue hat) (evalLocalValue had)
    (show evalExpr? config fa evm (.boolLit upper) = .ok (.bool upper) by simp only [evalExpr?, pure])
    (poolModifyTickRet upper)
  apply ExecBlock.consNormal ha
  apply execBlock_continueCall hc
  intro cf post values hret
  have hv := poolUpdateTickReturnedValues hret
  rw [hv]
  apply poolModifyTickAssignments
  · change (fa.locals.insert (poolModifyTickRet upper) _).get? "state" = _
    exact (store_get_ne _ _ (by cases upper <;> decide : (poolModifyTickRet upper == "state") = false)).trans has
  · exact store_get_self _ _ _

end Benchmarks.UniswapV4PoolManager
