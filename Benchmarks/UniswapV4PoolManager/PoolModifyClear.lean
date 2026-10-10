import Benchmarks.UniswapV4PoolManager.PoolModifyTickAssignments
import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.ConditionalSource
import Benchmarks.UniswapV4PoolManager.TickClearSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyClearAlias (upper : Bool) : Ident :=
  if upper then "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.14"
  else "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.13"
def poolModifyClearRet (upper : Bool) : Ident := if upper then "__c13" else "__c12"
def poolModifyClearAliasFrame (f : Frame) (id : UInt256) (upper : Bool) : Frame :=
  {f with locals := f.locals.insert (poolModifyClearAlias upper) (poolRefValue id)}
def poolModifyClearFrame (f : Frame) (id : UInt256) (upper : Bool) : Frame :=
  resumeAfterInternalCall (poolModifyClearAliasFrame f id upper) (poolModifyClearRet upper) none
def poolModifyClearStmt (upper : Bool) : Stmt :=
  .ite (.field (.var "state") (poolModifyFlipField upper))
    [.letStorage (poolModifyClearAlias upper) {base := "self"},
     .internalCall "Pool_clearTick" [.var (poolModifyClearAlias upper), .var (poolModifyTickName upper)]
       (poolModifyClearRet upper)] []
def poolModifyClearResult (f : Frame) (evm : State) (id : UInt256) (tick : Int)
    (upper flipped : Bool) : ExecResult :=
  if flipped then
    resumeCallResult (poolModifyClearAliasFrame f id upper) (poolModifyClearRet upper)
      (tickClearResult (poolModifyClearAliasFrame f id upper) evm id tick)
  else .ok f evm

theorem poolModifyClear {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {upper fl fu : Bool} {gl gu : UInt256} {tick : Int} (hc : PoolModifyContext f id p)
    (ht : f.locals.get? (poolModifyTickName upper) = some (.int tick))
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) :
    ExecStmt config f evm (poolModifyClearStmt upper)
      (poolModifyClearResult f evm id tick upper (if upper then fu else fl)) := by
  have he := evalStructField (evalLocalValue (cfg := config) (f := f) (evm := evm) hs)
    (show lookupField? (poolModifyStateValue fl gl fu gu) (poolModifyFlipField upper) =
      some (.bool (if upper then fu else fl)) by cases upper <;> rfl)
  let fa := poolModifyClearAliasFrame f id upper
  have ht' : fa.locals.get? (poolModifyTickName upper) = some (.int tick) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyClearAlias upper == poolModifyTickName upper) = false)).trans ht
  have hcall := tickClearCall (f := fa) (evm := evm) hc.contract (evalLocalValue (store_get_self _ _ _))
    (evalLocalValue ht') (poolModifyClearRet upper)
  exact execStmt_conditionalAliasCall he (resolveStorageAlias hc.self) hcall

theorem poolModifyClearResult_frame {f f' : Frame} {evm post : State} {id : UInt256}
    {tick : Int} {upper flipped : Bool}
    (h : poolModifyClearResult f evm id tick upper flipped = .ok f' post) :
    f' = (if flipped then poolModifyClearFrame f id upper else f) := by
  unfold poolModifyClearResult tickClearResult at h
  split_ifs at h <;> cases h <;> simp_all only [poolModifyClearFrame, Bool.false_eq_true, if_pos, if_false]

theorem poolModifyClearResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {tick : Int} {upper flipped : Bool} (hc : PoolModifyContext f id p)
    (h : poolModifyClearResult f evm id tick upper flipped = .ok f' post) : PoolModifyContext f' id p := by
  rw [poolModifyClearResult_frame h]
  cases flipped with
  | false => exact hc
  | true =>
    exact (hc.insert (poolModifyClearAlias upper) _ (by cases upper <;> decide)).resume
      (poolModifyClearRet upper) none (by cases upper <;> decide)

theorem poolModifyClearResult_get {f f' : Frame} {evm post : State} {id : UInt256}
    {tick : Int} {upper flipped : Bool}
    (h : poolModifyClearResult f evm id tick upper flipped = .ok f' post)
    (name : Ident) (ha : (poolModifyClearAlias upper == name) = false)
    (hr : (poolModifyClearRet upper == name) = false) : f'.locals.get? name = f.locals.get? name := by
  rw [poolModifyClearResult_frame h]
  cases flipped with
  | false => rfl
  | true => exact store_get_ne2 _ _ _ ha hr

end Benchmarks.UniswapV4PoolManager
