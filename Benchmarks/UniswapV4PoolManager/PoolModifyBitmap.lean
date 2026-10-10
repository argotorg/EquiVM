import Benchmarks.UniswapV4PoolManager.PoolModifyTickAssignments
import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.TickBitmapSource
import Benchmarks.UniswapV4PoolManager.ConditionalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFlipAlias (upper : Bool) : Ident :=
  if upper then "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.9"
  else "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.8"
def poolModifyFlipRet (upper : Bool) : Ident := if upper then "__c5" else "__c4"
def poolModifyFlipAliasFrame (f : Frame) (id : UInt256) (upper : Bool) : Frame :=
  {f with locals := f.locals.insert (poolModifyFlipAlias upper) (tickBitmapRefValue id)}
def poolModifyFlipFrame (f : Frame) (id : UInt256) (upper : Bool) : Frame :=
  resumeAfterInternalCall (poolModifyFlipAliasFrame f id upper) (poolModifyFlipRet upper) none
def poolModifyFlipStmt (upper : Bool) : Stmt :=
  .ite (.field (.var "state") (poolModifyFlipField upper))
    [.letStorage (poolModifyFlipAlias upper) {base := "self", steps := [.field "tickBitmap"]},
     .internalCall "TickBitmap_flipTick" [.var (poolModifyFlipAlias upper), .var (poolModifyTickName upper),
       .field (.var "params") "tickSpacing"] (poolModifyFlipRet upper)] []
def poolModifyFlipResult (f : Frame) (evm : State) (id : UInt256) (tick spacing : Int)
    (upper flipped : Bool) : ExecResult :=
  if flipped then
    resumeCallResult (poolModifyFlipAliasFrame f id upper) (poolModifyFlipRet upper)
      (tickBitmapResult (poolModifyFlipAliasFrame f id upper) evm id tick spacing)
  else .ok f evm

theorem poolModifyFlip {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {upper fl fu : Bool} {gl gu : UInt256} {tick : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p))
    (ht : f.locals.get? (poolModifyTickName upper) = some (.int tick))
    (hstate : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu))
    (hb : tick.natAbs ≤ 887272) :
    ExecStmt config f evm (poolModifyFlipStmt upper)
      (poolModifyFlipResult f evm id tick (EVM.signed p.spacing) upper (if upper then fu else fl)) := by
  have hc := evalStructField (evalLocalValue (cfg := config) (f := f) (evm := evm) hstate)
    (show lookupField? (poolModifyStateValue fl gl fu gu) (poolModifyFlipField upper) =
      some (.bool (if upper then fu else fl)) by cases upper <;> rfl)
  let fa := poolModifyFlipAliasFrame f id upper
  have ht' : fa.locals.get? (poolModifyTickName upper) = some (.int tick) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyFlipAlias upper == poolModifyTickName upper) = false)).trans ht
  have hp' : fa.locals.get? "params" = some (poolModifyParamsValue p) :=
    (store_get_ne _ _ (by cases upper <;> decide : (poolModifyFlipAlias upper == "params") = false)).trans hp
  have hcall := tickBitmapCall (f := fa) (evm := evm) hf (evalLocalValue (store_get_self _ _ _))
    (evalLocalValue ht') (evalStructField (evalLocalValue hp') (field := "tickSpacing") rfl) hb
    (poolModifyFlipRet upper)
  exact execStmt_conditionalAliasCall hc (resolveStorageAliasField hs rfl) hcall

theorem poolModifyFlipResult_frame {f f' : Frame} {evm post : State} {id : UInt256}
    {tick spacing : Int} {upper flipped : Bool}
    (h : poolModifyFlipResult f evm id tick spacing upper flipped = .ok f' post) :
    f' = (if flipped then poolModifyFlipFrame f id upper else f) := by
  unfold poolModifyFlipResult tickBitmapResult at h
  split_ifs at h <;> cases h <;> simp_all only [poolModifyFlipFrame, Bool.false_eq_true, if_pos, if_false]

theorem poolModifyFlipFrame_get (f : Frame) (id : UInt256) (upper : Bool) (name : Ident)
    (ha : (poolModifyFlipAlias upper == name) = false) (hr : (poolModifyFlipRet upper == name) = false) :
    (poolModifyFlipFrame f id upper).locals.get? name = f.locals.get? name :=
  store_get_ne2 _ _ _ ha hr

theorem poolModifyFlipResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {tick spacing : Int} {upper flipped : Bool}
    (hc : PoolModifyContext f id p)
    (h : poolModifyFlipResult f evm id tick spacing upper flipped = .ok f' post) :
    PoolModifyContext f' id p := by
  rw [poolModifyFlipResult_frame h]
  cases flipped with
  | false => exact hc
  | true =>
    exact (hc.insert (poolModifyFlipAlias upper) _ (by cases upper <;> decide)).resume
      (poolModifyFlipRet upper) none (by cases upper <;> decide)

theorem poolModifyFlipResult_get {f f' : Frame} {evm post : State} {id : UInt256}
    {tick spacing : Int} {upper flipped : Bool}
    (h : poolModifyFlipResult f evm id tick spacing upper flipped = .ok f' post)
    (name : Ident) (ha : (poolModifyFlipAlias upper == name) = false)
    (hr : (poolModifyFlipRet upper == name) = false) :
    f'.locals.get? name = f.locals.get? name := by
  rw [poolModifyFlipResult_frame h]
  cases flipped with
  | false => rfl
  | true => exact poolModifyFlipFrame_get f id upper name ha hr

end Benchmarks.UniswapV4PoolManager
