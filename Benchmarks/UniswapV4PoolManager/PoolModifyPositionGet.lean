import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.PositionGetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyPositionAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.11"
def poolModifyPositionKey (p : PoolModifyParams) : UInt256 := positionKey p.owner p.lower p.upper p.salt
def poolModifyPositionGetFrame (f : Frame) (id : UInt256) (p : PoolModifyParams) : Frame :=
  {f with locals := (((f.locals.insert poolModifyPositionAlias (positionsRefValue id)).insert "__c7"
    (positionRefValue id (poolModifyPositionKey p))).insert "position" (positionRefValue id (poolModifyPositionKey p)))}

theorem poolModifyPositionGet {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 12).take 3)
      (.ok (poolModifyPositionGetFrame f id p) evm) := by
  let fa := {f with locals := f.locals.insert poolModifyPositionAlias (positionsRefValue id)}
  let fc := {fa with locals := fa.locals.insert "__c7" (positionRefValue id (poolModifyPositionKey p))}
  have ha : ExecStmt config f evm poolModifyFunction.body[12]! (.ok fa evm) :=
    ExecStmt.letStorage (resolveStorageAliasField hc.self rfl)
  have hca : PoolModifyContext fa id p := hc.insert poolModifyPositionAlias _ (by decide)
  have hep := evalLocalValue (cfg := config) (f := fa) (evm := evm) hca.params
  have hcall := positionGetCall (f := fa) (evm := evm) hca.contract (evalLocalValue (store_get_self _ _ _))
    (evalStructField hep (field := "owner") rfl) (evalLocalValue hca.lower) (evalLocalValue hca.upper)
    (evalStructField hep (field := "salt") rfl) hl hu "__c7"
  have hp : ExecStmt config fc evm poolModifyFunction.body[14]!
      (.ok (poolModifyPositionGetFrame f id p) evm) :=
    ExecStmt.letStorage (resolveStorageAlias (store_get_self _ _ _))
  exact ExecBlock.consNormal ha (ExecBlock.consNormal hcall (execBlock_singleton hp))

theorem poolModifyPositionGetFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) : PoolModifyContext (poolModifyPositionGetFrame f id p) id p :=
  ((hc.insert poolModifyPositionAlias _ (by decide)).insert "__c7" _ (by decide)).insert "position" _ (by decide)

theorem poolModifyPositionGetFrame_get (f : Frame) (id : UInt256) (p : PoolModifyParams) (name : Ident)
    (ha : (poolModifyPositionAlias == name) = false) (hc : ("__c7" == name) = false)
    (hp : ("position" == name) = false) :
    (poolModifyPositionGetFrame f id p).locals.get? name = f.locals.get? name := store_get_ne3 _ _ _ _ ha hc hp

end Benchmarks.UniswapV4PoolManager
