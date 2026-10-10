import Benchmarks.UniswapV4PoolManager.PoolModifyPositionGet
import Benchmarks.UniswapV4PoolManager.PositionUpdateResult
import Benchmarks.UniswapV4PoolManager.CallContinuation
import Benchmarks.UniswapV4PoolManager.TupleLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyUpdateAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.12"
def poolModifyUpdateAliasFrame (f : Frame) (id key : UInt256) : Frame :=
  {f with locals := f.locals.insert poolModifyUpdateAlias (positionRefValue id key)}
def poolModifyOwedFrame (f : Frame) (owed0 owed1 : UInt256) : Frame :=
  wordLocal (wordLocal f "feesOwed0" owed0) "feesOwed1" owed1
def poolModifyPositionUpdateResult (f : Frame) (evm : State) (id key : UInt256) (delta : Int)
    (fee0 fee1 : UInt256) : ExecResult :=
  let fa := poolModifyUpdateAliasFrame f id key
  continueCallResult (fun post values => .ok
    (poolModifyOwedFrame (resumeAfterInternalCall fa "__c8" values)
      (positionUpdateOwed evm id key delta fee0 false) (positionUpdateOwed evm id key delta fee1 true)) post)
    (positionUpdateResult fa evm id key delta fee0 fee1)

theorem poolModifyPositionUpdate {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {key fee0 fee1 : UInt256} (hc : PoolModifyContext f id p)
    (hp : f.locals.get? "position" = some (positionRefValue id key))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)))
    (h1 : f.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat))) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 15).take 4)
      (poolModifyPositionUpdateResult f evm id key p.delta fee0 fee1) := by
  let fa := poolModifyUpdateAliasFrame f id key
  have ha : ExecStmt config f evm poolModifyFunction.body[15]! (.ok fa evm) :=
    ExecStmt.letStorage (resolveStorageAlias hp)
  have hca : PoolModifyContext fa id p := hc.insert poolModifyUpdateAlias _ (by decide)
  have h0a : fa.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)) :=
    (store_get_ne _ _ (by decide : (poolModifyUpdateAlias == "feeGrowthInside0X128") = false)).trans h0
  have h1a : fa.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)) :=
    (store_get_ne _ _ (by decide : (poolModifyUpdateAlias == "feeGrowthInside1X128") = false)).trans h1
  have hcall := positionUpdateCall (f := fa) (evm := evm) hca.contract
    (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hca.liquidityDelta)
    (evalLocalValue h0a) (evalLocalValue h1a) "__c8"
  apply ExecBlock.consNormal ha
  apply execBlock_continueCall hcall
  intro cf post values hret
  rw [positionUpdateReturnedValues hret]
  exact letTuplePair (cfg := config) (source := "__c8") (name0 := "feesOwed0") (name1 := "feesOwed1")
    (store_get_self _ _ _) (by decide)

end Benchmarks.UniswapV4PoolManager
