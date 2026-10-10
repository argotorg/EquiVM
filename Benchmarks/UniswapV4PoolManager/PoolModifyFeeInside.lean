import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.PoolFeeInsideSource
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.TupleLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFeeInsideAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.10"
def poolModifyFeeInsideFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : Frame :=
  let fa := {f with locals := f.locals.insert poolModifyFeeInsideAlias (poolRefValue id)}
  let fc := {fa with locals := fa.locals.insert "__c6" (.tuple (poolFeeInsideValues evm id
    (EVM.signed p.lower) (EVM.signed p.upper)))}
  wordLocal (wordLocal fc "feeGrowthInside0X128"
    (poolFeeInsideWord evm id (EVM.signed p.lower) (EVM.signed p.upper) false)) "feeGrowthInside1X128"
    (poolFeeInsideWord evm id (EVM.signed p.lower) (EVM.signed p.upper) true)

theorem poolModifyFeeInside {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 8).take 4)
      (.ok (poolModifyFeeInsideFrame f evm id p) evm) := by
  let fa := {f with locals := f.locals.insert poolModifyFeeInsideAlias (poolRefValue id)}
  let fc := {fa with locals := fa.locals.insert "__c6" (.tuple (poolFeeInsideValues evm id
    (EVM.signed p.lower) (EVM.signed p.upper)))}
  have ha : ExecStmt config f evm poolModifyFunction.body[8]! (.ok fa evm) :=
    ExecStmt.letStorage (resolveStorageAlias hc.self)
  have hca : PoolModifyContext fa id p := hc.insert poolModifyFeeInsideAlias _ (by decide)
  have hcall := poolFeeInsideCall (f := fa) (evm := evm) hca.contract
    (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hca.lower) (evalLocalValue hca.upper) "__c6"
  have hpair := letTuplePair (cfg := config) (f := fc) (evm := evm) (source := "__c6")
    (name0 := "feeGrowthInside0X128") (name1 := "feeGrowthInside1X128")
    (ty0 := some abiUInt256) (ty1 := some abiUInt256) (store_get_self _ _ _) (by decide)
  exact ExecBlock.consNormal ha (ExecBlock.consNormal hcall hpair)

theorem poolModifyFeeInsideFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (evm : State) :
    PoolModifyContext (poolModifyFeeInsideFrame f evm id p) id p :=
  (((hc.insert poolModifyFeeInsideAlias _ (by decide)).insert "__c6" _ (by decide)).insert
    "feeGrowthInside0X128" _ (by decide)).insert "feeGrowthInside1X128" _ (by decide)

theorem poolModifyFeeInsideFrame_get (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (name : Ident) (ha : (poolModifyFeeInsideAlias == name) = false) (hc : ("__c6" == name) = false)
    (h0 : ("feeGrowthInside0X128" == name) = false) (h1 : ("feeGrowthInside1X128" == name) = false) :
    (poolModifyFeeInsideFrame f evm id p).locals.get? name = f.locals.get? name :=
  store_get_ne4 _ _ _ _ _ ha hc h0 h1

end Benchmarks.UniswapV4PoolManager
