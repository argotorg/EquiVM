import Benchmarks.UniswapV4PoolManager.PoolDonateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donatePoolAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.23"
def donatePoolAliasFrame (f : Frame) (id : UInt256) : Frame :=
  {f with locals := f.locals.insert donatePoolAlias (poolRefValue id)}
def donatePoolCallFrame (f : Frame) (delta : UInt256) : Frame :=
  {f with locals := f.locals.insert "__c6" (.int (EVM.signed delta))}
def donatePoolDeltaFrame (f : Frame) (delta : UInt256) : Frame :=
  { (donatePoolCallFrame f delta) with locals := (donatePoolCallFrame f delta).locals.insert "delta" (.int (EVM.signed delta)) }

theorem donatePoolAliasSource {f : Frame} {evm : State} {id : UInt256}
    (hp : f.locals.get? "pool" = some (poolRefValue id)) :
    ExecStmt config f evm donateTransition.body[14]! (.ok (donatePoolAliasFrame f id) evm) :=
  ExecStmt.letStorage (resolveStorageAlias hp)

theorem donatePoolDeltaSource {f : Frame} {evm : State} {delta : UInt256} {old : Value}
    (hd : f.locals.get? "delta" = some old) :
    ExecStmt config (donatePoolCallFrame f delta) evm donateTransition.body[16]!
      (.ok (donatePoolDeltaFrame f delta) evm) :=
  ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
    (assignLocalValue ((store_get_ne _ _ (by decide : ("__c6" == "delta") = false)).trans hd))


end Benchmarks.UniswapV4PoolManager
