import Benchmarks.UniswapV4PoolManager.PoolLiquidityStorage
import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.LiquidityAddWords
import Benchmarks.UniswapV4PoolManager.LiquidityAddSource
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyLiquidityBlock : List Stmt :=
  [.internalCall "LiquidityMath_addDelta"
    [.storage {base := "self", steps := [.field "liquidity"]}, .var "liquidityDelta"] "__c28",
   .assign .storage {base := "self", steps := [.field "liquidity"]} (.var "__c28")]
def poolModifyLiquidityResult (f : Frame) (evm : State) (id : UInt256) (delta : Int) : ExecResult :=
  if liquidityAddFits (poolLiquidityWord evm id) delta then
    if evm.executionEnv.perm = false then .staticViolation else
      .ok (wordLocal f "__c28" (liquidityAddResultWord (poolLiquidityWord evm id) delta))
        (poolLiquidityStore evm id (liquidityAddResultWord (poolLiquidityWord evm id) delta))
  else .reverted

theorem poolModifyLiquidity {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) :
    ExecBlock config f evm poolModifyLiquidityBlock (poolModifyLiquidityResult f evm id p.delta) := by
  have hcall := liquidityAddCall (f := f) (evm := evm) hc.contract (poolLiquidity_read hc.self)
    (evalLocalValue hc.liquidityDelta) "__c28"
  by_cases hfit : liquidityAddFits (poolLiquidityWord evm id) p.delta
  · rw [if_pos hfit, ← liquidityAddResultWord_value hfit] at hcall
    let f1 := wordLocal f "__c28" (liquidityAddResultWord (poolLiquidityWord evm id) p.delta)
    have hs1 : f1.locals.get? "self" = some (poolRefValue id) :=
      (store_get_ne _ _ (by decide : ("__c28" == "self") = false)).trans hc.self
    have hw := poolLiquidity_write (f := f1) (evm := evm) hs1 (liquidityAddResultWord_bound hfit)
    rw [poolModifyLiquidityResult, if_pos hfit]
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact ExecBlock.consNormal hcall (ExecBlock.consStatic (ExecStmt.assignStatic wordLocal_eval hw hp))
    · rw [if_neg hp]
      exact ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign wordLocal_eval hw))
  · rw [poolModifyLiquidityResult, if_neg hfit]
    exact ExecBlock.consRevert (by simpa only [if_neg hfit] using hcall)

theorem poolModifyLiquidityResult_normal {f f' : Frame} {evm post : State} {id : UInt256} {delta : Int}
    (h : poolModifyLiquidityResult f evm id delta = .ok f' post) :
    f' = wordLocal f "__c28" (liquidityAddResultWord (poolLiquidityWord evm id) delta) ∧
    post = poolLiquidityStore evm id (liquidityAddResultWord (poolLiquidityWord evm id) delta) := by
  unfold poolModifyLiquidityResult at h
  split_ifs at h <;> cases h
  exact ⟨rfl, rfl⟩

end Benchmarks.UniswapV4PoolManager
