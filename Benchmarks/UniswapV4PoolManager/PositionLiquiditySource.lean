import Benchmarks.UniswapV4PoolManager.PositionFeesSource
import Benchmarks.UniswapV4PoolManager.LiquidityAddWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionChangeFrame (f : Frame) (liquidity : UInt256) (delta : Int) : Frame :=
  if delta = 0 then f else wordLocal f "__c0" (liquidityAddResultWord liquidity delta)
def positionChangeState (evm : EVM.State) (id key liquidity : UInt256) (delta : Int) : EVM.State :=
  if delta = 0 then evm else positionLiquidityStore evm id key (liquidityAddResultWord liquidity delta)
def positionChangeResult (f : Frame) (evm : EVM.State) (id key liquidity : UInt256) (delta : Int) : ExecResult :=
  if delta = 0 then
    if liquidity = ⟨0⟩ then .reverted else .ok f evm
  else if liquidityAddFits liquidity delta then
    if evm.executionEnv.perm = false then .staticViolation else
      .ok (positionChangeFrame f liquidity delta) (positionChangeState evm id key liquidity delta)
  else .reverted

theorem positionChangeFrame_get (f : Frame) (liquidity : UInt256) (delta : Int) (name : Ident)
    (hn : ("__c0" == name) = false) :
    (positionChangeFrame f liquidity delta).locals.get? name = f.locals.get? name := by
  unfold positionChangeFrame
  split
  · rfl
  · rw [wordLocal_get, hn]; rfl

theorem positionChangeFrame_contract (f : Frame) (liquidity : UInt256) (delta : Int) :
    (positionChangeFrame f liquidity delta).contract = f.contract := by
  unfold positionChangeFrame
  split <;> rfl

theorem positionLiquidityBranch {f : Frame} {evm : EVM.State} {id key liquidity : UInt256} {delta : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (positionRefValue id key))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta)) :
    ExecStmt config f evm positionUpdateFunction.body[3]! (positionChangeResult f evm id key liquidity delta) := by
  have hdelta := evalIntEq (evalLocalValue (cfg := config) (f := f) (evm := evm) hd)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  unfold positionChangeResult
  by_cases hz : delta = 0
  · rw [if_pos hz]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hdelta)
    have hliq := evalEqWords (evalLocalValue (cfg := config) (f := f) (evm := evm) hl)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    by_cases hlz : liquidity = ⟨0⟩
    · rw [if_pos hlz]
      exact ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hlz] using hliq)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))
    · rw [if_neg hlz]
      exact execBlock_singleton (ExecStmt.iteFalse (by simpa only [decide_eq_false hlz] using hliq) ExecBlock.nil)
  · rw [if_neg hz]
    apply ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hdelta)
    have hcall := liquidityAddCall (f := f) (evm := evm) hf (evalLocalValue hl) (evalLocalValue hd) "__c0"
    by_cases hfit : liquidityAddFits liquidity delta
    · rw [if_pos hfit] at hcall ⊢
      let f1 := wordLocal f "__c0" (liquidityAddResultWord liquidity delta)
      rw [← liquidityAddResultWord_value hfit] at hcall
      have hs1 : f1.locals.get? "self" = some (positionRefValue id key) :=
        (store_get_ne _ _ (by decide : ("__c0" == "self") = false)).trans hs
      have hwrite := positionLiquidity_write (f := f1) (evm := evm) hs1 (liquidityAddResultWord_bound hfit)
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp]
        exact ExecBlock.consNormal hcall (ExecBlock.consStatic (ExecStmt.assignStatic wordLocal_eval hwrite hp))
      · simp only [if_neg hp, positionChangeFrame, positionChangeState, if_neg hz]
        exact ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign wordLocal_eval hwrite))
    · rw [if_neg hfit] at hcall ⊢
      exact ExecBlock.consRevert hcall

end Benchmarks.UniswapV4PoolManager
