import Benchmarks.UniswapV4PoolManager.PoolUpdateTickPrelude
import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFinishSource
import Benchmarks.UniswapV4PoolManager.TickGrossWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolUpdateTickResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick delta : Int) (upper : Bool) : ExecResult :=
  let packed := tickFieldWord evm id tick .liquidityPacked
  if liquidityAddFits (tickGrossWord packed) delta then
    poolUpdateTickFinishResult f evm id packed (EVM.wordOfInt (tickGrossAfterInt packed delta))
      tick delta upper (tickFlipped packed delta)
  else .reverted

theorem poolUpdateTickBody {f : Frame} {evm : EVM.State} {id : UInt256} {tick delta : Int} {upper : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta))
    (hu : f.locals.get? "upper" = some (.bool upper)) :
    ∃ f', ExecFuncBody config f evm poolUpdateTickFunction.body (poolUpdateTickResult f' evm id tick delta upper) := by
  let packed := tickFieldWord evm id tick .liquidityPacked
  let f6 := poolUpdateTickPreludeFrame f evm id tick
  have hpre := poolUpdateTickPrelude (evm := evm) hs ht
  have hg6 : f6.locals.get? "liquidityGrossBefore" = some (.int (Int.ofNat (tickGrossWord packed).toNat)) :=
    (store_get_ne _ _ (by decide : ("liquidityNetBefore" == "liquidityGrossBefore") = false)).trans (store_get_self _ _ _)
  have hd6 : f6.locals.get? "liquidityDelta" = some (.int delta) := by
    simpa [f6, poolUpdateTickPreludeFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hd
  have hf6 : f6.contract = contract := by
    dsimp only [f6, poolUpdateTickPreludeFrame]
    exact hf
  have hcall := liquidityAddCall (f := f6) (evm := evm) (x := tickGrossWord packed) (y := delta)
    (ex := .var "liquidityGrossBefore") (ey := .var "liquidityDelta")
    hf6 (evalLocalValue hg6) (evalLocalValue hd6) "__c0"
  by_cases hfit : liquidityAddFits (tickGrossWord packed) delta
  · rw [if_pos hfit] at hcall
    let after := tickGrossAfterInt packed delta
    let f7 : Frame := {f6 with locals := f6.locals.insert "__c0" (.int after)}
    let f8 : Frame := {f7 with locals := f7.locals.insert "liquidityGrossAfter" (.int after)}
    let f9 : Frame := {f8 with locals := f8.locals.insert "flipped" (.bool (tickFlipped packed delta))}
    have hafter : Int.ofNat (EVM.wordOfInt after).toNat = after := tickGrossAfter_value hfit
    have hassign : ExecStmt config f7 evm poolUpdateTickFunction.body[7]! (.ok f8 evm) :=
      ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalValue
        ((store_get_ne5 _ _ _ _ _ _ (by decide : ("info" == "liquidityGrossAfter") = false)
          (by decide : ("liquidityPacked" == "liquidityGrossAfter") = false)
          (by decide : ("liquidityGrossBefore" == "liquidityGrossAfter") = false)
          (by decide : ("liquidityNetBefore" == "liquidityGrossAfter") = false)
          (by decide : ("__c0" == "liquidityGrossAfter") = false)).trans (store_get_self _ _ _)))
    have hflipExpr : evalExpr? config f8 evm (.binary .ne
        (.binary .eq (.var "liquidityGrossAfter") (.intLit 0))
        (.binary .eq (.var "liquidityGrossBefore") (.intLit 0))) = .ok (.bool (tickFlipped packed delta)) := by
      have hga : evalExpr? config f8 evm (.binary .eq (.var "liquidityGrossAfter") (.intLit 0)) =
          .ok (.bool (decide (after = 0))) := evalIntEq (evalLocalValue (store_get_self _ _ _))
        (by simp only [evalExpr?, pure])
      have hgb := evalIntEq (evalLocalValue (cfg := config) (f := f8) (evm := evm)
        ((store_get_ne2 _ _ _ (by decide : ("__c0" == "liquidityGrossBefore") = false)
          (by decide : ("liquidityGrossAfter" == "liquidityGrossBefore") = false)).trans hg6))
        (show evalExpr? config f8 evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
      rw [evalExpr_binary_nonshort (by decide) (by decide), hga, hgb]
      simp only [bind, EvalResult.bind, evalBinaryOp?, BEq.beq, Value.bool.injEq, tickFlipped, after]
      cases decide (tickGrossAfterInt packed delta = 0) <;>
        cases decide (Int.ofNat (tickGrossWord packed).toNat = 0) <;> rfl
    have hflip : ExecStmt config f8 evm poolUpdateTickFunction.body[8]! (.ok f9 evm) :=
      ExecStmt.assign hflipExpr (assignLocalValue
        ((store_get_ne2 _ _ _ (by decide : ("__c0" == "flipped") = false)
          (by decide : ("liquidityGrossAfter" == "flipped") = false)).trans
        ((store_get_ne5 _ _ _ _ _ _ (by decide : ("liquidityGrossAfter" == "flipped") = false)
          (by decide : ("info" == "flipped") = false) (by decide : ("liquidityPacked" == "flipped") = false)
          (by decide : ("liquidityGrossBefore" == "flipped") = false)
          (by decide : ("liquidityNetBefore" == "flipped") = false)).trans (store_get_self _ _ _))))
    have hp : ExecBlock config f evm (poolUpdateTickFunction.body.take 9) (.ok f9 evm) :=
      execBlock_append hpre (ExecBlock.consNormal hcall (ExecBlock.consNormal hassign
        (ExecBlock.consNormal hflip ExecBlock.nil)))
    have hs9 : f9.locals.get? "self" = some (poolRefValue id) := by
      simpa [f9, f8, f7, f6, poolUpdateTickPreludeFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hs
    have ht9 : f9.locals.get? "tick" = some (.int tick) := by
      simpa [f9, f8, f7, f6, poolUpdateTickPreludeFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ht
    have hd9 : f9.locals.get? "liquidityDelta" = some (.int delta) := by
      simpa [f9, f8, f7, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hd6
    have hu9 : f9.locals.get? "upper" = some (.bool upper) := by
      simpa [f9, f8, f7, f6, poolUpdateTickPreludeFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hu
    have hf9 : f9.contract = contract := by dsimp only [f9, f8, f7]; exact hf6
    obtain ⟨f', hfinish⟩ := poolUpdateTickFinishSource (f := f9) (evm := evm)
      (id := id) (packed := packed) (gross := EVM.wordOfInt after) hf9 hs9
      ((store_get_ne3 _ _ _ _ (by decide : ("__c0" == "info") = false)
        (by decide : ("liquidityGrossAfter" == "info") = false) (by decide : ("flipped" == "info") = false)).trans
        ((store_get_ne3 _ _ _ _ (by decide : ("liquidityPacked" == "info") = false)
          (by decide : ("liquidityGrossBefore" == "info") = false)
          (by decide : ("liquidityNetBefore" == "info") = false)).trans (store_get_self _ _ _))) ht9
      ((store_get_ne3 _ _ _ _ (by decide : ("__c0" == "liquidityNetBefore") = false)
        (by decide : ("liquidityGrossAfter" == "liquidityNetBefore") = false)
        (by decide : ("flipped" == "liquidityNetBefore") = false)).trans (store_get_self _ _ _))
      hd9 hu9 (by rw [hafter]; exact store_get_ne _ _ (by decide) |>.trans (store_get_self _ _ _))
      ((store_get_ne3 _ _ _ _ (by decide : ("__c0" == "liquidityGrossBefore") = false)
        (by decide : ("liquidityGrossAfter" == "liquidityGrossBefore") = false)
        (by decide : ("flipped" == "liquidityGrossBefore") = false)).trans hg6)
      (store_get_self _ _ _)
    refine ⟨f', ?_⟩
    have hfit' := hfit
    dsimp only [packed] at hfit'
    simp only [poolUpdateTickResult, if_pos hfit']
    exact execFuncBody_prepend hp hfinish
  · rw [if_neg hfit] at hcall
    refine ⟨f6, ?_⟩
    have hfit' := hfit
    dsimp only [packed] at hfit'
    simp only [poolUpdateTickResult, if_neg hfit']
    exact execFuncBody_prepend hpre (.execBlockRevert (ExecBlock.consRevert hcall))

end Benchmarks.UniswapV4PoolManager
