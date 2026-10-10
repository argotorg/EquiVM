import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFees
import Benchmarks.UniswapV4PoolManager.TickLiquidityWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickLiquidityStore (evm : EVM.State) (id : UInt256) (tick : Int) (gross : UInt256) (net : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tickSlot id tick)
    (tickLiquidityPacked gross (EVM.wordOfInt net))
def poolUpdateTickTailResult (f : Frame) (evm : EVM.State) (id packed gross : UInt256)
    (tick delta : Int) (upper flipped : Bool) : ExecResult :=
  if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta upper) then
    if evm.executionEnv.perm = false then .staticViolation else
      .returned f (tickLiquidityStore evm id tick gross (tickNetAfter packed delta upper))
        (some [.bool flipped, .int (Int.ofNat gross.toNat)])
  else .reverted

theorem poolUpdateTickTail {f : Frame} {evm : EVM.State} {id packed gross : UInt256}
    {tick delta : Int} {upper flipped : Bool}
    (hi : f.locals.get? "info" = some (tickRefValue id tick))
    (hb : f.locals.get? "liquidityNetBefore" = some (.int (EVM.signed (tickNetWord packed))))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta))
    (hu : f.locals.get? "upper" = some (.bool upper))
    (hg : f.locals.get? "liquidityGrossAfter" = some (.int (Int.ofNat gross.toNat)))
    (hflip : f.locals.get? "flipped" = some (.bool flipped)) :
    ∃ f', ExecFuncBody config f evm (poolUpdateTickFunction.body.drop 10)
      (poolUpdateTickTailResult f' evm id packed gross tick delta upper flipped) := by
  have hcheck := tickNetAfter_eval (evalLocalValue (cfg := config) (evm := evm) hb)
    (evalLocalValue hd) (evalLocalValue hu)
  by_cases hfit : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta upper)
  · simp only [if_pos hfit] at hcheck
    let f1 : Frame := {f with locals := f.locals.insert "liquidityNet" (.int (tickNetAfter packed delta upper))}
    have hlet : ExecStmt config f evm poolUpdateTickFunction.body[10]! (.ok f1 evm) := ExecStmt.letDecl hcheck
    have hnet : EVM.signed (EVM.wordOfInt (tickNetAfter packed delta upper)) = tickNetAfter packed delta upper := by
      apply signed_wordOfInt
      have hl := hfit.1
      have hh := hfit.2
      change -(2^127 : Int) ≤ tickNetAfter packed delta upper at hl
      change tickNetAfter packed delta upper < (2^127 : Int) at hh
      constructor
      · change -(2^255 : Int) ≤ tickNetAfter packed delta upper; omega
      · change tickNetAfter packed delta upper < (2^255 : Int); omega
    have hval : evalExpr? config f1 evm (.binary (.bitOr (.uint ⟨256, by decide⟩))
        (.cast (.var "liquidityGrossAfter") (.elem (.int (.uint ⟨256, by decide⟩))))
        (.binary (.shl (.uint ⟨256, by decide⟩))
          (.cast (.cast (.var "liquidityNet") (.elem (.int (.uint ⟨128, by decide⟩))))
            (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 128))) =
        .ok (.int (Int.ofNat (tickLiquidityPacked gross (EVM.wordOfInt (tickNetAfter packed delta upper))).toNat)) := by
      apply tickLiquidityPacked_eval (evalLocalValue
        ((store_get_ne _ _ (by decide : ("liquidityNet" == "liquidityGrossAfter") = false)).trans hg))
      rw [hnet]
      exact evalLocalValue (store_get_self _ _ _)
    have hwrite := tickField_write (f := f1) (evm := evm)
      ((store_get_ne _ _ (by decide : ("liquidityNet" == "info") = false)).trans hi)
      .liquidityPacked (tickLiquidityPacked gross (EVM.wordOfInt (tickNetAfter packed delta upper)))
    refine ⟨f1, ?_⟩
    simp only [poolUpdateTickTailResult, if_pos hfit]
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact .execBlockStatic (ExecBlock.consNormal hlet (ExecBlock.consStatic (ExecStmt.assignStatic hval hwrite hp)))
    · rw [if_neg hp]
      refine .execBlockRet (ExecBlock.consNormal hlet (ExecBlock.consNormal
        (ExecStmt.assign hval hwrite) (ExecBlock.consReturn (ExecStmt.return ?_))))
      have hf1 : f1.locals.get? "flipped" = some (.bool flipped) :=
        (store_get_ne _ _ (by decide : ("liquidityNet" == "flipped") = false)).trans hflip
      have hg1 : f1.locals.get? "liquidityGrossAfter" = some (.int (Int.ofNat gross.toNat)) :=
        (store_get_ne _ _ (by decide : ("liquidityNet" == "liquidityGrossAfter") = false)).trans hg
      simp only [evalExprs?, evalLocalValue hf1, evalLocalValue hg1, bind, EvalResult.bind, pure]
  · simp only [if_neg hfit] at hcheck
    exact ⟨f, by simpa only [poolUpdateTickTailResult, if_neg hfit] using
      (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.letDeclRevert hcheck)) :
        ExecFuncBody config f evm (poolUpdateTickFunction.body.drop 10) .reverted)⟩

end Benchmarks.UniswapV4PoolManager
