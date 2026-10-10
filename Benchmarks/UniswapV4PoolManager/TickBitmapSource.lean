import Benchmarks.UniswapV4PoolManager.TickBitmapPrelude
import Benchmarks.UniswapV4PoolManager.TickBitmapStorage
import Benchmarks.UniswapV4PoolManager.WordXorSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickBitmapPost (evm : EVM.State) (id : UInt256) (tick spacing : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tickBitmapSlot id (tickBitmapPosition tick spacing))
    (UInt256.xor (tickBitmapWord evm id (tickBitmapPosition tick spacing))
      (tickBitmapMask (tickBitmapCompressed tick spacing)))
def tickBitmapResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick spacing : Int) : ExecResult :=
  if tickBitmapAligned tick spacing then
    if evm.executionEnv.perm = false then .staticViolation else .returned f (tickBitmapPost evm id tick spacing) none
  else .reverted

theorem tickBitmapTail {f : Frame} {evm : EVM.State} {id : UInt256} {tick spacing : Int}
    (hs : f.locals.get? "self" = some (tickBitmapRefValue id))
    (hc : f.locals.get? "compressed" = some (.int (tickBitmapCompressed tick spacing)))
    (ht : tick.natAbs ≤ 887272) :
    ∃ f', ExecFuncBody config f evm (tickBitmapFunction.body.drop 2)
      (if evm.executionEnv.perm = false then .staticViolation else .returned f' (tickBitmapPost evm id tick spacing) none) := by
  let f1 : Frame := {f with locals := f.locals.insert "wordPos" (.int (tickBitmapPosition tick spacing))}
  let mask := tickBitmapMask (tickBitmapCompressed tick spacing)
  let f2 : Frame := {f1 with locals := f1.locals.insert "mask" (.int (Int.ofNat mask.toNat))}
  have hp : ExecStmt config f evm tickBitmapFunction.body[2]! (.ok f1 evm) :=
    ExecStmt.letDecl (tickBitmapPosition_eval ht (evalLocalValue hc))
  have hm : ExecStmt config f1 evm tickBitmapFunction.body[3]! (.ok f2 evm) :=
    ExecStmt.letDecl (tickBitmapMask_eval (tickBitmapCompressed_int256 spacing ht)
      (evalLocalValue ((store_get_ne _ _ (by decide : ("wordPos" == "compressed") = false)).trans hc)))
  have hs2 : f2.locals.get? "self" = some (tickBitmapRefValue id) :=
    (store_get_ne2 _ _ _ (by decide : ("wordPos" == "self") = false)
      (by decide : ("mask" == "self") = false)).trans hs
  have hp2 : evalExpr? config f2 evm (.var "wordPos") = .ok (.int (tickBitmapPosition tick spacing)) :=
    evalLocalValue ((store_get_ne _ _ (by decide : ("mask" == "wordPos") = false)).trans (store_get_self _ _ _))
  have hv := evalWordXor (tickBitmapWord_read hs2 hp2) (evalLocalValue (store_get_self _ _ _))
  have hw := tickBitmapWord_write hs2 hp2
    (UInt256.xor (tickBitmapWord evm id (tickBitmapPosition tick spacing)) mask)
  refine ⟨f2, ?_⟩
  by_cases hperm : evm.executionEnv.perm = false
  · rw [if_pos hperm]
    exact .execBlockStatic (ExecBlock.consNormal hp (ExecBlock.consNormal hm
      (ExecBlock.consStatic (ExecStmt.assignStatic hv hw hperm))))
  · rw [if_neg hperm]
    exact .execBlockOK (ExecBlock.consNormal hp (ExecBlock.consNormal hm
      (execBlock_singleton (ExecStmt.assign hv hw))))

theorem tickBitmapBody {f : Frame} {evm : EVM.State} {id : UInt256} {tick spacing : Int}
    (hs : f.locals.get? "self" = some (tickBitmapRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick))
    (hp : f.locals.get? "tickSpacing" = some (.int spacing)) (hb : tick.natAbs ≤ 887272) :
    ∃ f', ExecFuncBody config f evm tickBitmapFunction.body (tickBitmapResult f' evm id tick spacing) := by
  have hpre := tickBitmapPrelude (evm := evm) ht hp
  by_cases ha : tickBitmapAligned tick spacing
  · rw [if_pos ha] at hpre
    obtain ⟨f', htail⟩ := tickBitmapTail (evm := evm)
      ((tickBitmapPreludeFrame_get (by decide : ("compressed" == "self") = false)).trans hs)
      (tickBitmapPreludeFrame_compressed f tick spacing) hb
    exact ⟨f', by simpa only [tickBitmapResult, if_pos ha] using execFuncBody_prepend hpre htail⟩
  · rw [if_neg ha] at hpre
    refine ⟨f, ?_⟩
    rw [tickBitmapResult, if_neg ha]
    exact .execBlockRevert (execBlock_reverted_append (s2 := tickBitmapFunction.body.drop 2) hpre)

theorem tickBitmapCall {f : Frame} {evm : EVM.State} {id : UInt256} {tick spacing : Int}
    {es et ep : Expr} (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (tickBitmapRefValue id))
    (ht : evalExpr? config f evm et = .ok (.int tick))
    (hp : evalExpr? config f evm ep = .ok (.int spacing)) (hb : tick.natAbs ≤ 887272) (ret : Ident) :
    ExecStmt config f evm (.internalCall "TickBitmap_flipTick" [es, et, ep] ret)
      (resumeCallResult f ret (tickBitmapResult f evm id tick spacing)) := by
  obtain ⟨f', hbody⟩ := tickBitmapBody
    (f := {f with locals := ((((∅ : Store).insert "tickSpacing" (.int spacing)).insert "tick" (.int tick)).insert
      "self" (tickBitmapRefValue id))}) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "tick") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("tick" == "tickSpacing") = false)
      (by decide : ("self" == "tickSpacing") = false)).trans (store_get_self _ _ _)) hb
  have hcall := internalCallFunctionExec (caller := f) (name := "TickBitmap_flipTick") (retVar := ret)
    (args := [es, et, ep]) (argVals := [tickBitmapRefValue id, .int tick, .int spacing])
    (by simp only [evalExprs?, hs, ht, hp, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickBitmap_lookup) rfl hbody
  simpa only [tickBitmapResult, resumeCallResult_ite, resumeCallResult_returned,
    resumeCallResult_reverted, resumeCallResult_static] using hcall

end Benchmarks.UniswapV4PoolManager
