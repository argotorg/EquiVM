import Benchmarks.UniswapV4PoolManager.TickScanBranchSource
import Benchmarks.UniswapV4PoolManager.TickCompressSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanBody {f : Frame} {evm : EVM.State} {id tick spacing : UInt256} (lte : Bool)
    (hf : f.contract = contract) (htick : (EVM.signed tick).natAbs < 2^255)
    (href : f.locals.get? "self" = some (tickBitmapRefValue id))
    (ht : f.locals.get? "tick" = some (.int (EVM.signed tick)))
    (hs : f.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)))
    (hl : f.locals.get? "lte" = some (.bool lte)) :
    ∃ f', ExecFuncBody config f evm tickScanFunction.body
      (.returned f' evm (some (tickScanValues evm id tick spacing lte))) := by
  let compressed := tickCompressRaw tick spacing
  let f0 := valueLocal f "compressed" (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed)))
  have hcall : ExecStmt config f evm
      (.internalCall "TickBitmap_compress" [.var "tick", .var "tickSpacing"] "compressed") (.ok f0 evm) := by
    have h := tickCompressCall hf (evalLocalValue (cfg := config) (evm := evm) ht) (evalLocalValue hs) "compressed"
    rw [tickCompressWord_value htick] at h
    exact h
  have hf0 : f0.contract = contract := (valueLocal_contract _ _ _).trans hf
  have hc0 : f0.locals.get? "compressed" =
      some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))) := store_get_self _ _ _
  have hs0 : f0.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) :=
    (store_get_ne _ _ (by decide : ("compressed" == "tickSpacing") = false)).trans hs
  have hl0 : f0.locals.get? "lte" = some (.bool lte) :=
    (store_get_ne _ _ (by decide : ("compressed" == "lte") = false)).trans hl
  have hr0 : f0.locals.get? "self" = some (tickBitmapRefValue id) :=
    (store_get_ne _ _ (by decide : ("compressed" == "self") = false)).trans href
  cases lte with
  | true =>
    obtain ⟨f', hbranch⟩ := tickScanBranchSource (evm := evm) true hf0 hc0 hs0 hr0
    refine ⟨f', ?_⟩
    rw [tickScan_body_eq]
    exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hcall
      (ExecBlock.consReturn (ExecStmt.iteTrue (evalLocalValue hl0) hbranch)))
  | false =>
    let f1 := valueLocal f0 "compressed"
      (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) (compressed+UInt256.ofNat 1))))
    have he := evalSigned24Add (evalLocalValue (cfg := config) (evm := evm) hc0)
      (show evalExpr? config f0 evm (.intLit 1) = .ok (.int (EVM.signed (UInt256.ofNat 1))) by
        simp only [evalExpr?, pure]; rfl)
    rw [signextend24_add_left] at he
    have hinc : ExecStmt config f0 evm (.assign .localVar {base := "compressed"} tickScanIncrementExpr)
        (.ok f1 evm) := ExecStmt.assign he (assignLocalValue hc0)
    have hf1 : f1.contract = contract := (valueLocal_contract _ _ _).trans hf0
    have hc1 : f1.locals.get? "compressed" =
        some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) (compressed+UInt256.ofNat 1)))) :=
      store_get_self _ _ _
    have hs1 : f1.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) :=
      (store_get_ne _ _ (by decide : ("compressed" == "tickSpacing") = false)).trans hs0
    have hr1 : f1.locals.get? "self" = some (tickBitmapRefValue id) :=
      (store_get_ne _ _ (by decide : ("compressed" == "self") = false)).trans hr0
    obtain ⟨f', hbranch⟩ := tickScanBranchSource (evm := evm) false hf1 hc1 hs1 hr1
    refine ⟨f', ?_⟩
    rw [tickScan_body_eq]
    exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hcall
      (ExecBlock.consReturn (ExecStmt.iteFalse (evalLocalValue hl0) (ExecBlock.consNormal hinc hbranch))))

theorem tickScanCall {f : Frame} {evm : EVM.State} {id tick spacing : UInt256} {er et es el : Expr}
    (lte : Bool) (hf : f.contract = contract) (htick : (EVM.signed tick).natAbs < 2^255)
    (href : evalExpr? config f evm er = .ok (tickBitmapRefValue id))
    (ht : evalExpr? config f evm et = .ok (.int (EVM.signed tick)))
    (hs : evalExpr? config f evm es = .ok (.int (EVM.signed spacing)))
    (hl : evalExpr? config f evm el = .ok (.bool lte)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "TickBitmap_nextInitializedTickWithinOneWord" [er, et, es, el] ret)
      (.ok (valueLocal f ret (.tuple (tickScanValues evm id tick spacing lte))) evm) := by
  let fc : Frame := {f with locals :=
    (((((∅ : Store).insert "lte" (.bool lte)).insert "tickSpacing" (.int (EVM.signed spacing))).insert
      "tick" (.int (EVM.signed tick))).insert "self" (tickBitmapRefValue id))}
  have hr : fc.locals.get? "self" = some (tickBitmapRefValue id) := store_get_self _ _ _
  have ht' : fc.locals.get? "tick" = some (.int (EVM.signed tick)) :=
    (store_get_ne _ _ (by decide : ("self" == "tick") = false)).trans (store_get_self _ _ _)
  have hs' : fc.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) :=
    (store_get_ne2 _ _ _ (by decide : ("tick" == "tickSpacing") = false)
      (by decide : ("self" == "tickSpacing") = false)).trans (store_get_self _ _ _)
  have hl' : fc.locals.get? "lte" = some (.bool lte) :=
    (store_get_ne _ _ (by decide : ("self" == "lte") = false)).trans
      ((store_get_ne2 _ _ _ (by decide : ("tickSpacing" == "lte") = false)
        (by decide : ("tick" == "lte") = false)).trans (store_get_self _ _ _))
  obtain ⟨f', hb⟩ := tickScanBody (evm := evm) lte (f := fc) hf htick hr ht' hs' hl'
  exact internalCallFunctionReturn
    (argVals := [tickBitmapRefValue id, .int (EVM.signed tick), .int (EVM.signed spacing), .bool lte])
    (value := some (tickScanValues evm id tick spacing lte))
    (by simp only [evalExprs?, href, ht, hs, hl, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickScan_lookup) rfl hb

end Benchmarks.UniswapV4PoolManager
