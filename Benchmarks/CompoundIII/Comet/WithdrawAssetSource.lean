import Benchmarks.CompoundIII.Comet.WithdrawAssetModel
import Benchmarks.CompoundIII.Comet.WithdrawBaseSource
import Benchmarks.CompoundIII.Comet.WithdrawCollateralSource
import Benchmarks.CompoundIII.Comet.SafeUintSource
import Benchmarks.CompoundIII.Comet.AssetDispatchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawAsset_source {v src recipient asset amount evm result}
    (ht : WithdrawAssetTrace v src recipient asset amount evm result) (frame : Frame)
    (hf : WithdrawAssetArgs frame v src recipient asset amount) :
    ExecStmt config frame evm withdrawAssetStmt
      (internalStmtResult (withdrawAssetReady frame v evm src asset amount)
        (withdrawAssetReturn v asset) result) := by
  have hs : evalExpr? config frame evm (.var "src") = .ok (.address src) := by
    simp only [evalExpr?, hf.src, EvalResult.ofOption]
  have hto : evalExpr? config frame evm (.var "to") = .ok (.address recipient) := by
    simp only [evalExpr?, hf.recipient, EvalResult.ofOption]
  have ham : evalExpr? config frame evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, hf.amount, EvalResult.ofOption]
  have ha : evalExpr? config frame evm (.var "asset") = .ok (.address asset) := by
    simp only [evalExpr?, hf.asset, EvalResult.ofOption]
  have hb : evalExpr? config frame evm (.binary .eq (.var "asset") (.immutable "baseToken")) =
      .ok (.bool (decide (asset = v.baseToken))) :=
    evalExpr_address_eq ha (by
      simp only [evalExpr?, hf.immutables, immStore_get_baseToken, EvalResult.ofOption])
  have hm : evalExpr? config frame evm (.binary .eq (.var "amount") (.intLit (2^256-1))) =
      .ok (.bool (decide (amount = UInt256.lnot ⟨0⟩))) := evalExpr_uint256_max ham
  cases ht with
  | base hb' hm' ht =>
    simp only [withdrawAssetReady, withdrawAssetReturn, hb', if_true, hm', if_false]
    apply ExecStmt.iteTrue (hb.trans (by rw [decide_eq_true hb']))
    exact ExecBlock.consNormal (ExecStmt.iteFalse (hm.trans (by rw [decide_eq_false hm'])) .nil)
      (execBlock_singleton (withdrawBase_call ht frame _ _ _ "__c4"
        hf.contract hf.immutables hs hto ham))
  | balanceFailed hb' hm' hv =>
    exact ExecStmt.iteTrue (hb.trans (by rw [decide_eq_true hb']))
      (ExecBlock.consRevert (ExecStmt.iteTrue (hm.trans (by rw [decide_eq_true hm']))
        (ExecBlock.consRevert (balance_call_revert v frame evm src _ "__c3"
          hf.contract hf.immutables hs hv))))
  | allBase hb' hm' hv ht =>
    simp only [withdrawAssetReady, withdrawAssetReturn, hb', if_true, hm']
    let val := withdrawBalanceWord v evm src
    let read : Frame := { frame with locals := frame.locals.insert "__c3" (.int val.toNat) }
    let ready : Frame := { read with locals := read.locals.insert "amount" (.int val.toNat) }
    have hread := balance_call_ok v frame evm src (.var "src") "__c3"
      hf.contract hf.immutables hs hv
    have he : evalExpr? config read evm (.var "__c3") = .ok (.int val.toNat) := by
      simp only [evalExpr?, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hassign : ExecStmt config read evm (.assign .localVar ⟨"amount", []⟩ (.var "__c3"))
        (.ok ready evm) := ExecStmt.assign he (assignLocalFrame (by
      simpa only [read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hf.amount))
    have hcall := withdrawBase_call ht ready (.var "src") (.var "to") (.var "amount") "__c4"
      hf.contract hf.immutables
      (by simp only [evalExpr?, ready, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "src") = _
          rw [hf.src]; rfl)
      (by simp only [evalExpr?, ready, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "to") = _
          rw [hf.recipient]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption]; rfl)
    exact ExecStmt.iteTrue (hb.trans (by rw [decide_eq_true hb']))
      (ExecBlock.consNormal (ExecStmt.iteTrue (hm.trans (by rw [decide_eq_true hm']))
        (ExecBlock.consNormal hread (execBlock_singleton hassign))) (execBlock_singleton hcall))
  | tooLarge hb' hw =>
    have hc := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup frame evm amount
      (.var "amount") "__c5" hf.contract ham
    simp only [if_neg hw] at hc
    exact ExecStmt.iteFalse (hb.trans (by rw [decide_eq_false hb'])) (ExecBlock.consRevert hc)
  | collateral hb' hw ht =>
    simp only [withdrawAssetReady, withdrawAssetReturn, if_neg hb']
    let ready : Frame := { frame with locals := frame.locals.insert "__c5" (.int amount.toNat) }
    have hc := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup frame evm amount
      (.var "amount") "__c5" hf.contract ham
    simp only [if_pos hw] at hc
    have hcall := withdrawCollateral_call ht ready (.var "src") (.var "to") (.var "asset")
      (.var "__c5") "__c6" hf.contract hf.immutables
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "src") = _
          rw [hf.src]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "to") = _
          rw [hf.recipient]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "asset") = _
          rw [hf.asset]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption]; rfl)
    exact ExecStmt.iteFalse (hb.trans (by rw [decide_eq_false hb']))
      (ExecBlock.consNormal hc (execBlock_singleton hcall))

end Benchmarks.CompoundIII.Comet
