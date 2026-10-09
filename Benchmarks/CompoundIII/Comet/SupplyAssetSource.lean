import Benchmarks.CompoundIII.Comet.SupplyAssetModel
import Benchmarks.CompoundIII.Comet.SupplyBaseSource
import Benchmarks.CompoundIII.Comet.SupplyCollateralSource
import Benchmarks.CompoundIII.Comet.SafeUintSource
import Benchmarks.CompoundIII.Comet.AssetDispatchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem supplyAsset_source {v sender dst asset amount evm result}
    (ht : SupplyAssetTrace v sender dst asset amount evm result) (frame : Frame)
    (hf : SupplyAssetArgs frame v sender dst asset amount) :
    ExecStmt config frame evm supplyAssetStmt
      (internalStmtResult (supplyAssetReady frame v evm dst asset amount)
        (supplyAssetReturn v asset) result) := by
  have hs : evalExpr? config frame evm (.var "from") = .ok (.address sender) := by
    simp only [evalExpr?, hf.sender, EvalResult.ofOption]
  have hto : evalExpr? config frame evm (.var "dst") = .ok (.address dst) := by
    simp only [evalExpr?, hf.dst, EvalResult.ofOption]
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
    simp only [supplyAssetReady, supplyAssetReturn, hb', if_true, hm', if_false]
    apply ExecStmt.iteTrue (hb.trans (by rw [decide_eq_true hb']))
    exact ExecBlock.consNormal (ExecStmt.iteFalse (hm.trans (by rw [decide_eq_false hm'])) .nil)
      (execBlock_singleton (supplyBase_call ht frame _ _ _ "__c4"
        hf.contract hf.immutables hs hto ham))
  | balanceFailed hb' hm' hv =>
    exact ExecStmt.iteTrue (hb.trans (by rw [decide_eq_true hb']))
      (ExecBlock.consRevert (ExecStmt.iteTrue (hm.trans (by rw [decide_eq_true hm']))
        (ExecBlock.consRevert (borrowBalance_call_revert v frame evm dst _ "__c3"
          hf.contract hf.immutables hto hv))))
  | allBase hb' hm' hv ht =>
    simp only [supplyAssetReady, supplyAssetReturn, hb', if_true, hm']
    let val := supplyBorrowWord v evm dst
    let read : Frame := { frame with locals := frame.locals.insert "__c3" (.int val.toNat) }
    let ready : Frame := { read with locals := read.locals.insert "amount" (.int val.toNat) }
    have hread := borrowBalance_call_ok v frame evm dst (.var "dst") "__c3"
      hf.contract hf.immutables hto hv
    have he : evalExpr? config read evm (.var "__c3") = .ok (.int val.toNat) := by
      simp only [evalExpr?, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hassign : ExecStmt config read evm (.assign .localVar ⟨"amount", []⟩ (.var "__c3"))
        (.ok ready evm) := ExecStmt.assign he (assignLocalFrame (by
      simpa only [read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hf.amount))
    have hcall := supplyBase_call ht ready (.var "from") (.var "dst") (.var "amount") "__c4"
      hf.contract hf.immutables
      (by simp only [evalExpr?, ready, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "from") = _
          rw [hf.sender]; rfl)
      (by simp only [evalExpr?, ready, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "dst") = _
          rw [hf.dst]; rfl)
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
    simp only [supplyAssetReady, supplyAssetReturn, if_neg hb']
    let ready : Frame := { frame with locals := frame.locals.insert "__c5" (.int amount.toNat) }
    have hc := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup frame evm amount
      (.var "amount") "__c5" hf.contract ham
    simp only [if_pos hw] at hc
    have hcall := supplyCollateral_call ht ready (.var "from") (.var "dst") (.var "asset")
      (.var "__c5") "__c6" hf.contract hf.immutables
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "from") = _
          rw [hf.sender]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "dst") = _
          rw [hf.dst]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "asset") = _
          rw [hf.asset]; rfl)
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption]; rfl)
    exact ExecStmt.iteFalse (hb.trans (by rw [decide_eq_false hb']))
      (ExecBlock.consNormal hc (execBlock_singleton hcall))

end Benchmarks.CompoundIII.Comet
