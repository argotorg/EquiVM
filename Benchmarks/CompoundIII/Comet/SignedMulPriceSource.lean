import Benchmarks.CompoundIII.Comet.SignedMulPriceModel
import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES signedRangeSourceOverflow to failure at the lower signed bound.
theorem signedRangeSourceUnderflow {cfg frame evm expr i}
    (he : evalExpr? cfg frame evm expr = .ok (.int i)) (hlo : i < -(2^255 : Int)) :
    evalExpr? cfg frame evm (.inRange (.sint ⟨256, by decide⟩) expr) = .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hlo, decide_true, Bool.true_or, if_true]

theorem signedMulPriceReturn_source (frame : Frame) (evm : EVM.State) (m p scale : UInt256)
    (hscale : scale.toNat < 2^64)
    (hn : evalExpr? config frame evm (.var "n") = .ok (.int (-Int.ofNat m.toNat)))
    (hp : evalExpr? config frame evm (.var "__c0") = .ok (.int p.toNat))
    (hs : evalExpr? config frame evm (.var "fromScale") = .ok (.int scale.toNat)) :
    evalExpr? config frame evm signedMulPriceReturnExpr =
      if signedDebtPriceValid m p scale then .ok (.int (signedDebtPriceInt m p scale))
      else .revert := by
  have hm : evalExpr? config frame evm (.binary .mul (.var "n") (.var "__c0")) =
      .ok (.int (-Int.ofNat (m.toNat * p.toNat))) := by
    simp only [evalExpr?, hn, hp, bind, EvalResult.bind, evalBinaryOp?,
      Int.ofNat_eq_natCast, Nat.cast_mul, neg_mul]
  by_cases hfit : m.toNat * p.toNat ≤ 2^255
  · have hm' := signedRangeSourceOk (cfg := config) (frame := frame) (evm := evm) hm
      (by
        have hi : ((m.toNat * p.toNat : Nat) : Int) ≤ 2^255 := by exact_mod_cast hfit
        exact neg_le_neg hi)
      (by simp only [Int.ofNat_eq_natCast]; omega)
    have hs' := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
      (castUintSourceOk ⟨256, by decide⟩ hs (lt_trans hscale (by decide)))
    rw [normalizeInt_sint256_word_of_lt scale (lt_trans hscale (by decide))] at hs'
    by_cases hz : scale = UInt256.ofNat 0
    · have hbad : ¬ signedDebtPriceValid m p scale := fun h ↦ h.2 hz
      rw [if_neg hbad]
      simp only [signedMulPriceReturnExpr, evalExpr?, hm', hs', bind, EvalResult.bind,
        evalBinaryOp?, hz]
      rfl
    · rw [if_pos ⟨hfit, hz⟩]
      have hsz : (scale.toNat : Int) ≠ 0 := by
        intro hzero
        exact hz (uint256_toNat_eq_zero (by omega))
      simp only [signedMulPriceReturnExpr, evalExpr?, hm', hs', bind, EvalResult.bind,
        evalBinaryOp?, Int.ofNat_eq_natCast, hsz, if_false, signedDebtPriceInt,
        Int.neg_tdiv, Int.ofNat_tdiv]
  · have hm' := signedRangeSourceUnderflow (cfg := config) (frame := frame) (evm := evm)
      hm (by
        simp only [Int.ofNat_eq_natCast]
        have h : (2^255 : Nat) < m.toNat * p.toNat := by omega
        have hi : (2^255 : Int) < ((m.toNat * p.toNat : Nat) : Int) := by exact_mod_cast h
        exact neg_lt_neg hi)
    rw [if_neg (fun h : signedDebtPriceValid m p scale ↦ hfit h.1)]
    simp only [signedMulPriceReturnExpr, evalExpr?, hm', bind, EvalResult.bind]

theorem signedMulPrice_source (evm : EVM.State) (imms : Store) (m p scale : UInt256)
    (hp : p.toNat < 2^255) (hscale : scale.toNat < 2^64) :
    ExecFuncBody config (signedMulPriceEntry imms m p scale) evm signedMulPriceCallable.body
      (if signedDebtPriceValid m p scale then
        .returned (signedMulPriceFinal imms m p scale) evm
          (some [.int (signedDebtPriceInt m p scale)]) else .reverted) := by
  let frame := signedMulPriceEntry imms m p scale
  let final := signedMulPriceFinal imms m p scale
  have he : evalExpr? config frame evm (.var "price") = .ok (.int p.toNat) := by
    simp only [evalExpr?, frame, signedMulPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hcall := signed256_call_ok frame evm p (.var "price") "__c0" rfl he hp
  have hn : evalExpr? config final evm (.var "n") = .ok (.int (-Int.ofNat m.toNat)) := by
    simp only [evalExpr?, final, signedMulPriceFinal, signedMulPriceEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hprice : evalExpr? config final evm (.var "__c0") = .ok (.int p.toNat) := by
    simp only [evalExpr?, final, signedMulPriceFinal, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs : evalExpr? config final evm (.var "fromScale") = .ok (.int scale.toNat) := by
    simp only [evalExpr?, final, signedMulPriceFinal, signedMulPriceEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hr := signedMulPriceReturn_source final evm m p scale hscale hn hprice hs
  by_cases hv : signedDebtPriceValid m p scale
  · rw [if_pos hv] at hr ⊢
    exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hcall (ABlock.start.returns hr))
  · rw [if_neg hv] at hr ⊢
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consNormal hcall
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    change evalExprs? config final evm [signedMulPriceReturnExpr] = .revert
    simp only [evalExprs?, hr, bind, EvalResult.bind]

theorem signedMulPrice_call (frame : Frame) (evm : EVM.State) (m p scale : UInt256)
    (nExpr priceExpr scaleExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hp : p.toNat < 2^255) (hscale : scale.toNat < 2^64)
    (hn : evalExpr? config frame evm nExpr = .ok (.int (-Int.ofNat m.toNat)))
    (hep : evalExpr? config frame evm priceExpr = .ok (.int p.toNat))
    (hes : evalExpr? config frame evm scaleExpr = .ok (.int scale.toNat)) :
    ExecStmt config frame evm (.internalCall "signedMulPrice" [nExpr, priceExpr, scaleExpr] ret)
      (if signedDebtPriceValid m p scale then .ok { frame with
        locals := frame.locals.insert ret (.int (signedDebtPriceInt m p scale)) } evm
      else .reverted) := by
  have hb := signedMulPrice_source evm frame.immutables m p scale hp hscale
  by_cases hv : signedDebtPriceValid m p scale
  · rw [if_pos hv] at hb ⊢
    exact ExecStmt.internalCallReturn (cfg := config) (solm := frame) (evm := evm)
      (args := [nExpr, priceExpr, scaleExpr]) (callee := signedMulPriceCallable)
      (argVals := [.int (-Int.ofNat m.toNat), .int p.toNat, .int scale.toNat])
      (by simp only [evalExprs?, hn, hep, hes, pure, bind, EvalResult.bind])
      (by rw [hc]; exact signedMulPriceCallable_lookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hv] at hb ⊢
    exact ExecStmt.internalCallRevert (cfg := config) (solm := frame) (evm := evm)
      (args := [nExpr, priceExpr, scaleExpr]) (callee := signedMulPriceCallable)
      (argVals := [.int (-Int.ofNat m.toNat), .int p.toNat, .int scale.toNat])
      (by simp only [evalExprs?, hn, hep, hes, pure, bind, EvalResult.bind])
      (by rw [hc]; exact signedMulPriceCallable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
