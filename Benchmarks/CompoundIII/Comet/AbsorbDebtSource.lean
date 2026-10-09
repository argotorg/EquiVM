import Benchmarks.CompoundIII.Comet.AbsorbDebtModel
import Benchmarks.CompoundIII.Comet.Unsigned256Revert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbDebtArithmetic_source (frame : Frame) (evm : State)
    (v : CometWithExtendedAssetListImmutables) (old next price : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ho : frame.locals.get? "oldBalance" = some (.int (signedWord old)))
    (hn : frame.locals.get? "newBalance" = some (.int (signedWord next)))
    (hp : frame.locals.get? "basePrice" = some (.int price.toNat))
    (hnext : next.toNat < 2^255) :
    ExecBlock config frame evm absorbDebtArithmeticBlock
      (if AbsorbDebtValid v old next price then
        .ok (absorbDebtFrame frame v old next price) evm else .reverted) := by
  have he : evalExpr? config frame evm (.binary .sub (.var "newBalance") (.var "oldBalance")) =
      .ok (.int (signedWord next - signedWord old)) := by
    simp only [evalExpr?, ho, hn, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hh : signedWord next - signedWord old < (2^255 : Int)
  · have hlo : -(2^255 : Int) ≤ signedWord next - signedWord old := by
      have hn0 := (signedWord_nonneg_iff next).2 hnext
      have hohi := (signedWord_bounds old).2
      omega
    have her := signedRangeSourceOk he hlo hh
    have hd := absorbPaidWord_signed hnext hh
    by_cases h0 : 0 ≤ signedWord next - signedWord old
    · have hpaid : (absorbPaidWord old next).toNat < 2^255 :=
        (signedWord_nonneg_iff _).1 (by rw [hd]; exact h0)
      have hnat : Int.ofNat (absorbPaidWord old next).toNat =
          signedWord next - signedWord old := (signedWord_low hpaid).symm.trans hd
      rw [← hnat] at her
      have hu := unsigned256_call_ok frame evm (absorbPaidWord old next) _ "basePaidOut" hc her
      let paid := absorbPaidFrame frame old next
      have hp' : paid.locals.get? "basePrice" = some (.int price.toNat) := by
        simpa only [paid, absorbPaidFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] using hp
      have hm := mulPrice_call paid evm (absorbPaidWord old next) price (collateralBaseScale v)
        (.var "basePaidOut") (.var "basePrice")
        (.cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩))))
        "valueOfBasePaidOut" hc
        (by simp only [evalExpr?, paid, absorbPaidFrame, Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
        (by simp only [evalExpr?, hp', EvalResult.ofOption]) (by
          apply uintCastWord_source
          simp only [evalExpr?, show paid.immutables = immStore v from hi,
            immStore_get_baseScale, EvalResult.ofOption])
      by_cases hmV : MulPriceValid (absorbPaidWord old next) price (collateralBaseScale v)
      · rw [if_pos hmV] at hm
        rw [if_pos ⟨h0, hh, hmV⟩]
        exact ExecBlock.consNormal hu (ExecBlock.consNormal hm ExecBlock.nil)
      · rw [if_neg hmV] at hm
        rw [if_neg (fun hv ↦ hmV hv.2.2)]
        exact ExecBlock.consNormal hu (ExecBlock.consRevert hm)
    · rw [if_neg (fun hv ↦ h0 hv.1)]
      exact ExecBlock.consRevert
        (unsigned256_call_revert frame evm _ _ "basePaidOut" hc her (by omega))
  · rw [if_neg (fun hv ↦ hh hv.2.1)]
    have her := signedRangeSourceOverflow he (le_of_not_gt hh)
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
    change evalExprs? config frame evm _ = .revert
    simp only [evalExprs?, her, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
