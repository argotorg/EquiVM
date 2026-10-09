import Benchmarks.CompoundIII.Comet.TransferBaseBalanceSource
import Benchmarks.CompoundIII.Comet.TransferBaseAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseMath_source (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) (hc : frame.contract = contract)
    (hsp : frame.locals.get? "srcPrincipal" = some (.int (signed104 srcPrincipal)))
    (hdp : frame.locals.get? "dstPrincipal" = some (.int (signed104 dstPrincipal)))
    (ha : frame.locals.get? "amount" = some (.int amount.toNat)) :
    ExecBlock config frame evm transferBaseMathBlock
      (if TransferBaseMathFits evm srcPrincipal dstPrincipal amount then
        .ok (transferBaseMathFrame frame evm srcPrincipal dstPrincipal amount) evm
      else .reverted) := by
  have hbal := transferBaseBalances_source frame evm srcPrincipal dstPrincipal amount hc hsp hdp ha
  by_cases hb : TransferBaseBalanceFits evm srcPrincipal dstPrincipal amount
  · rw [if_pos hb] at hbal
    let fb := transferBaseBalanceFrame frame evm srcPrincipal dstPrincipal amount
    have hsb : fb.locals.get? "srcBalance" =
        some (.int (signedWord (withdrawBaseBalance evm srcPrincipal amount))) := by
      rw [withdrawBaseBalance_int hb.1]
      simp only [fb, transferBaseBalanceFrame, transferBaseSrcBalanceFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hdb : fb.locals.get? "dstBalance" =
        some (.int (signedWord (supplyBaseBalance evm dstPrincipal amount))) := by
      rw [supplyBaseBalance_int hb.2]
      simp only [fb, transferBaseBalanceFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    have hbc : fb.contract = contract := by
      simp only [fb, transferBaseBalanceFrame, transferBaseSrcBalanceFrame]
      exact hc
    have hpr := transferBasePrincipals_source fb evm srcPrincipal dstPrincipal amount hbc hsb hdb
    by_cases hp : PrincipalValueFits evm (withdrawBaseBalance evm srcPrincipal amount) ∧
        PrincipalValueFits evm (supplyBaseBalance evm dstPrincipal amount)
    · rw [if_pos hp] at hpr
      let fp := transferBasePrincipalFrame fb evm srcPrincipal dstPrincipal amount
      have hpc : fp.contract = contract := by
        simp only [fp, transferBasePrincipalFrame]
        exact hbc
      have hsp' : fp.locals.get? "srcPrincipal" = some (.int (signed104 srcPrincipal)) := by
        simpa only [fp, transferBasePrincipalFrame, fb, transferBaseBalanceFrame,
          transferBaseSrcBalanceFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          using hsp
      have hdp' : fp.locals.get? "dstPrincipal" = some (.int (signed104 dstPrincipal)) := by
        simpa only [fp, transferBasePrincipalFrame, fb, transferBaseBalanceFrame,
          transferBaseSrcBalanceFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          using hdp
      have hsn : fp.locals.get? "srcPrincipalNew" =
          some (.int (signed104 (withdrawBasePrincipal evm srcPrincipal amount))) := by
        rw [withdrawBasePrincipal, principalValueWord_signed104 hp.1]
        simp only [fp, transferBasePrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl
      have hdn : fp.locals.get? "dstPrincipalNew" =
          some (.int (signed104 (supplyBasePrincipal evm dstPrincipal amount))) := by
        rw [supplyBasePrincipal, principalValueWord_signed104 hp.2]
        simp only [fp, transferBasePrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl
      have ham := transferBaseAmounts_source fp evm srcPrincipal dstPrincipal
        (withdrawBasePrincipal evm srcPrincipal amount) (supplyBasePrincipal evm dstPrincipal amount)
        hpc hsp' hdp' hsn hdn
      by_cases hm : WithdrawAmountsFits srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount) ∧
          RepayAmountsFits dstPrincipal (supplyBasePrincipal evm dstPrincipal amount)
      · rw [if_pos hm] at ham
        rw [if_pos ⟨⟨hb.1, hp.1, hm.1⟩, hb.2, hp.2, hm.2⟩]
        exact execBlock_append (execBlock_append hbal hpr) ham
      · rw [if_neg hm] at ham
        rw [if_neg (fun hf ↦ hm ⟨hf.1.2.2, hf.2.2.2⟩)]
        exact execBlock_append (execBlock_append hbal hpr) ham
    · rw [if_neg hp] at hpr
      rw [if_neg (fun hf ↦ hp ⟨hf.1.2.1, hf.2.2.1⟩)]
      exact execBlock_append_term (execBlock_append hbal hpr) (fun _ _ ↦ by simp)
  · rw [if_neg hb] at hbal
    rw [if_neg (fun hf ↦ hb ⟨hf.1.1, hf.2.1⟩)]
    exact execBlock_append_term (execBlock_append_term hbal (fun _ _ ↦ by simp)) (fun _ _ ↦ by simp)

end Benchmarks.CompoundIII.Comet
