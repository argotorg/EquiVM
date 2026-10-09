import Benchmarks.CompoundIII.Comet.TransferBaseMathFrames
import Benchmarks.CompoundIII.Comet.PrincipalValueSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseBalances_source (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) (hc : frame.contract = contract)
    (hsp : frame.locals.get? "srcPrincipal" = some (.int (signed104 srcPrincipal)))
    (hdp : frame.locals.get? "dstPrincipal" = some (.int (signed104 dstPrincipal)))
    (ha : frame.locals.get? "amount" = some (.int amount.toNat)) :
    ExecBlock config frame evm transferBaseBalanceBlock
      (if TransferBaseBalanceFits evm srcPrincipal dstPrincipal amount then
        .ok (transferBaseBalanceFrame frame evm srcPrincipal dstPrincipal amount) evm
      else .reverted) := by
  have hsrc := baseBalance_source frame evm srcPrincipal amount true
    "srcPrincipal" "__c1" "__c2" "srcBalance" (by decide) (by decide) hc hsp ha
  simp only [baseBalanceFits_sub, baseBalanceFrame, baseBalanceInt, if_true] at hsrc
  by_cases hs : WithdrawBaseBalanceFits evm srcPrincipal amount
  · rw [if_pos hs] at hsrc
    let f := transferBaseSrcBalanceFrame frame evm srcPrincipal amount
    have hdp' : f.locals.get? "dstPrincipal" = some (.int (signed104 dstPrincipal)) := by
      simpa only [f, transferBaseSrcBalanceFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hdp
    have ha' : f.locals.get? "amount" = some (.int amount.toNat) := by
      simpa only [f, transferBaseSrcBalanceFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using ha
    have hdst := baseBalance_source f evm dstPrincipal amount false
      "dstPrincipal" "__c3" "__c4" "dstBalance" (by decide) (by decide) hc hdp' ha'
    simp only [baseBalanceFits_add, baseBalanceFrame, baseBalanceInt, Bool.false_eq_true,
      if_false] at hdst
    by_cases hd : SupplyBaseBalanceFits evm dstPrincipal amount
    · rw [if_pos hd] at hdst
      rw [if_pos ⟨hs, hd⟩]
      exact execBlock_append hsrc hdst
    · rw [if_neg hd] at hdst
      rw [if_neg (fun hf ↦ hd hf.2)]
      exact execBlock_append hsrc hdst
  · rw [if_neg hs] at hsrc
    rw [if_neg (fun hf ↦ hs hf.1)]
    exact execBlock_append_term hsrc (fun _ _ ↦ by simp)

theorem transferBasePrincipals_source (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal amount : UInt256) (hc : frame.contract = contract)
    (hsb : frame.locals.get? "srcBalance" =
      some (.int (signedWord (withdrawBaseBalance evm srcPrincipal amount))))
    (hdb : frame.locals.get? "dstBalance" =
      some (.int (signedWord (supplyBaseBalance evm dstPrincipal amount)))) :
    ExecBlock config frame evm transferBasePrincipalBlock
      (if PrincipalValueFits evm (withdrawBaseBalance evm srcPrincipal amount) ∧
          PrincipalValueFits evm (supplyBaseBalance evm dstPrincipal amount) then
        .ok (transferBasePrincipalFrame frame evm srcPrincipal dstPrincipal amount) evm
      else .reverted) := by
  have hse : evalExpr? config frame evm (.var "srcBalance") =
      .ok (.int (signedWord (withdrawBaseBalance evm srcPrincipal amount))) := by
    simp only [evalExpr?, hsb, EvalResult.ofOption]
  have hsrc := principalValue_call frame evm (withdrawBaseBalance evm srcPrincipal amount)
    _ "srcPrincipalNew" hc hse
  by_cases hs : PrincipalValueFits evm (withdrawBaseBalance evm srcPrincipal amount)
  · rw [if_pos hs] at hsrc
    let f : Frame := { frame with
      locals := frame.locals.insert "srcPrincipalNew"
        (.int (principalValueInt evm (withdrawBaseBalance evm srcPrincipal amount))) }
    have hde : evalExpr? config f evm (.var "dstBalance") =
        .ok (.int (signedWord (supplyBaseBalance evm dstPrincipal amount))) := by
      simp only [evalExpr?, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstBalance") = _
      rw [hdb]; rfl
    have hdst := principalValue_call f evm (supplyBaseBalance evm dstPrincipal amount)
      _ "dstPrincipalNew" hc hde
    by_cases hd : PrincipalValueFits evm (supplyBaseBalance evm dstPrincipal amount)
    · rw [if_pos hd] at hdst
      rw [if_pos ⟨hs, hd⟩]
      exact ExecBlock.consNormal hsrc (ExecBlock.consNormal hdst ExecBlock.nil)
    · rw [if_neg hd] at hdst
      rw [if_neg (fun hf ↦ hd hf.2)]
      exact ExecBlock.consNormal hsrc (ExecBlock.consRevert hdst)
  · rw [if_neg hs] at hsrc
    rw [if_neg (fun hf ↦ hs hf.1)]
    exact ExecBlock.consRevert hsrc

end Benchmarks.CompoundIII.Comet
