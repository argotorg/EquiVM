import Benchmarks.CompoundIII.Comet.SupplyBaseMathModel
import Benchmarks.CompoundIII.Comet.BaseBalanceSource
import Benchmarks.CompoundIII.Comet.PrincipalValueSource
import Benchmarks.CompoundIII.Comet.RepayAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem supplyBaseMath_source (frame : Frame) (evm : EVM.State) (principal amount : UInt256)
    (hc : frame.contract = contract)
    (hprincipal : frame.locals.get? "dstPrincipal" = some (.int (signed104 principal)))
    (hamount : frame.locals.get? "amount" = some (.int amount.toNat)) :
    ExecBlock config frame evm supplyBaseMathBlock
      (if SupplyBaseMathFits evm principal amount then
        .ok (supplyBaseMathFrame frame evm principal amount) evm else .reverted) := by
  have hprefix := baseBalance_source frame evm principal amount false
    "dstPrincipal" "__c2" "__c3" "dstBalance" (by decide) (by decide) hc hprincipal hamount
  simp only [baseBalanceFits_add, baseBalanceFrame, baseBalanceInt, baseBalanceBlock,
    Bool.false_eq_true, if_false] at hprefix
  by_cases hbalance : SupplyBaseBalanceFits evm principal amount
  · rw [if_pos hbalance] at hprefix
    let f3 : Frame := { frame with
      locals := ((frame.locals.insert "__c2" (.int (signedPresentValueInt evm principal))).insert
        "__c3" (.int amount.toNat)).insert "dstBalance"
          (.int (supplyBaseBalanceInt evm principal amount)) }
    have he3 : evalExpr? config f3 evm (.var "dstBalance") =
        .ok (.int (signedWord (supplyBaseBalance evm principal amount))) := by
      rw [supplyBaseBalance_int hbalance]
      simp only [evalExpr?, f3, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
    have hnext := principalValue_call f3 evm (supplyBaseBalance evm principal amount)
      _ "dstPrincipalNew" hc he3
    by_cases hp : PrincipalValueFits evm (supplyBaseBalance evm principal amount)
    · rw [if_pos hp] at hnext
      let next := supplyBasePrincipal evm principal amount
      let f4 : Frame := { f3 with
        locals := f3.locals.insert "dstPrincipalNew"
          (.int (principalValueInt evm (supplyBaseBalance evm principal amount))) }
      have ho4 : evalExpr? config f4 evm (.var "dstPrincipal") =
          .ok (.int (signed104 principal)) := by
        simp only [evalExpr?, f4, f3, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstPrincipal") = _
        rw [hprincipal]; rfl
      have hn4 : evalExpr? config f4 evm (.var "dstPrincipalNew") =
          .ok (.int (signed104 next)) := by
        change evalExpr? _ _ _ _ = .ok (.int (signed104
          (principalValueWord evm (supplyBaseBalance evm principal amount))))
        rw [principalValueWord_signed104 hp]
        simp only [evalExpr?, f4, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
      have hsplit := repayAmounts_call f4 evm principal next _ _ "__c5" hc ho4 hn4
      by_cases hw : RepayAmountsFits principal next
      · rw [if_pos hw] at hsplit
        rw [if_pos ⟨hbalance, hp, hw⟩]
        let supplied := repayAmount principal next
        let borrowed := supplyAmount principal next
        let f5 : Frame := { f4 with
          locals := f4.locals.insert "__c5" (.tuple [.int supplied.toNat, .int borrowed.toNat]) }
        let f6 : Frame := { f5 with
          locals := f5.locals.insert "repayAmount" (.int supplied.toNat) }
        have he5 : evalExpr? config f5 evm (.tupleGet (.var "__c5") 0) =
            .ok (.int supplied.toNat) := by
          simp only [evalExpr?, f5, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]; rfl
        have he6 : evalExpr? config f6 evm (.tupleGet (.var "__c5") 1) =
            .ok (.int borrowed.toNat) := by
          simp only [evalExpr?, f6, f5, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]; rfl
        exact execBlock_append hprefix (ExecBlock.consNormal hnext
          (ExecBlock.consNormal hsplit (ExecBlock.consNormal (ExecStmt.letDecl he5)
            (ExecBlock.consNormal (ExecStmt.letDecl he6) ExecBlock.nil))))
      · rw [if_neg hw] at hsplit
        rw [if_neg (fun hf ↦ hw hf.2.2)]
        exact execBlock_append hprefix (ExecBlock.consNormal hnext (ExecBlock.consRevert hsplit))
    · rw [if_neg hp] at hnext
      rw [if_neg (fun hf ↦ hp hf.2.1)]
      exact execBlock_append hprefix (ExecBlock.consRevert hnext)
  · rw [if_neg hbalance] at hprefix
    rw [if_neg (fun hf ↦ hbalance hf.1)]
    exact execBlock_append_term hprefix (fun _ _ ↦ by simp)

end Benchmarks.CompoundIII.Comet
