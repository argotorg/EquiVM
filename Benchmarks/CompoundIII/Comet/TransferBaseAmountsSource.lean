import Benchmarks.CompoundIII.Comet.TransferBaseMathFrames
import Benchmarks.CompoundIII.Comet.WithdrawAmountsSource
import Benchmarks.CompoundIII.Comet.RepayAmountsSource
import Benchmarks.CompoundIII.Comet.TupleLocalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseAmounts_source (frame : Frame) (evm : EVM.State)
    (srcPrincipal dstPrincipal srcNext dstNext : UInt256) (hc : frame.contract = contract)
    (hsp : frame.locals.get? "srcPrincipal" = some (.int (signed104 srcPrincipal)))
    (hdp : frame.locals.get? "dstPrincipal" = some (.int (signed104 dstPrincipal)))
    (hsn : frame.locals.get? "srcPrincipalNew" = some (.int (signed104 srcNext)))
    (hdn : frame.locals.get? "dstPrincipalNew" = some (.int (signed104 dstNext))) :
    ExecBlock config frame evm transferBaseAmountsBlock
      (if WithdrawAmountsFits srcPrincipal srcNext ∧ RepayAmountsFits dstPrincipal dstNext then
        .ok (transferBaseAmountsFrame frame srcPrincipal dstPrincipal srcNext dstNext) evm
      else .reverted) := by
  have hspe : evalExpr? config frame evm (.var "srcPrincipal") =
      .ok (.int (signed104 srcPrincipal)) := by simp only [evalExpr?, hsp, EvalResult.ofOption]
  have hsne : evalExpr? config frame evm (.var "srcPrincipalNew") =
      .ok (.int (signed104 srcNext)) := by simp only [evalExpr?, hsn, EvalResult.ofOption]
  have hsrc := withdrawAmounts_call frame evm srcPrincipal srcNext _ _ "__c7" hc hspe hsne
  by_cases hs : WithdrawAmountsFits srcPrincipal srcNext
  · rw [if_pos hs] at hsrc
    let withdrawn := withdrawSupplyAmount srcPrincipal srcNext
    let borrowed := withdrawBorrowAmount srcPrincipal srcNext
    let f1 : Frame := { frame with
      locals := frame.locals.insert "__c7" (.tuple [.int withdrawn.toNat, .int borrowed.toNat]) }
    have ht1 : f1.locals.get? "__c7" = some (.tuple [.int withdrawn.toNat, .int borrowed.toNat]) := by
      simp only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hp1 := tuplePairLets_source config f1 evm "__c7" "withdrawAmount" "borrowAmount"
      (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (some (.elem (.int (.uint ⟨104, by decide⟩)))) _ _ (by decide) ht1
    let f3 : Frame := { f1 with
      locals := (f1.locals.insert "withdrawAmount" (.int withdrawn.toNat)).insert
        "borrowAmount" (.int borrowed.toNat) }
    have hdpe : evalExpr? config f3 evm (.var "dstPrincipal") =
        .ok (.int (signed104 dstPrincipal)) := by
      simp only [evalExpr?, f3, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstPrincipal") = _
      rw [hdp]; rfl
    have hdne : evalExpr? config f3 evm (.var "dstPrincipalNew") =
        .ok (.int (signed104 dstNext)) := by
      simp only [evalExpr?, f3, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstPrincipalNew") = _
      rw [hdn]; rfl
    have hdst := repayAmounts_call f3 evm dstPrincipal dstNext _ _ "__c8" hc hdpe hdne
    by_cases hd : RepayAmountsFits dstPrincipal dstNext
    · rw [if_pos hd] at hdst
      rw [if_pos ⟨hs, hd⟩]
      let repaid := repayAmount dstPrincipal dstNext
      let supplied := supplyAmount dstPrincipal dstNext
      let f4 : Frame := { f3 with
        locals := f3.locals.insert "__c8" (.tuple [.int repaid.toNat, .int supplied.toNat]) }
      have ht4 : f4.locals.get? "__c8" = some (.tuple [.int repaid.toNat, .int supplied.toNat]) := by
        simp only [f4, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
      have hp4 := tuplePairLets_source config f4 evm "__c8" "repayAmount" "supplyAmount"
        (some (.elem (.int (.uint ⟨104, by decide⟩))))
        (some (.elem (.int (.uint ⟨104, by decide⟩)))) _ _ (by decide) ht4
      exact ExecBlock.consNormal hsrc (execBlock_append hp1 (ExecBlock.consNormal hdst hp4))
    · rw [if_neg hd] at hdst
      rw [if_neg (fun hf ↦ hd hf.2)]
      exact ExecBlock.consNormal hsrc (execBlock_append hp1 (ExecBlock.consRevert hdst))
  · rw [if_neg hs] at hsrc
    rw [if_neg (fun hf ↦ hs hf.1)]
    exact ExecBlock.consRevert hsrc

end Benchmarks.CompoundIII.Comet
