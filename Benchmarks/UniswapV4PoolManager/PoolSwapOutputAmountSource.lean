import Benchmarks.UniswapV4PoolManager.PoolSwapAmountWords
import Benchmarks.UniswapV4PoolManager.PoolSwapAmountSyntax
import Benchmarks.UniswapV4PoolManager.SafeCast256Source
import Benchmarks.UniswapV4PoolManager.SignedSubSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapOutputAmountSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {remaining calculated : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated))) :
    ExecBlock config f evm poolSwapOutputAmountStmts
      (if poolSwapOutputAmountFits s calculated then .ok (poolSwapOutputAmountFrame f s remaining calculated) evm else .reverted) := by
  let total := s.amountIn+s.feeAmount
  let f1 := valueLocal f "__c16" (.int (EVM.signed s.amountOut))
  let f2 := valueLocal f1 "amountSpecifiedRemaining" (.int (EVM.signed (UInt256.sub remaining s.amountOut)))
  let f3 := valueLocal f2 "__c17" (.int (EVM.signed total))
  have hfirst := uintToInt256Call (evm := evm) hf
    (evalStructField (field := "amountOut") (evalLocalValue hs) rfl) "__c16"
  by_cases ho : s.amountOut.toNat < 2^255
  · rw [if_pos ho] at hfirst
    have hr1 : f1.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)) :=
      (store_get_ne _ _ (by decide : ("__c16" == "amountSpecifiedRemaining") = false)).trans hr
    have hremaining : ExecStmt config f1 evm poolSwapOutputAmountStmts[1]! (.ok f2 evm) :=
      ExecStmt.assign (evalSignedWordSub (evalLocalValue hr1) (evalLocalValue (store_get_self _ _ _)))
        (assignLocalValue hr1)
    have hs2 : f2.locals.get? "step" = some (poolSwapStepValue s) :=
      (store_get_ne2 _ _ _ (by decide : ("__c16" == "step") = false)
        (by decide : ("amountSpecifiedRemaining" == "step") = false)).trans hs
    have hinput := evalStructField (field := "amountIn") (evalLocalValue (cfg := config) (evm := evm) hs2) rfl
    have hfee := evalStructField (field := "feeAmount") (evalLocalValue (cfg := config) (evm := evm) hs2) rfl
    by_cases hsum : s.amountIn.toNat+s.feeAmount.toNat < UInt256.size
    · have heTotal := checkedAddSourceOk hinput hfee hsum
      have hsecond := uintToInt256Call (f := f2) hf heTotal "__c17"
      by_cases ht : total.toNat < 2^255
      · rw [if_pos ht] at hsecond
        have hc3 : f3.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)) :=
          (store_get_ne3 _ _ _ _ (by decide : ("__c16" == "amountCalculated") = false)
            (by decide : ("amountSpecifiedRemaining" == "amountCalculated") = false)
            (by decide : ("__c17" == "amountCalculated") = false)).trans hc
        have hlast := evalCheckedSignedSub ⟨256, by decide⟩
          (evalLocalValue (cfg := config) (evm := evm) hc3) (evalLocalValue (store_get_self _ _ _))
        by_cases hfit : int256Fits (EVM.signed calculated-EVM.signed total)
        · rw [if_pos (show signedFits ⟨256, by decide⟩ (EVM.signed calculated-EVM.signed total) from hfit)] at hlast
          rw [if_pos (show poolSwapOutputAmountFits s calculated from ⟨ho, hsum, ht, hfit⟩)]
          have he : EVM.signed (UInt256.sub calculated total) = EVM.signed calculated-EVM.signed total := by
            rw [← wordOfInt_signed_sub, signed_wordOfInt hfit]
          rw [← he] at hlast
          exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consNormal hsecond
            (execBlock_singleton (ExecStmt.assign hlast (assignLocalValue hc3)))))
        · rw [if_neg (show ¬signedFits ⟨256, by decide⟩ (EVM.signed calculated-EVM.signed total) from hfit)] at hlast
          rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => hfit h.2.2.2)]
          exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consNormal hsecond
            (ExecBlock.consRevert (ExecStmt.assignExprRevert hlast))))
      · rw [if_neg ht] at hsecond
        rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => ht h.2.2.1)]
        exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consRevert hsecond))
    · have heTotal := checkedAddSourceOverflow hinput hfee (Nat.le_of_not_gt hsum)
      rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => hsum h.2.1)]
      exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consRevert
        (ExecStmt.internalCallArgsRevert (by simp only [evalExprs?, heTotal, bind, EvalResult.bind]))))
  · rw [if_neg ho] at hfirst
    rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => ho h.1)]
    exact ExecBlock.consRevert hfirst

end Benchmarks.UniswapV4PoolManager
