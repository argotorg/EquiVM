import Benchmarks.UniswapV4PoolManager.PoolSwapAmountWords
import Benchmarks.UniswapV4PoolManager.PoolSwapAmountSyntax
import Benchmarks.UniswapV4PoolManager.SafeCast256Source
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapInputAmountSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {remaining calculated : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated))) :
    ExecBlock config f evm poolSwapInputAmountStmts
      (if poolSwapInputAmountFits s calculated then .ok (poolSwapInputAmountFrame f s remaining calculated) evm else .reverted) := by
  let total := s.amountIn+s.feeAmount
  let f1 := valueLocal f "__c18" (.int (EVM.signed total))
  let f2 := valueLocal f1 "amountSpecifiedRemaining" (.int (EVM.signed (remaining+total)))
  let f3 := valueLocal f2 "__c19" (.int (EVM.signed s.amountOut))
  have heTotal := evalWordAdd
    (evalStructField (field := "amountIn") (evalLocalValue (cfg := config) (evm := evm) hs) rfl)
    (evalStructField (field := "feeAmount") (evalLocalValue (cfg := config) (evm := evm) hs) rfl)
  have hfirst := uintToInt256Call hf heTotal "__c18"
  by_cases ht : total.toNat < 2^255
  · rw [if_pos ht] at hfirst
    have hr1 : f1.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)) :=
      (store_get_ne _ _ (by decide : ("__c18" == "amountSpecifiedRemaining") = false)).trans hr
    have hremaining : ExecStmt config f1 evm poolSwapInputAmountStmts[1]! (.ok f2 evm) :=
      ExecStmt.assign (evalSignedWordAdd (evalLocalValue hr1) (evalLocalValue (store_get_self _ _ _)))
        (assignLocalValue hr1)
    have hs2 : f2.locals.get? "step" = some (poolSwapStepValue s) :=
      (store_get_ne2 _ _ _ (by decide : ("__c18" == "step") = false)
        (by decide : ("amountSpecifiedRemaining" == "step") = false)).trans hs
    have hsecond := uintToInt256Call (f := f2) (evm := evm) hf
      (evalStructField (field := "amountOut") (evalLocalValue hs2) rfl) "__c19"
    by_cases ho : s.amountOut.toNat < 2^255
    · rw [if_pos ho] at hsecond
      have hc3 : f3.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)) :=
        (store_get_ne3 _ _ _ _ (by decide : ("__c18" == "amountCalculated") = false)
          (by decide : ("amountSpecifiedRemaining" == "amountCalculated") = false)
          (by decide : ("__c19" == "amountCalculated") = false)).trans hc
      have hlast := evalCheckedInt256Add (evalLocalValue (cfg := config) (evm := evm) hc3)
        (evalLocalValue (store_get_self _ _ _))
      by_cases hfit : int256Fits (EVM.signed calculated+EVM.signed s.amountOut)
      · rw [if_pos hfit] at hlast
        rw [if_pos (show poolSwapInputAmountFits s calculated from ⟨ht, ho, hfit⟩)]
        have he : EVM.signed (calculated+s.amountOut) = EVM.signed calculated+EVM.signed s.amountOut := by
          rw [← wordOfInt_signed_add, signed_wordOfInt hfit]
        rw [← he] at hlast
        exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consNormal hsecond
          (execBlock_singleton (ExecStmt.assign hlast (assignLocalValue hc3)))))
      · rw [if_neg hfit] at hlast
        rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => hfit h.2.2)]
        exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consNormal hsecond
          (ExecBlock.consRevert (ExecStmt.assignExprRevert hlast))))
    · rw [if_neg ho] at hsecond
      rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => ho h.2.1)]
      exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hremaining (ExecBlock.consRevert hsecond))
  · rw [if_neg ht] at hfirst
    rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => ht h.1)]
    exact ExecBlock.consRevert hfirst

end Benchmarks.UniswapV4PoolManager
