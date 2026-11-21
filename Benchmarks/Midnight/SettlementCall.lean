import Benchmarks.Midnight.SettlementSource

/-! Source wrapper calling the settlement-fee internal function. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def settlementExternalArguments (id time : UInt256) : Store :=
  ((∅ : Store).insert "id" (wordBytes32Value id)).insert "timeToMaturity" (.int time.toNat)

theorem evalSettlementCallArgs (evm : EVM.State) (id time : UInt256) :
    evalExprs? config (calldataFrame contract (settlementExternalArguments id time) ∅ evm)
      evm [.var "id", .var "timeToMaturity"] =
      .ok [wordBytes32Value id, .int time.toNat] := by
  have hid : (calldataFrame contract (settlementExternalArguments id time) ∅ evm).locals.get?
      "id" = some (wordBytes32Value id) := by
    change ((((∅ : Store).insert "id" (wordBytes32Value id)).insert "timeToMaturity"
      (.int time.toNat)).insert "__calldata" (.bytes evm.executionEnv.calldata)).get? "id" = _
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have ht : (calldataFrame contract (settlementExternalArguments id time) ∅ evm).locals.get?
      "timeToMaturity" = some (.int time.toNat) := by
    change ((settlementExternalArguments id time).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? "timeToMaturity" = _
    rw [store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  simp only [evalExprs?, evalExpr?, hid, ht, EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem settlementFeeBodyReturns (evm : EVM.State) (id time : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (settlementExternalArguments id time)
      settlementFeeTransition.body
      (.returned (resumeAfterInternalCall
        (calldataFrame contract (settlementExternalArguments id time) ∅ evm)
        "__r" (some [.int (settlementFeeValue (marketFeeWord evm id) time).toNat]))
        evm (some [.int (settlementFeeValue (marketFeeWord evm id) time).toNat])) := by
  obtain ⟨frame', hbody⟩ := settlementFeeInternalReturns evm ∅ id time hspace
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (stele' := resumeAfterInternalCall _ "__r"
    (some [.int (settlementFeeValue (marketFeeWord evm id) time).toNat]))
  · exact internalCallFunctionReturn (callee := settlementFeeFunction)
      (locals := settlementFeeArguments id time) (evalSettlementCallArgs evm id time) rfl rfl hbody
  · exact returnInternalResult "__r" _

theorem settlementFeeBodyReverts (evm : EVM.State) (id time : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecTransitionBody config contract evm (settlementExternalArguments id time)
      settlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := settlementFeeFunction)
    (locals := settlementFeeArguments id time) (evalSettlementCallArgs evm id time) rfl rfl
    (settlementFeeInternalReverts evm ∅ id time hspace)

end Benchmarks.Midnight
