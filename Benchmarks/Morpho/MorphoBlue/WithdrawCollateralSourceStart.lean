import Benchmarks.Morpho.MorphoBlue.CollateralTransferLocals
import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawCollateralPrelude (p : MarketParamsWords) (assets account receiver : UInt256)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := collateralTransferArgs p assets account receiver, immutables := imms }
      withdrawCollateralTransition.body (collateralTransferFrame p assets account receiver evm.executionEnv.calldata imms)
      (withdrawCollateralTransition.body.drop 4) := by
  refine ⟨fun h => (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, collateralTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
      EvalResult.ofOption])

theorem morphoWithdrawCollateralSourceBasicGuards (p : MarketParamsWords) (assets account receiver : UInt256)
    (hc : p.Canonical) (hr : receiver.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyCollateralGuards evm.accountMap evm.executionEnv p assets receiver) :
    ABlock config evm { contract := contract, locals := collateralTransferArgs p assets account receiver, immutables := imms }
      withdrawCollateralTransition.body (collateralTransferFrame p assets account receiver evm.executionEnv.calldata imms)
      (withdrawCollateralTransition.body.drop 7) := by
  have hl := collateralTransferFrame_locals p assets account receiver evm.executionEnv.calldata imms
  exact (((morphoWithdrawCollateralPrelude p assets account receiver hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg.1] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))).requireStep
    (by simpa only [decide_eq_true hg.2.1] using evalWordNeZero (hl.evalAssets imms evm))).requireStep
    (by simpa only [decide_eq_true hg.2.2] using evalCanonicalAddressNeZero hr (hl.evalReceiver imms evm))

theorem morphoWithdrawCollateralSourceBasicReject (p : MarketParamsWords) (assets account receiver : UInt256)
    (hc : p.Canonical) (hr : receiver.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ SupplyCollateralGuards evm.accountMap evm.executionEnv p assets receiver) :
    ExecTransitionBody config contract evm (collateralTransferArgs p assets account receiver)
      withdrawCollateralTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hl := collateralTransferFrame_locals p assets account receiver evm.executionEnv.calldata imms
  have pref := morphoWithdrawCollateralPrelude p assets account receiver hc evm imms hcv hsize
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · exact pref.requireRevert (by simpa only [decide_eq_false hcreated] using
        (evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩)))
  have pref1 := pref.requireStep (by simpa only [decide_eq_true hcreated] using
      (evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩)))
  by_cases hz : assets ≠ ⟨0⟩
  swap
  · exact pref1.requireRevert (by simpa only [decide_eq_false hz] using evalWordNeZero (hl.evalAssets imms evm))
  exact (pref1.requireStep (by simpa only [decide_eq_true hz] using evalWordNeZero (hl.evalAssets imms evm))).requireRevert
    (by simpa only [decide_eq_false (fun hn => hg ⟨hcreated, hz, hn⟩)] using
      (evalCanonicalAddressNeZero hr (hl.evalReceiver imms evm)))

theorem collateralTransferAuthorizedFrame_eval_c1 (p : MarketParamsWords) (assets account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    evalExpr? config (collateralTransferAuthorizedFrame p assets account receiver evm imms) evm (.var "__c1") =
      .ok (.bool (decide (senderAuthorizedWord evm.accountMap evm.executionEnv account ≠ UInt256.ofNat 0))) := by
  simp only [evalExpr?, collateralTransferAuthorizedFrame, store_get_self, EvalResult.ofOption, wordToElemBool, decide_not]
  rfl

theorem morphoWithdrawCollateralSourceAuthorized (p : MarketParamsWords)
    (assets account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyCollateralGuards evm.accountMap evm.executionEnv p assets receiver) :
    ABlock config evm { contract := contract, locals := collateralTransferArgs p assets account receiver, immutables := imms }
      withdrawCollateralTransition.body (collateralTransferAuthorizedFrame p assets account receiver evm imms)
      (withdrawCollateralTransition.body.drop 8) := by
  have hl := collateralTransferFrame_locals p assets account receiver evm.executionEnv.calldata imms
  have pref := morphoWithdrawCollateralSourceBasicGuards p assets account receiver hc hr evm imms hcv hsize hg
  refine ⟨fun h ↦ pref.run (ExecBlock.consNormal ?_ h)⟩
  apply morphoSenderAuthorizedCall account imms _ evm _ "__c1" ha
  exact evalExprs?_singleton (hl.evalAccount imms evm)

theorem morphoWithdrawCollateralSourceGuards (p : MarketParamsWords)
    (assets account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : WithdrawCollateralGuards evm.accountMap evm.executionEnv p assets account receiver) :
    ABlock config evm { contract := contract, locals := collateralTransferArgs p assets account receiver, immutables := imms }
      withdrawCollateralTransition.body (collateralTransferBeforeAccrue p assets account receiver evm imms)
      (withdrawCollateralTransition.body.drop 10) := by
  have hl := collateralTransferAuthorizedFrame_locals p assets account receiver evm imms
  exact ((morphoWithdrawCollateralSourceAuthorized p assets account receiver hc ha hr evm imms hcv hsize hg.1).requireStep
    (by rw [collateralTransferAuthorizedFrame_eval_c1, decide_eq_true hg.2])).letStep
    (evalAccrueActive p _ imms evm hc hl.toMarketLocals)

theorem morphoWithdrawCollateralSourceReject (p : MarketParamsWords)
    (assets account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ WithdrawCollateralGuards evm.accountMap evm.executionEnv p assets account receiver) :
    ExecTransitionBody config contract evm (collateralTransferArgs p assets account receiver)
      withdrawCollateralTransition.body .reverted imms := by
  by_cases hb : SupplyCollateralGuards evm.accountMap evm.executionEnv p assets receiver
  swap
  · exact morphoWithdrawCollateralSourceBasicReject p assets account receiver hc hr evm imms hcv hsize hb
  apply ExecFuncBody.execBlockRevert
  exact (morphoWithdrawCollateralSourceAuthorized p assets account receiver hc ha hr evm imms hcv hsize hb).requireRevert
    (by rw [collateralTransferAuthorizedFrame_eval_c1, decide_eq_false (fun h ↦ hg ⟨hb, h⟩)])

end Benchmarks.Morpho.MorphoBlue
