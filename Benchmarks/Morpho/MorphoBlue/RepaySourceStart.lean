import Benchmarks.Morpho.MorphoBlue.SupplySourceStart
import Benchmarks.Morpho.MorphoBlue.RepayGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoRepayPrelude (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      repayTransition.body (supplyFrame p assets shares account data evm.executionEnv.calldata imms)
      (repayTransition.body.drop 4) := by
  refine ⟨fun h ↦ (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, supplyArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption])

theorem morphoRepaySourceInput (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      repayTransition.body (supplyInputFrame p assets shares account data evm.executionEnv.calldata imms)
      (repayTransition.body.drop 6) := by
  have hl := supplyFrame_locals p assets shares account data evm.executionEnv.calldata imms
  have pref := (morphoRepayPrelude p assets shares account data hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  exact ⟨fun h ↦ pref.run (ExecBlock.consNormal (morphoSupplyExactlyOneZero p assets shares account data evm imms) h)⟩

theorem morphoRepaySourceGuards (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyGuards evm.accountMap evm.executionEnv p assets shares account) :
    ABlock config evm { contract := contract, locals := supplyArgs p assets shares account data, immutables := imms }
      repayTransition.body (supplyBeforeAccrue p assets shares account data evm imms)
      (repayTransition.body.drop 9) := by
  have hl := supplyInputFrame_locals p assets shares account data evm.executionEnv.calldata imms
  exact (((morphoRepaySourceInput p assets shares account data hc evm imms hcv hsize hg.1).requireStep
    (by rw [supplyInputFrame_eval_c1, hg.2.1])).requireStep
    (by simpa only [decide_eq_true hg.2.2] using evalCanonicalAddressNeZero ha (hl.evalAccount imms evm))).letStep
    (evalAccrueActive p _ imms evm hc hl.toMarketLocals)

theorem morphoRepaySourceReject (p : MarketParamsWords) (assets shares account : UInt256) (data : ByteArray)
    (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ SupplyGuards evm.accountMap evm.executionEnv p assets shares account) :
    ExecTransitionBody config contract evm (supplyArgs p assets shares account data)
      repayTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · have hl := supplyFrame_locals p assets shares account data evm.executionEnv.calldata imms
    exact (morphoRepayPrelude p assets shares account data hc evm imms hcv hsize).requireRevert
      (by simpa only [decide_eq_false hcreated] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  have pref := morphoRepaySourceInput p assets shares account data hc evm imms hcv hsize hcreated
  by_cases hz : exactlyOneZero assets shares = true
  swap
  · exact pref.requireRevert (by rw [supplyInputFrame_eval_c1, Bool.eq_false_iff.mpr hz])
  have hl := supplyInputFrame_locals p assets shares account data evm.executionEnv.calldata imms
  exact (pref.requireStep (by rw [supplyInputFrame_eval_c1, hz])).requireRevert
    (by simpa only [decide_eq_false (fun hn ↦ hg ⟨hcreated, hz, hn⟩)] using
      evalCanonicalAddressNeZero ha (hl.evalAccount imms evm))

end Benchmarks.Morpho.MorphoBlue
