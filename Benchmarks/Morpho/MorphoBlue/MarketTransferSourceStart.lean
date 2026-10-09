import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals
import Benchmarks.Morpho.MorphoBlue.WithdrawGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- Borrow and withdraw have the same source prefix through captured accrual activity.
def marketTransferGuardBody (tail : List Stmt) : List Stmt := withdrawTransition.body.take 11 ++ tail

theorem morphoMarketTransferPrelude (tail : List Stmt) (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := marketTransferArgs p assets shares account receiver, immutables := imms }
      (marketTransferGuardBody tail) (marketTransferFrame p assets shares account receiver evm.executionEnv.calldata imms)
      ((marketTransferGuardBody tail).drop 4) := by
  refine ⟨fun h ↦ (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp [evalExpr?, marketTransferArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption])

theorem morphoMarketTransferExactlyOneZero (p : MarketParamsWords) (assets shares account receiver : UInt256)
     (evm : EVM.State) (imms : Store) :
    ExecStmt config (marketTransferFrame p assets shares account receiver evm.executionEnv.calldata imms) evm
      withdrawTransition.body[5]!
      (.ok (marketTransferInputFrame p assets shares account receiver evm.executionEnv.calldata imms) evm) := by
  have hl := marketTransferFrame_locals p assets shares account receiver evm.executionEnv.calldata imms
  apply morphoExactlyOneZeroCall
  have ha := hl.evalAssets imms evm
  have hs := hl.evalShares imms evm
  dsimp only [marketTransferFrame] at ha hs
  simp only [evalExprs?, ha, hs, pure, bind, EvalResult.bind]

theorem morphoMarketTransferSourceInput (tail : List Stmt) (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (hc : p.Canonical) (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := marketTransferArgs p assets shares account receiver, immutables := imms }
      (marketTransferGuardBody tail) (marketTransferInputFrame p assets shares account receiver evm.executionEnv.calldata imms)
      ((marketTransferGuardBody tail).drop 6) := by
  have hl := marketTransferFrame_locals p assets shares account receiver evm.executionEnv.calldata imms
  have pref := (morphoMarketTransferPrelude tail p assets shares account receiver hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hg] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  exact ⟨fun h ↦ pref.run (ExecBlock.consNormal (morphoMarketTransferExactlyOneZero p assets shares account receiver evm imms) h)⟩

theorem marketTransferInputFrame_eval_c1 (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (cd : ByteArray) (evm : EVM.State) (imms : Store) :
    evalExpr? config (marketTransferInputFrame p assets shares account receiver cd imms) evm (.var "__c1") =
      .ok (.bool (exactlyOneZero assets shares)) := by
  simp only [evalExpr?, marketTransferInputFrame, store_get_self, EvalResult.ofOption]


theorem marketTransferAuthorizedFrame_eval_c2 (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (evm : EVM.State) (imms : Store) :
    evalExpr? config (marketTransferAuthorizedFrame p assets shares account receiver evm imms) evm (.var "__c2") =
      .ok (.bool (decide (senderAuthorizedWord evm.accountMap evm.executionEnv account ≠ UInt256.ofNat 0))) := by
  simp only [evalExpr?, marketTransferAuthorizedFrame, store_get_self, EvalResult.ofOption, wordToElemBool, decide_not]
  rfl

theorem morphoMarketTransferSourceAuthorized (tail : List Stmt) (p : MarketParamsWords)
    (assets shares account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SupplyGuards evm.accountMap evm.executionEnv p assets shares receiver) :
    ABlock config evm { contract := contract, locals := marketTransferArgs p assets shares account receiver, immutables := imms }
      (marketTransferGuardBody tail) (marketTransferAuthorizedFrame p assets shares account receiver evm imms)
      ((marketTransferGuardBody tail).drop 9) := by
  have hl := marketTransferInputFrame_locals p assets shares account receiver evm.executionEnv.calldata imms
  have pref := ((morphoMarketTransferSourceInput tail p assets shares account receiver hc evm imms hcv hsize hg.1).requireStep
    (by rw [marketTransferInputFrame_eval_c1, hg.2.1])).requireStep
    (by simpa only [decide_eq_true hg.2.2] using evalCanonicalAddressNeZero hr (hl.evalReceiver imms evm))
  refine ⟨fun h ↦ pref.run (ExecBlock.consNormal ?_ h)⟩
  apply morphoSenderAuthorizedCall account imms _ evm _ "__c2" ha
  exact evalExprs?_singleton (hl.evalAccount imms evm)

theorem morphoMarketTransferSourceGuards (tail : List Stmt) (p : MarketParamsWords)
    (assets shares account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : WithdrawGuards evm.accountMap evm.executionEnv p assets shares account receiver) :
    ABlock config evm { contract := contract, locals := marketTransferArgs p assets shares account receiver, immutables := imms }
      (marketTransferGuardBody tail) (marketTransferBeforeAccrue p assets shares account receiver evm imms) tail := by
  have hl := marketTransferAuthorizedFrame_locals p assets shares account receiver evm imms
  exact ((morphoMarketTransferSourceAuthorized tail p assets shares account receiver hc ha hr evm imms hcv hsize hg.1).requireStep
    (by rw [marketTransferAuthorizedFrame_eval_c2, decide_eq_true hg.2])).letStep
    (evalAccrueActive p _ imms evm hc hl.toMarketLocals)

theorem morphoMarketTransferSourceReject (tail : List Stmt) (p : MarketParamsWords)
    (assets shares account receiver : UInt256) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : ¬ WithdrawGuards evm.accountMap evm.executionEnv p assets shares account receiver) :
    ExecTransitionBody config contract evm (marketTransferArgs p assets shares account receiver)
      (marketTransferGuardBody tail) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
  swap
  · have hl := marketTransferFrame_locals p assets shares account receiver evm.executionEnv.calldata imms
    exact (morphoMarketTransferPrelude tail p assets shares account receiver hc evm imms hcv hsize).requireRevert
      (by simpa only [decide_eq_false hcreated] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))
  have pref := morphoMarketTransferSourceInput tail p assets shares account receiver hc evm imms hcv hsize hcreated
  by_cases hz : exactlyOneZero assets shares = true
  swap
  · exact pref.requireRevert (by rw [marketTransferInputFrame_eval_c1, Bool.eq_false_iff.mpr hz])
  have hl := marketTransferInputFrame_locals p assets shares account receiver evm.executionEnv.calldata imms
  by_cases hn : receiver ≠ ⟨0⟩
  swap
  · exact (pref.requireStep (by rw [marketTransferInputFrame_eval_c1, hz])).requireRevert
      (by simpa only [decide_eq_false hn] using evalCanonicalAddressNeZero hr (hl.evalReceiver imms evm))
  exact (morphoMarketTransferSourceAuthorized tail p assets shares account receiver hc ha hr evm imms hcv hsize
    ⟨hcreated, hz, hn⟩).requireRevert
    (by rw [marketTransferAuthorizedFrame_eval_c2,
      decide_eq_false (fun h ↦ hg ⟨⟨hcreated, hz, hn⟩, h⟩)])

end Benchmarks.Morpho.MorphoBlue
