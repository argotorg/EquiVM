import Benchmarks.Midnight.ClaimFeeSourceFrames
import Benchmarks.Midnight.ClaimFeeArithmeticSource
import Benchmarks.Midnight.SafeTransferSource

/-! Source composition of continuous-fee claims. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

attribute [local simp] wordLocal_get wordLocal_get_ne

theorem claimFeeCredit_get (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    let frame := claimFeeCreditFrame evm m amount receiver
    frame.contract = contract ∧ frame.locals.get? "amount" = some (.int amount.toNat) ∧
      frame.locals.get? "_marketState" = some (.storageRef (marketStateRef m.id) marketStateType) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [claimFeeCreditFrame, wordLocal_get_ne _ _ _ _ (by decide : "__c1" ≠ "amount")]
    exact (claimFeeAlias_get evm m amount receiver).2.1
  · rw [claimFeeCreditFrame, wordLocal_get_ne _ _ _ _ (by decide : "__c1" ≠ "_marketState")]
    exact (claimFeeAlias_get evm m amount receiver).2.2

theorem claimFeeUnits_get (evm : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    let frame := claimFeeUnitsFrame evm m amount receiver
    frame.contract = contract ∧ frame.locals.get? "amount" = some (.int amount.toNat) ∧
      frame.locals.get? "_marketState" = some (.storageRef (marketStateRef m.id) marketStateType) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [claimFeeUnitsFrame, wordLocal_get_ne _ _ _ _ (by decide : "__c2" ≠ "amount")]
    exact (claimFeeCredit_get evm m amount receiver).2.1
  · rw [claimFeeUnitsFrame, wordLocal_get_ne _ _ _ _ (by decide : "__c2" ≠ "_marketState")]
    exact (claimFeeCredit_get evm m amount receiver).2.2

theorem claimFeeCreditSource {evm evm' : EVM.State} {m : MarketData} {amount receiver : UInt256}
    {result : ExecResult} (hamount : amount.toNat < 2^128)
    (hle : amount.toNat ≤ (marketBalanceWord evm' m.id 2).toNat)
    (hperm : evm'.executionEnv.perm = true)
    (htail : ExecBlock config (claimFeeCreditFrame evm m amount receiver)
      (claimFeeCreditState evm' m.id amount) (claimContinuousFeeTransition.body.drop 8) result) :
    ExecBlock config (claimFeeAliasFrame evm m amount receiver) evm'
      (claimContinuousFeeTransition.body.drop 6) result := by
  have hg := claimFeeAlias_get evm m amount receiver
  exact claimFeeSubtractSource 2 "__c1" (by decide) hg.1 hg.2.1 hg.2.2 hamount hle hperm htail

theorem claimFeeUnitsSource {evm evm' : EVM.State} {m : MarketData} {amount receiver : UInt256}
    {result : ExecResult} (hamount : amount.toNat < 2^128)
    (hle : amount.toNat ≤ (marketBalanceWord (claimFeeCreditState evm' m.id amount) m.id 0).toNat)
    (hperm : evm'.executionEnv.perm = true)
    (htail : ExecBlock config (claimFeeUnitsFrame evm m amount receiver)
      (claimFeeUnitsState evm' m.id amount) (claimContinuousFeeTransition.body.drop 10) result) :
    ExecBlock config (claimFeeCreditFrame evm m amount receiver)
      (claimFeeCreditState evm' m.id amount) (claimContinuousFeeTransition.body.drop 8) result := by
  have hg := claimFeeCredit_get evm m amount receiver
  exact claimFeeSubtractSource 0 "__c2" (by decide) hg.1 hg.2.1 hg.2.2 hamount hle
    (by simpa only [claimFeeCreditState_env] using hperm) htail

theorem claimFeeWithdrawableSource {evm evm' : EVM.State} {m : MarketData} {amount receiver : UInt256}
    {result : ExecResult} (hamount : amount.toNat < 2^128)
    (hle : amount.toNat ≤ (marketBalanceWord (claimFeeUnitsState evm' m.id amount) m.id 1).toNat)
    (hperm : evm'.executionEnv.perm = true)
    (htail : ExecBlock config (claimFeeFinalFrame evm m amount receiver)
      (claimFeeFinalState evm' m.id amount) (claimContinuousFeeTransition.body.drop 12) result) :
    ExecBlock config (claimFeeUnitsFrame evm m amount receiver)
      (claimFeeUnitsState evm' m.id amount) (claimContinuousFeeTransition.body.drop 10) result := by
  have hg := claimFeeUnits_get evm m amount receiver
  exact claimFeeSubtractSource 1 "__c3" (by decide) hg.1 hg.2.1 hg.2.2 hamount hle
    (by simpa only [claimFeeUnitsState_env] using hperm) htail

theorem claimFeeEmitPrefix (evm evm' : EVM.State) (m : MarketData) (amount receiver : UInt256)
    (hperm : evm'.executionEnv.perm = true) :
    ABlock config evm' (claimFeeFinalFrame evm m amount receiver)
      (claimContinuousFeeTransition.body.drop 12) (claimFeeFinalFrame evm m amount receiver)
      (claimContinuousFeeTransition.body.drop 13) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm'.executionEnv.source, wordBytes32Value m.id, .int amount.toNat,
      .address (AccountAddress.ofNat receiver.toNat)]) hperm ?_) h⟩
  simp [evalExprs?, evalExpr?, envValue, claimFeeFinalFrame, claimFeeUnitsFrame, claimFeeCreditFrame,
    claimFeeAliasFrame, claimFeeAfterTouchFrame, resumeAfterInternalCall, claimFeeExternalFrame,
    calldataFrame, marketAmountAccountArguments, collapseReturns, wordLocal,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem evalClaimFeeTransferArgs (evm evm' : EVM.State) (m : MarketData) (amount receiver : UInt256) :
    evalExprs? config (claimFeeFinalFrame evm m amount receiver) evm'
      [.field (.var "market") "loanToken", .var "receiver", .var "amount"] =
      .ok [.address m.loanToken, .address (AccountAddress.ofNat receiver.toNat), .int amount.toNat] := by
  simp [evalExprs?, evalExpr?, claimFeeFinalFrame, claimFeeUnitsFrame, claimFeeCreditFrame,
    claimFeeAliasFrame, claimFeeAfterTouchFrame, resumeAfterInternalCall, claimFeeExternalFrame,
    calldataFrame, marketAmountAccountArguments, collapseReturns, wordLocal,
    Model.marketValue, MarketData.value, lookupField?, lookupAssoc, EvalResult.ofOption, EvalResult.bind,
    bind, pure, Std.HashMap.getElem_insert]

theorem claimFeeBodyBlock {evm evm' : EVM.State} {m : MarketData} {amount receiver : UInt256}
    {frame : Frame} {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body
      (.returned frame evm' (some [wordBytes32Value m.id])))
    (hauth : roleAllowed evm' ⟨11⟩)
    (htail : ExecBlock config (claimFeeAliasFrame evm m amount receiver) evm'
      (claimContinuousFeeTransition.body.drop 6) result) :
    ExecBlock config { contract := contract, immutables := ∅, locals :=
      marketAmountAccountArguments "receiver" m amount (AccountAddress.ofNat receiver.toNat) } evm
      claimContinuousFeeTransition.body result := by
  apply guardedBodyBlock hwv hhi
  apply claimFeeAfterTouchSource htouch
  apply (claimFeeBindAlias evm evm' m amount receiver).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  simpa only [decide_eq_true hauth] using claimFeeAuthEval evm evm' m amount receiver

end Benchmarks.Midnight
