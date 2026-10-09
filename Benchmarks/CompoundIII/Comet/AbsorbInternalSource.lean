import Benchmarks.CompoundIII.Comet.AbsorbInternalModel
import Benchmarks.CompoundIII.Comet.AbsorbReadSource
import Benchmarks.CompoundIII.Comet.AbsorbBasePriceSource
import Benchmarks.CompoundIII.Comet.CollateralCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbInternalInitial_frame (v : CometWithExtendedAssetListImmutables)
    (absorber account : AccountAddress) (evm : State) (price : UInt256) :
    AbsorbLoopFrame v absorber account (absorbBasic evm account) (absorbOldBalance evm account)
      price 0 ⟨0⟩ (absorbInitialFrame
        (absorbBitsFrame (absorbInternalCheckedFrame v absorber account) evm account) price) := by
  constructor <;> simp only [absorbInitialFrame, absorbBasePriceFrame, absorbBitsFrame,
    absorbPresentFrame, absorbOldPrincipalFrame, absorbReadFrame, absorbInternalCheckedFrame,
    absorbInternalEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty] <;> rfl

theorem absorbReadTail_source {v : CometWithExtendedAssetListImmutables}
    {account : AccountAddress} {evm : State} {result : InternalOutcome}
    (ht : AbsorbReadTrace v account evm result) (absorber : AccountAddress) :
    internalBlockResult config (absorbInternalCheckedFrame v absorber account) evm
      absorbReadTailBlock result := by
  let frame := absorbInternalCheckedFrame v absorber account
  have ha : frame.locals.get? "account" = some (.address account) := by
    simp only [frame, absorbInternalCheckedFrame, absorbInternalEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  have hu : frame.locals.get? "userBasic" = none := by
    simp only [frame, absorbInternalCheckedFrame, absorbInternalEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl
  have hr := absorbRead_source frame evm account rfl ha hu
  have hp := absorbPresent_source frame evm account rfl
  cases ht with
  | minimum hm =>
      rw [if_neg hm] at hp
      exact execBlock_append hr (ExecBlock.consRevert hp)
  | present hm htail =>
      rw [if_pos hm] at hp
      have hb := absorbBasePrice_source htail (absorbBitsFrame frame evm account) rfl rfl
        (absorbInternalInitial_frame v absorber account evm)
      exact ((hb.prependBlock (absorbBits_source frame evm account)).prepend hp).prependBlock hr

theorem absorbInternal_source {v : CometWithExtendedAssetListImmutables}
    {account : AccountAddress} {evm : State} {result : InternalOutcome}
    (ht : AbsorbInternalTrace v account evm result) (absorber : AccountAddress) :
    internalSourceResult config (absorbInternalEntry v absorber account) evm
      absorbInternalCallable.body result := by
  apply internalBlockResult.toSource
  let frame := absorbInternalEntry v absorber account
  have ha : evalExpr? config frame evm (.var "account") = .ok (.address account) := by
    simp only [evalExpr?, frame, absorbInternalEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  cases ht with
  | checkReverted ht =>
      exact ExecBlock.consRevert (collateralCheck_call ht frame (.var "account") "__c0" rfl rfl ha)
  | notLiquidatable ht =>
      have hc := collateralCheck_call ht frame (.var "account") "__c0" rfl rfl ha
      apply ExecBlock.consNormal hc
      apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
  | liquidatable hc ht =>
      have hcall := collateralCheck_call hc frame (.var "account") "__c0" rfl rfl ha
      have hb := absorbReadTail_source ht absorber
      exact (hb.prepend (ExecStmt.requireTrue (by
        simp only [evalExpr?, absorbInternalCheckedFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl))).prepend hcall

theorem absorbInternal_call {v : CometWithExtendedAssetListImmutables}
    {account : AccountAddress} {evm : State} {result : InternalOutcome}
    (ht : AbsorbInternalTrace v account evm result) (frame : Frame) (absorber : AccountAddress)
    (absorberExpr accountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : evalExpr? config frame evm absorberExpr = .ok (.address absorber))
    (hb : evalExpr? config frame evm accountExpr = .ok (.address account)) :
    ExecStmt config frame evm (.internalCall "absorbInternal" [absorberExpr, accountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := absorbInternalCallable)
    (locals := (absorbInternalEntry v absorber account).locals)
    (argVals := [.address absorber, .address account])
  · simp only [evalExprs?, ha, hb, pure, bind, EvalResult.bind]
  · rw [hc]; exact absorbInternalCallable_lookup
  · rfl
  · simpa only [hc, hi] using absorbInternal_source ht absorber

end Benchmarks.CompoundIII.Comet
