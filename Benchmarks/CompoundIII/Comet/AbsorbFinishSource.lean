import Benchmarks.CompoundIII.Comet.AbsorbFinishModel
import Benchmarks.CompoundIII.Comet.AbsorbSettlementSource
import Benchmarks.CompoundIII.Comet.PrincipalValueSource
import Benchmarks.CompoundIII.Comet.UpdateBaseSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104 updateBaseOutcome

theorem absorbFinish_source (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : State) (absorber account : AccountAddress) (basic : UserBasicData)
    (old next price : UInt256) {result : InternalOutcome}
    (ht : AbsorbFinishTrace v evm account basic old next price result)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (hbasic : frame.locals.get? "accountUser" = some (userBasicValue basic))
    (ho : frame.locals.get? "oldBalance" = some (.int (signedWord old)))
    (hn : frame.locals.get? "newBalance" = some (.int (signedWord next)))
    (hp : frame.locals.get? "basePrice" = some (.int price.toNat))
    (hop : frame.locals.get? "oldPrincipal" = some (.int (signed104 basic.principal)))
    (hU : frame.locals.get? "userBasic" = none)
    (hS : frame.locals.get? "totalSupplyBase" = none)
    (hB : frame.locals.get? "totalBorrowBase" = none)
    (hI : frame.locals.get? "baseSupplyIndex" = none) (hnext : next.toNat < 2^255) :
    internalBlockResult config frame evm absorbFinishBlock result := by
  have hprincipal := principalValue_call frame evm next (.var "newBalance") "newPrincipal" hc
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
  let principal := absorbPrincipalFrame frame evm next
  let updated := absorbUpdatedFrame frame evm next
  have hget (key : String) (hc11 : "__c11" ≠ key) (hnp : "newPrincipal" ≠ key) :
      updated.locals.get? key = frame.locals.get? key := by
    simp only [updated, absorbUpdatedFrame, absorbPrincipalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hc11, if_neg hnp]
  have hupdate (hf : PrincipalValueFits evm next) := updateBase_call v principal evm account basic
    (principalValueWord evm next) (.var "account") (.var "accountUser") (.var "newPrincipal")
    "__c11" hc hi
    (by simp only [evalExpr?, principal, absorbPrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "account") = _
        rw [hb]; rfl)
    (by simp only [evalExpr?, principal, absorbPrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "accountUser") = _
        rw [hbasic]; rfl)
    (by simp only [evalExpr?, principal, absorbPrincipalFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption, principalValueWord_signed104 hf]; rfl)
  have htail {evm' result'} (hf : PrincipalValueFits evm next)
      (ht' : AbsorbSettlementTrace v evm' account basic.principal
        (principalValueWord evm next) old next price result') :=
    absorbSettlement_source updated v evm' absorber account basic.principal
      (principalValueWord evm next) old next price ht' hc hi
      ((hget _ (by decide) (by decide)).trans ha) ((hget _ (by decide) (by decide)).trans hb)
      ((hget _ (by decide) (by decide)).trans ho) ((hget _ (by decide) (by decide)).trans hn)
      ((hget _ (by decide) (by decide)).trans hp) ((hget _ (by decide) (by decide)).trans hop)
      (by simp only [updated, absorbUpdatedFrame, absorbPrincipalFrame,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            principalValueWord_signed104 hf]; rfl)
      ((hget _ (by decide) (by decide)).trans hU) ((hget _ (by decide) (by decide)).trans hS)
      ((hget _ (by decide) (by decide)).trans hB) ((hget _ (by decide) (by decide)).trans hI)
      hnext (principalValueWord_nonneg_lt hf ((signedWord_nonneg_iff next).2 hnext))
  change internalBlockResult config frame evm
    (.internalCall "principalValue" [.var "newBalance"] "newPrincipal" ::
      .internalCall "updateBasePrincipal" [.var "account", .var "accountUser", .var "newPrincipal"]
        "__c11" :: absorbSettlementBlock) result
  cases ht with
  | principalReverted hf =>
    rw [if_neg hf] at hprincipal
    exact ExecBlock.consRevert hprincipal
  | updateReverted hf hu =>
    rw [if_pos hf] at hprincipal
    exact (show internalBlockResult config principal evm _ .reverted from
      ExecBlock.consRevert (internalStmtResult.cast (hupdate hf) hu)).prepend hprincipal
  | updateStatic hf hu =>
    rw [if_pos hf] at hprincipal
    exact (show internalBlockResult config principal evm _ .staticViolation from
      ExecBlock.consStatic (internalStmtResult.cast (hupdate hf) hu)).prepend hprincipal
  | settled hf hu ht' =>
    rw [if_pos hf] at hprincipal
    exact ((htail hf ht').prepend (internalStmtResult.cast (hupdate hf) hu)).prepend hprincipal

end Benchmarks.CompoundIII.Comet
