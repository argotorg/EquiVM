import Benchmarks.CompoundIII.Comet.AbsorbSettlementModel
import Benchmarks.CompoundIII.Comet.AbsorbRepaySource
import Benchmarks.CompoundIII.Comet.AbsorbRepayResult
import Benchmarks.CompoundIII.Comet.AbsorbDebtTailSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem absorbSettlement_source (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : State) (absorber account : AccountAddress)
    (oldPrincipal principal old next price : UInt256) {result : InternalOutcome}
    (ht : AbsorbSettlementTrace v evm account oldPrincipal principal old next price result)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (ho : frame.locals.get? "oldBalance" = some (.int (signedWord old)))
    (hn : frame.locals.get? "newBalance" = some (.int (signedWord next)))
    (hp : frame.locals.get? "basePrice" = some (.int price.toNat))
    (hop : frame.locals.get? "oldPrincipal" = some (.int (signed104 oldPrincipal)))
    (hnp : frame.locals.get? "newPrincipal" = some (.int (signed104 principal)))
    (hU : frame.locals.get? "userBasic" = none)
    (hS : frame.locals.get? "totalSupplyBase" = none)
    (hB : frame.locals.get? "totalBorrowBase" = none)
    (hI : frame.locals.get? "baseSupplyIndex" = none)
    (hnext : next.toNat < 2^255) (hprincipal : principal.toNat < 2^103) :
    internalBlockResult config frame evm absorbSettlementBlock result := by
  have hclear := absorbClear_source frame evm account hc hU hb
  have hrepay := absorbRepay_source frame (absorbClearState evm account) oldPrincipal principal
    hc hop hnp hS hB
  let repaid := absorbRepayFrame frame oldPrincipal principal
  have hget (key : String) (ht : "__c12" ≠ key) (hr : "repayAmount" ≠ key)
      (hs : "supplyAmount" ≠ key) : repaid.locals.get? key = frame.locals.get? key := by
    simp only [repaid, absorbRepayFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, if_neg ht, if_neg hr, if_neg hs]
  have htail (totaled : State) := absorbDebtTail_source repaid totaled v absorber account
    old next price principal hc hi
    ((hget _ (by decide) (by decide) (by decide)).trans ha)
    ((hget _ (by decide) (by decide) (by decide)).trans hb)
    ((hget _ (by decide) (by decide) (by decide)).trans ho)
    ((hget _ (by decide) (by decide) (by decide)).trans hn)
    ((hget _ (by decide) (by decide) (by decide)).trans hp)
    (by rw [hget _ (by decide) (by decide) (by decide), hnp, signed104_low hprincipal]; rfl)
    ((hget _ (by decide) (by decide) (by decide)).trans hI)
    hnext (lt_trans hprincipal (by decide))
  change internalBlockResult config frame evm
    (absorbClearBlock ++ (absorbRepayBlock ++ (absorbDebtArithmeticBlock ++ absorbEventsBlock))) result
  refine internalBlockResult.prependBlock ?_ hclear
  cases ht with
  | repayReverted hr =>
    exact execBlock_reverted_append (absorbRepay_result hrepay hr)
  | repayStatic hr =>
    exact execBlock_append_term (absorbRepay_result hrepay hr) (by intro _ _ he; cases he)
  | debtReverted totaled hr hd =>
    have hb := htail totaled
    rw [if_neg hd] at hb
    exact hb.prependBlock (absorbRepay_result hrepay hr)
  | ok totaled hr hd =>
    have hb := htail totaled
    rw [if_pos hd] at hb
    exact hb.prependBlock (absorbRepay_result hrepay hr)

end Benchmarks.CompoundIII.Comet
