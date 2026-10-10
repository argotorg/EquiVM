import Benchmarks.CompoundIII.Comet.AbsorbDebtSource
import Benchmarks.CompoundIII.Comet.AbsorbEventsSource
import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbDebtTail_source (frame : Frame) (evm : State)
    (v : CometWithExtendedAssetListImmutables) (absorber account : AccountAddress)
    (old next price principal : UInt256) (hc : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (ho : frame.locals.get? "oldBalance" = some (.int (signedWord old)))
    (hn : frame.locals.get? "newBalance" = some (.int (signedWord next)))
    (hp : frame.locals.get? "basePrice" = some (.int price.toNat))
    (hprincipal : frame.locals.get? "newPrincipal" = some (.int principal.toNat))
    (hindex : frame.locals.get? "baseSupplyIndex" = none)
    (hnext : next.toNat < 2^255) (hbound : principal.toNat < 2^104) :
    internalBlockResult config frame evm (absorbDebtArithmeticBlock ++ absorbEventsBlock)
      (if AbsorbDebtValid v old next price then .ok evm else .reverted) := by
  have hm := absorbDebtArithmetic_source frame evm v old next price hc hi ho hn hp hnext
  by_cases hv : AbsorbDebtValid v old next price
  · rw [if_pos hv] at hm ⊢
    let final := absorbDebtFrame frame v old next price
    have hget (key : String) (hpaid : "basePaidOut" ≠ key) (hvalue : "valueOfBasePaidOut" ≠ key) :
        final.locals.get? key = frame.locals.get? key := by
      simp only [final, absorbDebtFrame, absorbPaidFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hpaid, if_neg hvalue]
    obtain ⟨last, he⟩ := absorbEvents_source final evm absorber account
      (absorbPaidWord old next) (absorbDebtValue v old next price) principal hc
      ((hget _ (by decide) (by decide)).trans ha) ((hget _ (by decide) (by decide)).trans hb)
      (by simp only [final, absorbDebtFrame, absorbPaidFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]; rfl)
      (by simp only [final, absorbDebtFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]; rfl)
      ((hget _ (by decide) (by decide)).trans hprincipal)
      ((hget _ (by decide) (by decide)).trans hindex) hbound
    exact ⟨last, execBlock_append hm he⟩
  · rw [if_neg hv] at hm ⊢
    exact execBlock_reverted_append hm

end Benchmarks.CompoundIII.Comet
