import Benchmarks.CompoundIII.Comet.TrackingAccrualModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem trackingBranchFrame_contract (frame evm v borrow elapsed) :
    (trackingBranchFrame frame evm v borrow elapsed).contract = frame.contract := by
  unfold trackingBranchFrame
  split <;> rfl

theorem trackingBranchFrame_immutables (frame evm v borrow elapsed) :
    (trackingBranchFrame frame evm v borrow elapsed).immutables = frame.immutables := by
  unfold trackingBranchFrame
  split <;> rfl

theorem trackingBranchFrame_get (frame evm v borrow elapsed name)
    (hd : trackingDivName borrow ≠ name) (hs : trackingSafeName borrow ≠ name) :
    (trackingBranchFrame frame evm v borrow elapsed).locals.get? name = frame.locals.get? name := by
  unfold trackingBranchFrame
  split
  · simp only [trackingAccrualFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_eq_false_iff_ne.mpr hd, beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true, if_false]
  · rfl

theorem trackingBranchFrame_eval (frame evm v borrow elapsed name evm')
    (hd : trackingDivName borrow ≠ name) (hs : trackingSafeName borrow ≠ name) :
    evalExpr? config (trackingBranchFrame frame evm v borrow elapsed) evm' (.var name) =
      evalExpr? config frame evm (.var name) := by
  simp only [evalExpr?, trackingBranchFrame_get _ _ _ _ _ _ hd hs]

end Benchmarks.CompoundIII.Comet
