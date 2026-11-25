import Benchmarks.Midnight.TakeOfferChecksSource
import Benchmarks.Midnight.Authorization

variable {fork : Ethereum.Fork}

/-! The source authorization check for the offer's ratifier. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeRatifierGuard : Expr :=
  .storage { base := "isAuthorized", steps :=
    [.mindex (.field (.var "offer") "maker"), .mindex (.field (.var "offer") "ratifier")] }

theorem evalTakeRatifierGuard {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract) (hb : frame.locals.get? "isAuthorized" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeRatifierGuard = .ok (.bool (decide
      (authorizationWord evm (UInt256.ofNat offer.maker.val) (UInt256.ofNat offer.ratifier.val) ≠
        ⟨0⟩))) := by
  apply evalAuthorization _ _ _ _ (addressWord_canonical _) (addressWord_canonical _) hc hb
  · simpa only [UInt256.toNat_ofNat_of_lt (Nat.lt_trans offer.maker.isLt (by decide)),
      accountAddress_ofNat_val] using evalOfferMaker (evm := evm) (cfg := config) ho
  · simpa only [UInt256.toNat_ofNat_of_lt (Nat.lt_trans offer.ratifier.isLt (by decide)),
      accountAddress_ofNat_val] using evalOfferRatifier (evm := evm) (cfg := config) ho

theorem takeRatifierSource {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract) (hb : frame.locals.get? "isAuthorized" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ha : authorizationWord evm (UInt256.ofNat offer.maker.val)
      (UInt256.ofNat offer.ratifier.val) ≠ ⟨0⟩) :
    ABlock fork config evm frame (takeTransition.body.drop 14) frame (takeTransition.body.drop 15) :=
  ABlock.start.requireStep ((evalTakeRatifierGuard hc hb ho).trans (by rw [decide_eq_true ha]))

theorem takeRatifierRevert {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract) (hb : frame.locals.get? "isAuthorized" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ha : authorizationWord evm (UInt256.ofNat offer.maker.val)
      (UInt256.ofNat offer.ratifier.val) = ⟨0⟩) :
    ExecBlock fork config frame evm (takeTransition.body.drop 14) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse ((evalTakeRatifierGuard hc hb ho).trans
    (by rw [decide_eq_false (not_not.mpr ha)])))

end Benchmarks.Midnight
