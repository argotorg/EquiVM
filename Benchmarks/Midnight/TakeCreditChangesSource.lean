import Benchmarks.Midnight.TakePositionUpdatesValues
import Benchmarks.Midnight.WordMin

/-! Credit and debt deltas are computed from the state after both position updates. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerCreditIncrease (evm : State) (id buyer units : UInt256) : UInt256 :=
  zeroFloorSubWord units (low128 (healthPositionWord evm id buyer))

def takeSellerCreditDecrease (evm : State) (id seller units : UInt256) : UInt256 :=
  wordMin units (positionFieldWord evm id seller 0)

def takeSellerDebtIncrease (evm : State) (id seller units : UInt256) : UInt256 :=
  UInt256.sub units (takeSellerCreditDecrease evm id seller units)

def takeBuyerCreditFrame (frame : Frame) (evm : State) (id buyer units : UInt256) : Frame :=
  wordLocal frame "buyerCreditIncrease" (takeBuyerCreditIncrease evm id buyer units)

def takeSellerCreditChangeFrame (frame : Frame) (evm : State)
    (id buyer seller units : UInt256) : Frame :=
  wordLocal (takeBuyerCreditFrame frame evm id buyer units) "sellerCreditDecrease"
    (takeSellerCreditDecrease evm id seller units)

def takeCreditChangesFrame (frame : Frame) (evm : State)
    (id buyer seller units : UInt256) : Frame :=
  wordLocal (takeSellerCreditChangeFrame frame evm id buyer seller units) "sellerDebtIncrease"
    (takeSellerDebtIncrease evm id seller units)

theorem takeCreditChanges_shape : takeTransition.body.drop 35 =
    takeTransition.body[35]! :: takeTransition.body[36]! :: takeTransition.body[37]! ::
      takeTransition.body.drop 38 := rfl

-- LIBRARY CANDIDATE: the branchless minimum never exceeds its first operand.
theorem wordMin_le_left (x y : UInt256) : (wordMin x y).toNat ≤ x.toNat := by
  unfold wordMin
  split <;> omega

theorem takeBuyerCreditSource {frame : Frame} {evm : State} {id buyer units : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hcanon : buyer.toNat < EVM.addressModulus) :
    ExecStmt config frame evm takeTransition.body[35]!
      (.ok (takeBuyerCreditFrame frame evm id buyer units) evm) := by
  apply callZeroFloorSub hc
  simp only [evalExprs?, evalWordLocal hu, evalNamedPositionDebt hcanon hp,
    bind, pure, EvalResult.bind]

theorem takeSellerCreditSourceChange {frame : Frame} {evm : State} {id seller units : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hcanon : seller.toNat < EVM.addressModulus) :
    ExecStmt config frame evm takeTransition.body[36]!
      (.ok (wordLocal frame "sellerCreditDecrease" (takeSellerCreditDecrease evm id seller units))
        evm) := by
  apply callMin hc
  have he := evalNamedPositionField (evm := evm) 0 hcanon hp
  change evalExpr? config frame evm (.storage { base := "sellerPos", steps := [.field "credit"] }) =
    .ok (.int (positionFieldWord evm id seller 0).toNat) at he
  simp only [evalExprs?, evalWordLocal hu, he, bind, pure, EvalResult.bind]

theorem takeCreditChangesSource {frame : Frame} {evm : State} {offer : OfferData}
    {id buyer seller units taker : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hs : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hbc : buyer.toNat < EVM.addressModulus) (hsc : seller.toNat < EVM.addressModulus) :
    ABlock config evm frame (takeTransition.body.drop 35)
      (takeCreditChangesFrame frame evm id buyer seller units) (takeTransition.body.drop 38) := by
  have hf1 := hf.insert "buyerCreditIncrease"
    (.int (takeBuyerCreditIncrease evm id buyer units).toNat) (by decide)
  have hf2 := hf1.insert "sellerCreditDecrease"
    (.int (takeSellerCreditDecrease evm id seller units).toNat) (by decide)
  rw [takeCreditChanges_shape]
  refine ⟨fun h ↦ ExecBlock.consNormal (takeBuyerCreditSource hf.contract hb hf.units hbc)
    (ExecBlock.consNormal (takeSellerCreditSourceChange hf1.contract
      ((store_get_ne _ _ (by decide)).trans hs) hf1.units hsc)
      (ExecBlock.consNormal (ExecStmt.letDecl ?_) h))⟩
  exact evalExpr_uint256_sub (evalWordLocal hf2.units) (evalWordLocal (wordLocal_get ..))
    (wordMin_le_left units (positionFieldWord evm id seller 0))

theorem TakeSourceFrame.creditChanges {frame : Frame} {evm : State} {offer : OfferData}
    {id buyer seller units taker : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeCreditChangesFrame frame evm id buyer seller units) offer id units taker
      receiver callback ratifierData data :=
  ((hf.insert "buyerCreditIncrease" _ (by decide)).insert
    "sellerCreditDecrease" _ (by decide)).insert
    "sellerDebtIncrease" _ (by decide)

end Benchmarks.Midnight
