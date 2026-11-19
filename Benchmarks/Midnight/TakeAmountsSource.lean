import Benchmarks.Midnight.TakeAmountCall

/-! Source execution of both asset calculations in the selected offer branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeAmountsInit (frame : Frame) : Frame :=
  wordLocal (wordLocal frame "buyerAssets" ⟨0⟩) "sellerAssets" ⟨0⟩

def takeAmountsBuyerFrame (frame : Frame) (buy units buyerPrice : UInt256) : Frame :=
  takeAmountStepFrame (takeAmountsInit frame) buy units buyerPrice "bought" "buyerAssets"

def takeAmountsFrame (frame : Frame) (buy units buyerPrice sellerPrice : UInt256) : Frame :=
  takeAmountStepFrame (takeAmountsBuyerFrame frame buy units buyerPrice) buy units sellerPrice
    "sold" "sellerAssets"

def takeAmountsBranch (buy : UInt256) : List Stmt :=
  takeAmountStep buy "buyerPrice" "bought" "buyerAssets" ++
    takeAmountStep buy "sellerPrice" "sold" "sellerAssets"

theorem takeAmountsInit_get (frame : Frame) (name : Ident)
    (hb : name ≠ "buyerAssets") (hs : name ≠ "sellerAssets") :
    (takeAmountsInit frame).locals.get? name = frame.locals.get? name := by
  exact (wordLocal_get_ne _ _ _ _ hs.symm).trans (wordLocal_get_ne _ _ _ _ hb.symm)

theorem takeAmountsBuyerFrame_get (frame : Frame) (buy units buyerPrice : UInt256) (name : Ident)
    (hb : name ≠ "buyerAssets") (hs : name ≠ "sellerAssets") (ht : name ≠ "bought") :
    (takeAmountsBuyerFrame frame buy units buyerPrice).locals.get? name =
      frame.locals.get? name := by
  exact (wordLocal_get_ne _ _ _ _ hb.symm).trans
    ((wordLocal_get_ne _ _ _ _ ht.symm).trans (takeAmountsInit_get frame name hb hs))

theorem takeAmountsBuyerFrame_seller (frame : Frame) (buy units buyerPrice : UInt256) :
    (takeAmountsBuyerFrame frame buy units buyerPrice).locals.get? "sellerAssets" =
      some (.int 0) :=
  (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self ..))

theorem takeAmounts_shape : takeTransition.body.drop 22 =
    .letDecl "buyerAssets" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0) ::
    .letDecl "sellerAssets" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0) ::
    .ite (.field (.var "offer") "buy") (takeAmountsBranch ⟨1⟩) (takeAmountsBranch ⟨0⟩) ::
    takeTransition.body.drop 25 := rfl

theorem takeAmountsBranchSource {frame : Frame} {evm : State}
    {buy units buyerPrice sellerPrice : UInt256}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hb : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hs : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (hsafe : TakeAmountSafe buy units buyerPrice ∧ TakeAmountSafe buy units sellerPrice) :
    ExecBlock config (takeAmountsInit frame) evm (takeAmountsBranch buy)
      (.ok (takeAmountsFrame frame buy units buyerPrice sellerPrice) evm) := by
  have hbuyer := takeAmountStepSource (cfg := config) (evm := evm) (frame := takeAmountsInit frame)
    (name := "bought") (target := "buyerAssets") hc
    ((takeAmountsInit_get frame "units" (by decide) (by decide)).trans hu)
    ((takeAmountsInit_get frame "buyerPrice" (by decide) (by decide)).trans hb)
    ((store_get_ne _ _ (by decide)).trans (store_get_self ..)) (by decide) hsafe.1
  apply execBlock_append_ok hbuyer
  exact takeAmountStepSource (frame := takeAmountsBuyerFrame frame buy units buyerPrice)
    (name := "sold") (target := "sellerAssets") hc
    ((takeAmountsBuyerFrame_get frame buy units buyerPrice "units"
      (by decide) (by decide) (by decide)).trans hu)
    ((takeAmountsBuyerFrame_get frame buy units buyerPrice "sellerPrice"
      (by decide) (by decide) (by decide)).trans hs)
    (takeAmountsBuyerFrame_seller ..) (by decide) hsafe.2

theorem takeAmountsBranchRevert {frame : Frame} {evm : State}
    {buy units buyerPrice sellerPrice : UInt256}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hb : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hs : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (hbad : ¬ (TakeAmountSafe buy units buyerPrice ∧ TakeAmountSafe buy units sellerPrice)) :
    ExecBlock config (takeAmountsInit frame) evm (takeAmountsBranch buy) .reverted := by
  by_cases hsafe : TakeAmountSafe buy units buyerPrice
  · have hbuyer := takeAmountStepSource (cfg := config) (evm := evm)
      (frame := takeAmountsInit frame)
      (name := "bought") (target := "buyerAssets") hc
      ((takeAmountsInit_get frame "units" (by decide) (by decide)).trans hu)
      ((takeAmountsInit_get frame "buyerPrice" (by decide) (by decide)).trans hb)
      ((store_get_ne _ _ (by decide)).trans (store_get_self ..)) (by decide) hsafe
    apply execBlock_append_ok hbuyer
    exact ExecBlock.consRevert (takeAmountCallRevert
      (frame := takeAmountsBuyerFrame frame buy units buyerPrice) hc
      ((takeAmountsBuyerFrame_get frame buy units buyerPrice "units"
        (by decide) (by decide) (by decide)).trans hu)
      ((takeAmountsBuyerFrame_get frame buy units buyerPrice "sellerPrice"
        (by decide) (by decide) (by decide)).trans hs)
      (fun h ↦ hbad ⟨hsafe, h⟩))
  · exact ExecBlock.consRevert (takeAmountCallRevert (frame := takeAmountsInit frame) hc
      ((takeAmountsInit_get frame "units" (by decide) (by decide)).trans hu)
      ((takeAmountsInit_get frame "buyerPrice" (by decide) (by decide)).trans hb) hsafe)

theorem takeAmountsSource {frame : Frame} {evm : State} {offer : OfferData}
    {units buyerPrice sellerPrice : UInt256}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hs : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (hsafe : TakeAmountSafe offer.buy units buyerPrice ∧
      TakeAmountSafe offer.buy units sellerPrice) :
    ABlock config evm frame (takeTransition.body.drop 22)
      (takeAmountsFrame frame offer.buy units buyerPrice sellerPrice)
      (takeTransition.body.drop 25) := by
  have he := evalOfferBuy (cfg := config) (evm := evm)
    ((takeAmountsInit_get frame "offer" (by decide) (by decide)).trans ho)
  rw [wordToElemBool] at he
  have hx := takeAmountsBranchSource (evm := evm) hc hu hb hs hsafe
  have hi : ExecStmt config (takeAmountsInit frame) evm
      (.ite (.field (.var "offer") "buy") (takeAmountsBranch ⟨1⟩) (takeAmountsBranch ⟨0⟩))
      (.ok (takeAmountsFrame frame offer.buy units buyerPrice sellerPrice) evm) := by
    by_cases hbuy : offer.buy = ⟨0⟩
    · apply ExecStmt.iteFalse (by simpa only [hbuy, decide_true, Bool.not_true] using he)
      simpa only [takeAmountsBranch, takeAmountStep, takeAmountCall, if_pos hbuy,
        show (⟨0⟩ : UInt256) = ⟨0⟩ from rfl, if_true] using hx
    · apply ExecStmt.iteTrue (by simpa only [hbuy, decide_false, Bool.not_false] using he)
      simpa only [takeAmountsBranch, takeAmountStep, takeAmountCall, if_neg hbuy,
        show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide, if_false] using hx
  rw [takeAmounts_shape]
  exact ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
      (ExecBlock.consNormal hi h))⟩

theorem takeAmountsSourceRevert {frame : Frame} {evm : State} {offer : OfferData}
    {units buyerPrice sellerPrice : UInt256}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hs : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (hbad : ¬ (TakeAmountSafe offer.buy units buyerPrice ∧
      TakeAmountSafe offer.buy units sellerPrice)) :
    ExecBlock config frame evm (takeTransition.body.drop 22) .reverted := by
  have he := evalOfferBuy (cfg := config) (evm := evm)
    ((takeAmountsInit_get frame "offer" (by decide) (by decide)).trans ho)
  rw [wordToElemBool] at he
  have hx := takeAmountsBranchRevert (evm := evm) hc hu hb hs hbad
  have hi : ExecStmt config (takeAmountsInit frame) evm
      (.ite (.field (.var "offer") "buy") (takeAmountsBranch ⟨1⟩) (takeAmountsBranch ⟨0⟩))
      .reverted := by
    by_cases hbuy : offer.buy = ⟨0⟩
    · apply ExecStmt.iteFalse (by simpa only [hbuy, decide_true, Bool.not_true] using he)
      simpa only [takeAmountsBranch, takeAmountStep, takeAmountCall, if_pos hbuy,
        show (⟨0⟩ : UInt256) = ⟨0⟩ from rfl, if_true] using hx
    · apply ExecStmt.iteTrue (by simpa only [hbuy, decide_false, Bool.not_false] using he)
      simpa only [takeAmountsBranch, takeAmountStep, takeAmountCall, if_neg hbuy,
        show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide, if_false] using hx
  rw [takeAmounts_shape]
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl))
      (ExecBlock.consRevert hi))

theorem TakeSourceFrame.amounts {frame : Frame} {offer : OfferData}
    {id units taker buyerPrice sellerPrice : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeAmountsFrame frame offer.buy units buyerPrice sellerPrice) offer
      id units taker receiver callback ratifierData data :=
  (((((hf.insert "buyerAssets" (.int 0) (by decide)).insert "sellerAssets" (.int 0)
    (by decide)).insert "bought" (.int (takeAmount offer.buy units buyerPrice).toNat)
    (by decide)).insert "buyerAssets" (.int (takeAmount offer.buy units buyerPrice).toNat)
    (by decide)).insert "sold" (.int (takeAmount offer.buy units sellerPrice).toNat)
    (by decide)).insert "sellerAssets" (.int (takeAmount offer.buy units sellerPrice).toNat)
    (by decide)

end Benchmarks.Midnight
