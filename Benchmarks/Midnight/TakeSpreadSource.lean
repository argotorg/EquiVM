import Benchmarks.Midnight.TakeSpread

variable {fork : Ethereum.Fork}

/-! Source checked arithmetic for the seller and buyer prices. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeSellerPriceExpr : Expr :=
  .ite (.field (.var "offer") "buy")
    (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "offerPrice") (.var "_settlementFee")))
    (.var "offerPrice")

def takeBuyerPriceExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "sellerPrice") (.var "_settlementFee"))

def takeSellerFrame (frame : Frame) (buy price fee : UInt256) : Frame :=
  wordLocal frame "sellerPrice" (takeSellerPrice buy price fee)

def takeSpreadFrame (frame : Frame) (buy price fee : UInt256) : Frame :=
  wordLocal (takeSellerFrame frame buy price fee) "buyerPrice" (takeBuyerPrice buy price fee)

theorem takeSpread_shape : takeTransition.body.drop 20 =
    .letDecl "sellerPrice" (some (.elem (.int (.uint ⟨256, by decide⟩)))) takeSellerPriceExpr ::
    .letDecl "buyerPrice" (some (.elem (.int (.uint ⟨256, by decide⟩)))) takeBuyerPriceExpr ::
    takeTransition.body.drop 22 := rfl

theorem TakeSourceFrame.spread {frame : Frame} {offer : OfferData}
    {id units taker price fee : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeSpreadFrame frame offer.buy price fee) offer id units taker receiver
      callback ratifierData data :=
  (hf.insert "sellerPrice" (.int (takeSellerPrice offer.buy price fee).toNat) (by decide)).insert
    "buyerPrice" (.int (takeBuyerPrice offer.buy price fee).toNat) (by decide)

theorem evalTakeSellerPrice {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {price fee : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "offerPrice" = some (.int price.toNat))
    (hf : frame.locals.get? "_settlementFee" = some (.int fee.toNat))
    (hs : offer.buy ≠ ⟨0⟩ → fee.toNat ≤ price.toNat) :
    evalExpr? cfg frame evm takeSellerPriceExpr =
      .ok (.int (takeSellerPrice offer.buy price fee).toNat) := by
  rw [takeSellerPriceExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hb : offer.buy = ⟨0⟩
  · simp only [hb, decide_true, Bool.not_true, takeSellerPrice, if_true]
    exact evalWordLocal hp
  · simp only [hb, decide_false, Bool.not_false, takeSellerPrice, if_false]
    exact evalExpr_uint256_sub (evalWordLocal hp) (evalWordLocal hf) (hs hb)

theorem evalTakeSellerPriceRevert {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {price fee : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "offerPrice" = some (.int price.toNat))
    (hf : frame.locals.get? "_settlementFee" = some (.int fee.toNat))
    (hb : offer.buy ≠ ⟨0⟩) (hlt : price.toNat < fee.toNat) :
    evalExpr? cfg frame evm takeSellerPriceExpr = .revert := by
  rw [takeSellerPriceExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, hb, decide_false, Bool.not_false, bind, EvalResult.bind]
  exact evalCheckedSubUnderflow ⟨256, by decide⟩ (evalWordLocal hp) (evalWordLocal hf) hlt

theorem takeSpreadSource {frame : Frame} {evm : State} {offer : OfferData} {price fee : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "offerPrice" = some (.int price.toNat))
    (hf : frame.locals.get? "_settlementFee" = some (.int fee.toNat))
    (hs : TakeSpreadSafe offer.buy price fee) :
    ABlock fork config evm frame (takeTransition.body.drop 20)
      (takeSpreadFrame frame offer.buy price fee) (takeTransition.body.drop 22) := by
  rw [takeSpread_shape]
  have hf1 : (takeSellerFrame frame offer.buy price fee).locals.get? "_settlementFee" =
      some (.int fee.toNat) := (store_get_ne _ _ (by decide)).trans hf
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl (evalTakeSellerPrice ho hp hf hs.1))
    (ExecBlock.consNormal (ExecStmt.letDecl ?_) h)⟩
  exact checkedAddSourceOk (evalWordLocal (wordLocal_get ..)) (evalWordLocal hf1) hs.2

theorem takeSpreadSourceRevert {frame : Frame} {evm : State} {offer : OfferData}
    {price fee : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "offerPrice" = some (.int price.toNat))
    (hf : frame.locals.get? "_settlementFee" = some (.int fee.toNat))
    (hs : ¬ TakeSpreadSafe offer.buy price fee) :
    ExecBlock fork config frame evm (takeTransition.body.drop 20) .reverted := by
  rw [takeSpread_shape]
  by_cases hsub : offer.buy ≠ ⟨0⟩ → fee.toNat ≤ price.toNat
  · have hadd : UInt256.size ≤ (takeSellerPrice offer.buy price fee).toNat + fee.toNat := by
      by_contra h
      exact hs ⟨hsub, by omega⟩
    have hf1 : (takeSellerFrame frame offer.buy price fee).locals.get? "_settlementFee" =
        some (.int fee.toNat) := (store_get_ne _ _ (by decide)).trans hf
    apply ExecBlock.consNormal (ExecStmt.letDecl (evalTakeSellerPrice ho hp hf hsub))
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (checkedAddSourceOverflow (evalWordLocal (wordLocal_get ..)) (evalWordLocal hf1) hadd))
  · have hb : offer.buy ≠ ⟨0⟩ := fun h ↦ hsub (fun hn ↦ False.elim (hn h))
    have hlt : price.toNat < fee.toNat := by
      by_contra h
      exact hsub (fun _ ↦ by omega)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalTakeSellerPriceRevert ho hp hf hb hlt))

end Benchmarks.Midnight
