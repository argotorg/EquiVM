import Benchmarks.Midnight.TakePositionAliases
import Benchmarks.Midnight.HasCreditSource

/-! Source aliases and the first credit predicate before updating the buyer's position. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePositionReadFrame (frame : Frame) (evm : State) (id buyer seller : UInt256) : Frame :=
  resumeAfterInternalCall (takePositionAliasesFrame frame id buyer seller) "__c9"
    (some [.bool (hasCreditValue evm id buyer)])

theorem takePositionReadSource {frame : Frame} {evm : State} {id buyer seller : UInt256}
    (hc : frame.contract = contract) (hp : frame.locals.get? "position" = none)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hb : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hs : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hcanon : buyer.toNat < EVM.addressModulus) :
    ABlock config evm frame (takeTransition.body.drop 29)
      (takePositionReadFrame frame evm id buyer seller) (takeTransition.body.drop 32) := by
  have hi1 : (takePositionAliasesFrame frame id buyer seller).locals.get? "id" =
      some (wordBytes32Value id) :=
    (takePositionAliasesFrame_get _ _ _ _ _ (by decide) (by decide)).trans hi
  have hb1 : (takePositionAliasesFrame frame id buyer seller).locals.get? "buyer" =
      some (.address (AccountAddress.ofNat buyer.toNat)) :=
    (takePositionAliasesFrame_get _ _ _ _ _ (by decide) (by decide)).trans hb
  have he : evalExprs? config (takePositionAliasesFrame frame id buyer seller) evm
      [.var "id", .var "buyer"] =
      .ok [wordBytes32Value id, .address (AccountAddress.ofNat buyer.toNat)] := by
    simp only [evalExprs?, evalExpr?, hi1, hb1, EvalResult.ofOption, bind, pure, EvalResult.bind]
  exact ⟨fun h ↦ (takePositionAliasesSource hc hp hi hb hs).run
    (ExecBlock.consNormal (callHasCredit hc he hcanon) h)⟩

theorem TakeSourceFrame.positionRead {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker buyer seller : UInt256} {receiver callback : AccountAddress}
    {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takePositionReadFrame frame evm id buyer seller) offer id units taker receiver
      callback ratifierData data :=
  hf.positionAliases.insert "__c9" (.bool (hasCreditValue evm id buyer)) (by decide)

end Benchmarks.Midnight
