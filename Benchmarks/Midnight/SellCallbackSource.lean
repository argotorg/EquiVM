import Benchmarks.Midnight.TakeSellData
import Benchmarks.Midnight.SellCallbackABI
import Benchmarks.Midnight.FlashLoanCallbackSource

variable {fork : Ethereum.Fork}

/-! Source statements and exact argument evaluation for the seller callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def sellCallbackExprs : List Expr :=
  [.var "id", .field (.var "offer") "market", .var "sellerAssets", .var "units",
    .var "sellerPendingFeeDecrease", .var "seller", .var "receiver", .var "sellerCallbackData"]

def sellCallbackStmt : Stmt := .externalCall (.var "sellerCallback") "onSell" (.intLit 0)
  sellCallbackExprs "__c30" true

def sellMagicGuard : Expr :=
  .binary .eq (.var "__c30") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def sellCallbackFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c30" (wordBytes32Value value) }

def takeSellCondition : Expr :=
  .binary .ne (.var "sellerCallback") (.cast (.intLit 0) (.elem .address))

theorem takeSellCallback_shape : takeTransition.body.drop 70 =
    .ite takeSellCondition
      [.letDecl "sellerCallbackData" (some .bytes) takeSellerDataExpr, sellCallbackStmt, .require sellMagicGuard] [] ::
      takeTransition.body.drop 71 := by decide +kernel

theorem sellCallbackArgs {frame : Frame} {evm : State} {offer : OfferData}
    {id assets units fee user receiver : UInt256} {data : ByteArray}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "sellerAssets" = some (.int assets.toNat))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hf : frame.locals.get? "sellerPendingFeeDecrease" = some (.int fee.toNat))
    (hb : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat user.toNat)))
    (hr : frame.locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hd : frame.locals.get? "sellerCallbackData" = some (.bytes data)) :
    evalExprs? config frame evm sellCallbackExprs =
      .ok (sellCallbackArguments offer.market id assets units fee
        (AccountAddress.ofNat user.toNat) (AccountAddress.ofNat receiver.toNat) data) := by
  unfold sellCallbackExprs
  rw [evalExprs?, evalExpr?, hi]
  simp only [EvalResult.ofOption, bind, EvalResult.bind]
  rw [evalExprs?, evalOfferMarket ho]
  simp only [evalExprs?, evalExpr?, ha, hu, hf, hb, hr, hd, EvalResult.ofOption,
    bind, pure, EvalResult.bind, sellCallbackArguments]

theorem sellMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (sellCallbackFrame frame value) evm sellMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) := by
  simp only [sellMagicGuard, evalExpr?, sellCallbackFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, if_true,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, wordBytes32Value_beq]

section
variable {frame : Frame} {evm evm' : State} {m : MarketData}
  {id assets units fee user receiver : UInt256} {callback : AccountAddress} {data out : ByteArray}
  (ht : frame.locals.get? "sellerCallback" = some (.address callback))
  (ha : evalExprs? config frame evm sellCallbackExprs =
    .ok (sellCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) (AccountAddress.ofNat receiver.toNat) data))

include ht ha

theorem sellCallbackFailure
    (hcall : typedCallViaEVM fork config evm callback "onSell" 0
      (sellCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) (AccountAddress.ofNat receiver.toNat) data)
      (false, evm', out) true) :
    ExecStmt fork config frame evm sellCallbackStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall)

theorem sellCallbackShort
    (hcall : typedCallViaEVM fork config evm callback "onSell" 0
      (sellCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) (AccountAddress.ofNat receiver.toNat) data)
      (true, evm', out) true) (hshort : out.size < 32) :
    ExecStmt fork config frame evm sellCallbackStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall) (decodeSellCallback_short hshort)

theorem sellCallbackSuccess
    (hcall : typedCallViaEVM fork config evm callback "onSell" 0
      (sellCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) (AccountAddress.ofNat receiver.toNat) data)
      (true, evm', out) true) (h32 : 32 ≤ out.size) :
    ExecStmt fork config frame evm sellCallbackStmt
      (.ok (sellCallbackFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall) (decodeSellCallback h32)

end

end Benchmarks.Midnight
