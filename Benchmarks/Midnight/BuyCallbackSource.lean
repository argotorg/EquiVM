import Benchmarks.Midnight.TakeBuyData
import Benchmarks.Midnight.BuyCallbackABI
import Benchmarks.Midnight.FlashLoanCallbackSource

/-! Source statements and exact argument evaluation for the buyer callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def buyCallbackExprs : List Expr :=
  [.var "id", .field (.var "offer") "market", .var "buyerAssets", .var "units",
    .var "buyerPendingFeeIncrease", .var "buyer", .var "buyerCallbackData"]

def buyCallbackStmt : Stmt := .externalCall (.var "buyerCallback") "onBuy" (.intLit 0)
  buyCallbackExprs "__c27" true

def buyMagicGuard : Expr :=
  .binary .eq (.var "__c27") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def buyCallbackFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c27" (wordBytes32Value value) }

def takeBuyCondition : Expr :=
  .binary .ne (.var "buyerCallback") (.cast (.intLit 0) (.elem .address))

theorem takeBuyCallback_shape : takeTransition.body.drop 67 =
    .ite takeBuyCondition
      [.letDecl "buyerCallbackData" (some .bytes) takeBuyerDataExpr, buyCallbackStmt, .require buyMagicGuard] [] ::
      takeTransition.body.drop 68 := by decide +kernel

theorem buyCallbackArgs {frame : Frame} {evm : State} {offer : OfferData}
    {id assets units fee user : UInt256} {data : ByteArray}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "buyerAssets" = some (.int assets.toNat))
    (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hf : frame.locals.get? "buyerPendingFeeIncrease" = some (.int fee.toNat))
    (hb : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat user.toNat)))
    (hd : frame.locals.get? "buyerCallbackData" = some (.bytes data)) :
    evalExprs? config frame evm buyCallbackExprs =
      .ok (buyCallbackArguments offer.market id assets units fee
        (AccountAddress.ofNat user.toNat) data) := by
  unfold buyCallbackExprs
  rw [evalExprs?, evalExpr?, hi]
  simp only [EvalResult.ofOption, bind, EvalResult.bind]
  rw [evalExprs?, evalOfferMarket ho]
  simp only [evalExprs?, evalExpr?, ha, hu, hf, hb, hd, EvalResult.ofOption,
    bind, pure, EvalResult.bind, buyCallbackArguments]

theorem buyMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (buyCallbackFrame frame value) evm buyMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) := by
  simp only [buyMagicGuard, evalExpr?, buyCallbackFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, if_true,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, wordBytes32Value_beq]

section
variable {frame : Frame} {evm evm' : State} {m : MarketData}
  {id assets units fee user : UInt256} {callback : AccountAddress} {data out : ByteArray}
  (ht : frame.locals.get? "buyerCallback" = some (.address callback))
  (ha : evalExprs? config frame evm buyCallbackExprs =
    .ok (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data))

include ht ha

theorem buyCallbackFailure
    (hcall : typedCallViaEVM config evm callback "onBuy" 0
      (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data)
      (false, evm', out) true) :
    ExecStmt config frame evm buyCallbackStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall)

theorem buyCallbackShort
    (hcall : typedCallViaEVM config evm callback "onBuy" 0
      (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data)
      (true, evm', out) true) (hshort : out.size < 32) :
    ExecStmt config frame evm buyCallbackStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall) (decodeBuyCallback_short hshort)

theorem buyCallbackSuccess
    (hcall : typedCallViaEVM config evm callback "onBuy" 0
      (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data)
      (true, evm', out) true) (h32 : 32 ≤ out.size) :
    ExecStmt config frame evm buyCallbackStmt
      (.ok (buyCallbackFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := callback) (Or.inl wordOfInt_zero)
    (by simp only [evalExpr?, ht, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) ha
    (by simpa only [address_of_val] using hcall) (decodeBuyCallback h32)

end

end Benchmarks.Midnight
