import Benchmarks.Midnight.RatifierABI
import Benchmarks.Midnight.TakeSourceFrame
import Benchmarks.Midnight.OfferSourceValues
import Benchmarks.Midnight.FlashLoanCallbackSource

variable {fork : Ethereum.Fork}

/-! Source execution of the ratifier call and its bytes32 acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def ratifierCallStmt : Stmt :=
  .externalCall (.field (.var "offer") "ratifier") "isRatified" (.intLit 0)
    [.var "offer", .var "ratifierData", .var "taker"] "__c1" false

def ratifierMagicGuard : Expr :=
  .binary .eq (.var "__c1") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE flashLoanMagic))

def ratifierCallFrame (frame : Frame) (value : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c1" (wordBytes32Value value) }

theorem ratifierCall_shape :
    takeTransition.body.drop 15 = ratifierCallStmt :: .require ratifierMagicGuard ::
      takeTransition.body.drop 17 := by decide +kernel

theorem ratifierCallFrame_spec {frame : Frame} {offer : OfferData} {id units taker : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (value : UInt256) :
    TakeSourceFrame (ratifierCallFrame frame value)
      offer id units taker receiver callback ratifierData data :=
  hf.insert "__c1" _ (by simp)

theorem ratifierCallArgs {frame : Frame} {evm : State} {offer : OfferData}
    {data : ByteArray} {taker : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "ratifierData" = some (.bytes data))
    (ht : frame.locals.get? "taker" = some (.address taker)) :
    evalExprs? config frame evm [.var "offer", .var "ratifierData", .var "taker"] =
      .ok (ratifierArguments offer data taker) := by
  simp only [evalExprs?, evalExpr?, ho, hd, ht, EvalResult.ofOption,
    bind, pure, EvalResult.bind, ratifierArguments]

theorem ratifierMagicGuard_eval (frame : Frame) (evm : State) (value : UInt256) :
    evalExpr? config (ratifierCallFrame frame value) evm ratifierMagicGuard =
      .ok (.bool (decide (value = flashLoanMagic))) :=
  flashLoanMagicGuard_eval frame evm value

theorem ratifierCallFailure {frame : Frame} {evm evm' : State} {offer : OfferData}
    {data out : ByteArray} {taker : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "ratifierData" = some (.bytes data))
    (ht : frame.locals.get? "taker" = some (.address taker))
    (hcall : typedCallViaEVM fork config evm offer.ratifier "isRatified" 0
      (ratifierArguments offer data taker) (false, evm', out) false) :
    ExecStmt fork config frame evm ratifierCallStmt .reverted := by
  exact ExecStmt.externalCallFailure (target := offer.ratifier) (Or.inl wordOfInt_zero)
    (evalOfferRatifier ho) (by simp only [evalExpr?, pure]) (ratifierCallArgs ho hd ht)
    (by simpa only [address_of_val] using hcall)

theorem ratifierCallShort {frame : Frame} {evm evm' : State} {offer : OfferData}
    {data out : ByteArray} {taker : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "ratifierData" = some (.bytes data))
    (ht : frame.locals.get? "taker" = some (.address taker))
    (hcall : typedCallViaEVM fork config evm offer.ratifier "isRatified" 0
      (ratifierArguments offer data taker) (true, evm', out) false)
    (hshort : out.size < 32) :
    ExecStmt fork config frame evm ratifierCallStmt .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (target := offer.ratifier) (Or.inl wordOfInt_zero)
    (evalOfferRatifier ho) (by simp only [evalExpr?, pure]) (ratifierCallArgs ho hd ht)
    (by simpa only [address_of_val] using hcall) (decodeRatifierCall_short hshort)

theorem ratifierCallSuccess {frame : Frame} {evm evm' : State} {offer : OfferData}
    {data out : ByteArray} {taker : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "ratifierData" = some (.bytes data))
    (ht : frame.locals.get? "taker" = some (.address taker))
    (hcall : typedCallViaEVM fork config evm offer.ratifier "isRatified" 0
      (ratifierArguments offer data taker) (true, evm', out) false)
    (h32 : 32 ≤ out.size) :
    ExecStmt fork config frame evm ratifierCallStmt
      (.ok (ratifierCallFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (target := offer.ratifier) (Or.inl wordOfInt_zero)
    (evalOfferRatifier ho) (by simp only [evalExpr?, pure]) (ratifierCallArgs ho hd ht)
    (by simpa only [address_of_val] using hcall) (decodeRatifierCall h32)

end Benchmarks.Midnight
