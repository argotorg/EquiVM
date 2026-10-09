import Benchmarks.Safe.TokenTransferSource
import Benchmarks.Safe.SafeMulSource
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure PaymentInput where
  gasUsed : UInt256
  baseGas : UInt256
  gasPrice : UInt256
  gasToken : EVM.Address
  refundReceiver : EVM.Address

namespace PaymentInput

def args (p : PaymentInput) : Store :=
  (((((∅ : Store).insert "refundReceiver" (.address p.refundReceiver)).insert
    "gasToken" (.address p.gasToken)).insert "gasPrice" (uint256Value p.gasPrice)).insert
      "baseGas" (uint256Value p.baseGas)).insert "gasUsed" (uint256Value p.gasUsed)

def frame (p : PaymentInput) : Frame := { contract := contract, locals := p.args }

def receiver (p : PaymentInput) (I : ExecutionEnv) : EVM.Address :=
  if p.refundReceiver = EVM.address 0 then I.sender else p.refundReceiver

def receiverFrame (p : PaymentInput) (I : ExecutionEnv) : Frame :=
  { p.frame with locals := p.args.insert "receiver" (.address (p.receiver I)) }

def gasTotal (p : PaymentInput) : UInt256 := p.gasUsed + p.baseGas

def totalFrame (p : PaymentInput) (I : ExecutionEnv) : Frame :=
  { p.receiverFrame I with
    locals := (p.receiverFrame I).locals.insert "gasTotal" (uint256Value p.gasTotal) }

def nativePrice (p : PaymentInput) (I : ExecutionEnv) : UInt256 :=
  if p.gasPrice.toNat < (UInt256.ofNat I.gasPrice).toNat then p.gasPrice
  else UInt256.ofNat I.gasPrice

def paidFrame (p : PaymentInput) (I : ExecutionEnv) (price : UInt256) : Frame :=
  { p.totalFrame I with
    locals := (p.totalFrame I).locals.insert "payment"
      (uint256Value (UInt256.mul p.gasTotal price)) }

def tokenInput (p : PaymentInput) (I : ExecutionEnv) : TokenTransferInput :=
  ⟨p.gasToken, p.receiver I, UInt256.mul p.gasTotal p.gasPrice⟩

def tokenFinal (p : PaymentInput) (I : ExecutionEnv) (z : Bool) : Frame :=
  { p.paidFrame I p.gasPrice with
    locals := (p.paidFrame I p.gasPrice).locals.insert
      "transferred" (.bool z) }

def nativeFinal (p : PaymentInput) (I : ExecutionEnv) (z : Bool) (out : ByteArray) : Frame :=
  { p.paidFrame I (p.nativePrice I) with
    locals := ((p.paidFrame I (p.nativePrice I)).locals.insert "refundSuccess" (.bool z)).insert
      "refundData" (.bytes out) }

end PaymentInput

theorem safePaymentReceiver (p : PaymentInput) (evm : EVM.State) :
    ExecStmt config p.frame evm
      (.letDecl "receiver" (some addr)
        (.ite (eqE (.var "refundReceiver") zeroAddr) origin (.var "refundReceiver")))
      (.ok (p.receiverFrame evm.executionEnv) evm) := by
  apply ExecStmt.letDecl
  have hzero : AccountAddress.ofNat 0 = EVM.address 0 := by decide +kernel
  have he : (Value.address p.refundReceiver == Value.address (EVM.address 0)) =
      decide (p.refundReceiver = EVM.address 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]
  by_cases hz : p.refundReceiver = EVM.address 0 <;>
    simp [evalExpr?, eqE, zeroAddr, addrSt, castValue?, hzero, origin, envValue,
      PaymentInput.frame,
      PaymentInput.args, PaymentInput.receiver, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, he, hz]

theorem safePaymentTotal (p : PaymentInput) (evm : EVM.State)
    (hfit : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size) :
    ExecStmt config (p.receiverFrame evm.executionEnv) evm
      (.internalCall "_add" [.var "gasUsed", .var "baseGas"] "gasTotal")
      (.ok (p.totalFrame evm.executionEnv) evm) := by
  apply safeInternalAdd rfl ?_ ?_ hfit <;>
    exact evalLocalValue (by simp [PaymentInput.receiverFrame, PaymentInput.frame,
      PaymentInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safePaymentPrefix {p : PaymentInput} {evm : EVM.State} {result : ExecResult}
    (hfit : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (htail : ExecBlock config (p.totalFrame evm.executionEnv) evm
      (handlePaymentFunction.body.drop 2) result) :
    ExecBlock config p.frame evm handlePaymentFunction.body result :=
  .consNormal (safePaymentReceiver p evm) (.consNormal (safePaymentTotal p evm hfit) htail)

theorem safePaymentAddOverflow (p : PaymentInput) (evm : EVM.State)
    (hover : UInt256.size ≤ p.gasUsed.toNat + p.baseGas.toNat) :
    ExecFuncBody config p.frame evm handlePaymentFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine .consNormal (safePaymentReceiver p evm) (.consRevert ?_)
  apply safeInternalAddOverflow (a := p.gasUsed) (b := p.baseGas) rfl ?_ ?_ hover <;>
    exact evalLocalValue (by simp [PaymentInput.receiverFrame, PaymentInput.frame,
      PaymentInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem safePaymentTokenCondition (p : PaymentInput) (evm : EVM.State) :
    evalExpr? config (p.totalFrame evm.executionEnv) evm (eqE (.var "gasToken") zeroAddr) =
      .ok (.bool (decide (p.gasToken = EVM.address 0))) := by
  have hzero : AccountAddress.ofNat 0 = EVM.address 0 := by decide +kernel
  have he : (Value.address p.gasToken == Value.address (EVM.address 0)) =
      decide (p.gasToken = EVM.address 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]
  simp [evalExpr?, eqE, zeroAddr, addrSt, castValue?, hzero, PaymentInput.totalFrame,
    PaymentInput.receiverFrame, PaymentInput.frame, PaymentInput.args,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?, he]

theorem safePaymentPrice (p : PaymentInput) (evm : EVM.State) :
    evalExpr? config (p.totalFrame evm.executionEnv) evm (minE (.var "gasPrice") gasprice) =
      .ok (uint256Value (p.nativePrice evm.executionEnv)) := by
  have hl : evalExpr? config (p.totalFrame evm.executionEnv) evm (.var "gasPrice") =
      .ok (uint256Value p.gasPrice) := evalLocalValue (by
        simp [PaymentInput.totalFrame, PaymentInput.receiverFrame, PaymentInput.frame,
          PaymentInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  simp only [minE, evalExpr?, ltE, gasprice, envValue, hl, EvalResult.bind, bind, pure,
    uint256Value, evalBinaryOp_lt_int_ok, EVM.Word.ofNat]
  have hcmp : Int.ofNat p.gasPrice.toNat <
      Int.ofNat (UInt256.ofNat evm.executionEnv.gasPrice).toNat ↔
      p.gasPrice.toNat < (UInt256.ofNat evm.executionEnv.gasPrice).toNat := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [hcmp]
  change (match Value.bool (decide (p.gasPrice.toNat <
      (UInt256.ofNat evm.executionEnv.gasPrice).toNat)) with
    | .bool true => EvalResult.ok (Value.int (Int.ofNat p.gasPrice.toNat))
    | .bool false =>
        EvalResult.ok (Value.int (Int.ofNat (UInt256.ofNat evm.executionEnv.gasPrice).toNat))
    | _ => EvalResult.error .typeError) = _
  by_cases hh : p.gasPrice.toNat < (UInt256.ofNat evm.executionEnv.gasPrice).toNat <;>
    simp [PaymentInput.nativePrice, hh]

theorem safeInternalTransferToken {p : TokenTransferInput} {caller : Frame} {evm : EVM.State}
    {token receiver amount : Expr} {retVar : Ident} {result : ExecResult}
    (hc : caller.contract = contract) (hi : caller.immutables = ∅)
    (ht : evalExpr? config caller evm token = .ok (.address p.token))
    (hr : evalExpr? config caller evm receiver = .ok (.address p.receiver))
    (ha : evalExpr? config caller evm amount = .ok (uint256Value p.amount))
    (hbody : ExecFuncBody config p.frame evm transferTokenFunction.body result) :
    ExecStmt config caller evm (.internalCall "transferToken" [token, receiver, amount] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := transferTokenFunction)
    (argVals := [.address p.token, .address p.receiver, uint256Value p.amount]) (locals := p.args)
  · simp [evalExprs?, ht, hr, ha, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · convert hbody using 1
    simp only [TokenTransferInput.frame, hc, hi]

end Benchmarks.Safe
