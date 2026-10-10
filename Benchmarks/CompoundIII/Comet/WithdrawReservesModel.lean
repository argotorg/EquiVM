import Benchmarks.CompoundIII.Comet.ReservesTrace
import Benchmarks.CompoundIII.Comet.WithdrawReservesChecks
import Benchmarks.CompoundIII.Comet.TransferOutSource
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def withdrawReservesArgs (recipient : AccountAddress) (amount : UInt256) : Store :=
  ((∅ : Store).insert "to" (.address recipient)).insert "amount" (.int (Int.ofNat amount.toNat))

def withdrawReservesEntry (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) : Frame :=
  calldataLocalFrame
    { contract := contract, immutables := immStore v,
      locals := withdrawReservesArgs recipient amount }
    evm

def withdrawReservesFrame (v : CometWithExtendedAssetListImmutables) (initial : EVM.State)
    (recipient : AccountAddress) (amount reserves : UInt256) : Frame :=
  let frame := withdrawReservesEntry v initial recipient amount
  { frame with locals := frame.locals.insert "reserves" (.int (signedWord reserves)) }

def withdrawReservesUnsignedFrame (v : CometWithExtendedAssetListImmutables)
    (initial : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256) : Frame :=
  let frame := withdrawReservesFrame v initial recipient amount reserves
  { frame with locals := frame.locals.insert "__c1" (.int (Int.ofNat reserves.toNat)) }

def withdrawReservesEmit : Stmt := .emit "WithdrawReserves" [.var "to", .var "amount"]

def withdrawReservesTail : List Stmt :=
  [.require (.binary .ge (.var "reserves") (.intLit 0)),
    .internalCall "unsigned256" [.var "reserves"] "__c1",
    .require (.binary .le (.var "amount") (.var "__c1")),
    .internalCall "doTransferOut" [.immutable "baseToken", .var "to", .var "amount"] "__c2",
    withdrawReservesEmit]

def withdrawReservesAuth : Expr := .binary .eq (.env .caller) (.immutable "governor")

theorem withdrawReservesTransition_body : withdrawReservesTransition.body = calldataPrologue
    ([.require withdrawReservesAuth, .internalCall "getReserves_body" [] "reserves"] ++
      withdrawReservesTail) := rfl

inductive WithdrawReservesAfter (v : CometWithExtendedAssetListImmutables)
    (recipient : AccountAddress) (amount reserves : UInt256) (evm : EVM.State) :
    Option EVM.State → Prop where
  | checksFailed (hv : ¬ WithdrawReservesAllowed reserves amount) :
      WithdrawReservesAfter v recipient amount reserves evm none
  | transfer {result : Option EVM.State} (hv : WithdrawReservesAllowed reserves amount)
      (ht : TransferOutTrace v.baseToken recipient amount evm result) :
      WithdrawReservesAfter v recipient amount reserves evm result

inductive WithdrawReservesTrace (v : CometWithExtendedAssetListImmutables)
    (recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    Option EVM.State → Prop where
  | unauthorized (ha : evm.executionEnv.source ≠ v.governor) :
      WithdrawReservesTrace v recipient amount evm none
  | reservesFailed (ha : evm.executionEnv.source = v.governor) (ht : ReservesTrace v evm none) :
      WithdrawReservesTrace v recipient amount evm none
  | reservesOk {evm' : EVM.State} {reserves : UInt256} {result : Option EVM.State}
      (ha : evm.executionEnv.source = v.governor) (ht : ReservesTrace v evm (some (evm', reserves)))
      (ht' : WithdrawReservesAfter v recipient amount reserves evm' result) :
      WithdrawReservesTrace v recipient amount evm result

def WithdrawReservesBlockResult (frame : Frame) (evm : EVM.State) (body : List Stmt)
    (result : Option EVM.State) : Prop :=
  match result with
  | none => ExecBlock config frame evm body .reverted
  | some evm' => if evm'.executionEnv.perm = true then
      ∃ final, ExecBlock config frame evm body (.ok final evm')
    else ExecBlock config frame evm body .staticViolation

theorem withdrawReservesAuth_eval (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      withdrawReservesAuth = .ok (.bool (decide (evm.executionEnv.source = v.governor))) := by
  simp only [withdrawReservesAuth, evalExpr?, evalImmutable_governor, envValue, pure, bind,
    EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

end Benchmarks.CompoundIII.Comet
