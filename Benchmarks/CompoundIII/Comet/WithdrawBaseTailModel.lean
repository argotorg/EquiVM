import Benchmarks.CompoundIII.Comet.WithdrawBaseTrace
import Benchmarks.CompoundIII.Comet.PresentValue
import Benchmarks.CompoundIII.Comet.SignedArithmeticWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure WithdrawBaseArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount supplied : UInt256) : Prop where
  contract : frame.contract = contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  recipient : frame.locals.get? "to" = some (.address recipient)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)
  supplied : frame.locals.get? "withdrawAmount" = some (.int supplied.toNat)
  index : frame.locals.get? "baseSupplyIndex" = none

theorem WithdrawBaseArgs.insert {frame v src recipient amount supplied}
    (hf : WithdrawBaseArgs frame v src recipient amount supplied)
    (name : Ident) (value : Value)
    (hn : name ∉ ["src", "to", "amount", "withdrawAmount", "baseSupplyIndex"]) :
    WithdrawBaseArgs { frame with locals := frame.locals.insert name value }
      v src recipient amount supplied := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1, Ne.symm hn.1]
      using hf.src
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1,
      Ne.symm hn.2.1] using hf.recipient
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1,
      Ne.symm hn.2.2.1] using hf.amount
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.1,
      Ne.symm hn.2.2.2.1] using hf.supplied
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.2,
      Ne.symm hn.2.2.2.2] using hf.index

def withdrawBaseTransferEvent : Stmt :=
  .ite (.binary .gt (.var "withdrawAmount") (.intLit 0))
    [.internalCall "presentValueSupply"
      [.storage ⟨"baseSupplyIndex", []⟩, .var "withdrawAmount"] "__c8",
      .emit "Transfer" [.var "src", .cast (.intLit 0) (.elem .address), .var "__c8"]] []

def withdrawBaseTransferTail : List Stmt :=
  [.internalCall "doTransferOut" [.immutable "baseToken", .var "to", .var "amount"] "__c7",
    .emit "Withdraw" [.var "src", .var "to", .var "amount"], withdrawBaseTransferEvent]

def withdrawBaseBorrowMinExpr : Expr :=
  .binary .ge
    (.cast (.inRange (.sint ⟨256, by decide⟩) (.binary .sub (.intLit 0) (.var "srcBalance")))
      (.elem (.int (.uint ⟨256, by decide⟩)))) (.immutable "baseBorrowMin")

def withdrawBaseChecks : List Stmt :=
  [.require withdrawBaseBorrowMinExpr,
    .internalCall "isBorrowCollateralized_body" [.var "src"] "__c6", .require (.var "__c6")]

def withdrawBaseTail : List Stmt :=
  .ite (.binary .lt (.var "srcBalance") (.intLit 0)) withdrawBaseChecks [] ::
    withdrawBaseTransferTail

end Benchmarks.CompoundIII.Comet
