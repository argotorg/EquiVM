import Benchmarks.CompoundIII.Comet.PrincipalTransferEventSource
import Benchmarks.CompoundIII.Comet.TotalsStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def supplyBaseTransferEvent : Stmt :=
  .ite (.binary .gt (.var "supplyAmount") (.intLit 0))
    [.internalCall "presentValueSupply" [.storage ⟨"baseSupplyIndex", []⟩,
      .var "supplyAmount"] "__c7",
      .emit "Transfer" [.cast (.intLit 0) (.elem .address), .var "dst", .var "__c7"]] []

def supplyBaseEvents : List Stmt :=
  [.emit "Supply" [.var "from", .var "dst", .var "amount"], supplyBaseTransferEvent]

structure SupplyBaseArgs (frame : Frame) (sender dst : AccountAddress)
    (amount supplied : UInt256) : Prop where
  contract : frame.contract = contract
  sender : frame.locals.get? "from" = some (.address sender)
  dst : frame.locals.get? "dst" = some (.address dst)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)
  supplied : frame.locals.get? "supplyAmount" = some (.int supplied.toNat)
  index : frame.locals.get? "baseSupplyIndex" = none

theorem SupplyBaseArgs.insert {frame sender dst amount supplied}
    (hf : SupplyBaseArgs frame sender dst amount supplied) (key : Ident) (value : Value)
    (hk : key ∉ ["from", "dst", "amount", "supplyAmount", "baseSupplyIndex"]) :
    SupplyBaseArgs { frame with locals := frame.locals.insert key value }
      sender dst amount supplied := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  constructor
  · exact hf.contract
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.1] using hf.sender
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.1] using hf.dst
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.1] using hf.amount
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.1] using hf.supplied
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hk.2.2.2.2] using hf.index

theorem supplyBaseEvents_source {sender dst amount supplied}
    (frame : Frame) (evm : EVM.State) (hf : SupplyBaseArgs frame sender dst amount supplied)
    (hsupplied : supplied.toNat < 2^104) :
    ∃ final, ExecBlock config frame evm supplyBaseEvents (.ok final evm) := by
  have hem : ExecStmt config frame evm (.emit "Supply"
      [.var "from", .var "dst", .var "amount"]) (.ok frame evm) :=
    ExecStmt.emit (vals := [.address sender, .address dst, .int amount.toNat]) (by
      simp only [evalExprs?, evalExpr?, hf.sender, hf.dst, hf.amount,
        EvalResult.ofOption, pure, bind, EvalResult.bind])
  have hmint := principalTransferEvent_source frame evm true dst supplied
    "dst" "supplyAmount" "__c7" (by decide) hf.contract hf.dst hf.supplied hf.index hsupplied
  exact ⟨_, ExecBlock.consNormal hem (ExecBlock.consNormal hmint .nil)⟩

end Benchmarks.CompoundIII.Comet
