import Benchmarks.CompoundIII.Comet.WithdrawBaseTailModel
import Benchmarks.CompoundIII.Comet.TransferBaseEventsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive TransferBaseTailTrace (v : CometWithExtendedAssetListImmutables)
    (src : AccountAddress) (balance : UInt256) (evm : EVM.State) : InternalOutcome → Prop where
  | nonnegative (hn : 0 ≤ signedWord balance) : TransferBaseTailTrace v src balance evm (.ok evm)
  | tooSmall (hn : signedWord balance < 0) (hm : ¬ WithdrawBaseBorrowMin v balance) :
      TransferBaseTailTrace v src balance evm .reverted
  | failed (hn : signedWord balance < 0) (hm : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm none) :
      TransferBaseTailTrace v src balance evm .reverted
  | rejected {evm'} (hn : signedWord balance < 0) (hm : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm (some (evm', false))) :
      TransferBaseTailTrace v src balance evm .reverted
  | accepted {evm'} (hn : signedWord balance < 0) (hm : WithdrawBaseBorrowMin v balance)
      (hc : CollateralCheckTrace v true src evm (some (evm', true))) :
      TransferBaseTailTrace v src balance evm (.ok evm')

def transferBaseChecks : List Stmt :=
  [.require withdrawBaseBorrowMinExpr,
    .internalCall "isBorrowCollateralized_body" [.var "src"] "__c11", .require (.var "__c11")]

def transferBaseTail : List Stmt :=
  .ite (.binary .lt (.var "srcBalance") (.intLit 0)) transferBaseChecks [] :: transferBaseEvents

structure TransferBaseTailArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (balance withdrawn supplied : UInt256) : Prop where
  contract : frame.contract = contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  dst : frame.locals.get? "dst" = some (.address dst)
  balance : frame.locals.get? "srcBalance" = some (.int (signedWord balance))
  withdrawn : frame.locals.get? "withdrawAmount" = some (.int withdrawn.toNat)
  supplied : frame.locals.get? "supplyAmount" = some (.int supplied.toNat)
  index : frame.locals.get? "baseSupplyIndex" = none

theorem TransferBaseTailArgs.insert {frame v src dst balance withdrawn supplied}
    (hf : TransferBaseTailArgs frame v src dst balance withdrawn supplied) (name : Ident)
    (value : Value)
    (hn : name ∉ ["src", "dst", "srcBalance", "withdrawAmount", "supplyAmount", "baseSupplyIndex"]) :
    TransferBaseTailArgs { frame with locals := frame.locals.insert name value }
      v src dst balance withdrawn supplied := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.1] using hf.src
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.2.1] using hf.dst
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.2.2.1] using hf.balance
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.2.2.2.1] using hf.withdrawn
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.2.2.2.2.1] using hf.supplied
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, if_neg hn.2.2.2.2.2] using hf.index

end Benchmarks.CompoundIII.Comet
