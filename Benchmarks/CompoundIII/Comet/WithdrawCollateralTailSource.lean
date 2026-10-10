import Benchmarks.CompoundIII.Comet.WithdrawCollateralTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

structure WithdrawCollateralArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) : Prop where
  contract : frame.contract = contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  recipient : frame.locals.get? "to" = some (.address recipient)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)

theorem WithdrawCollateralArgs.insert {frame v src recipient asset amount}
    (hf : WithdrawCollateralArgs frame v src recipient asset amount)
    (name : Ident) (value : Value) (hn : name ∉ ["src", "to", "asset", "amount"]) :
    WithdrawCollateralArgs { frame with locals := frame.locals.insert name value }
      v src recipient asset amount := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1, Ne.symm hn.1]
      using hf.src
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1,
      Ne.symm hn.2.1] using hf.recipient
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1,
      Ne.symm hn.2.2.1] using hf.asset
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2,
      Ne.symm hn.2.2.2] using hf.amount

def withdrawCollateralTransferTail : List Stmt :=
  [.internalCall "doTransferOut" [.var "asset", .var "to", .var "amount"] "__c3",
    .emit "WithdrawCollateral" [.var "src", .var "to", .var "asset", .var "amount"]]

def withdrawCollateralCheckTail : List Stmt :=
  [.internalCall "isBorrowCollateralized_body" [.var "src"] "__c2",
    .require (.var "__c2")] ++ withdrawCollateralTransferTail

def withdrawCollateralMemberTail : List Stmt :=
  .internalCall "updateAssetsIn"
    [.var "src", .var "assetInfo", .var "srcCollateral", .var "srcCollateralNew"] "__c1" ::
    withdrawCollateralCheckTail

theorem withdrawCollateralTransfer_source {v src recipient asset amount evm result}
    (ht : WithdrawCollateralTransfer asset recipient amount evm result) (frame : Frame)
    (hf : WithdrawCollateralArgs frame v src recipient asset amount) :
    internalBlockResult config frame evm withdrawCollateralTransferTail result := by
  have hcall {r} (hc : TransferOutTrace asset recipient amount evm r) :=
    transferOut_call hc frame (.var "asset") (.var "to") (.var "amount") "__c3"
      hf.contract (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.recipient, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.amount, EvalResult.ofOption]; rfl)
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | @done evm' ht =>
    let final : Frame := { frame with locals := frame.locals.insert "__c3" .unit }
    have hf' := hf.insert "__c3" .unit (by decide)
    have he : evalExprs? config final evm'
        [.var "src", .var "to", .var "asset", .var "amount"] =
        .ok [.address src, .address recipient, .address asset, .int amount.toNat] := by
      simp only [evalExprs?, evalExpr?, final, hf'.src, hf'.recipient, hf'.asset, hf'.amount,
        EvalResult.ofOption, pure, bind, EvalResult.bind]
    cases hp : evm'.executionEnv.perm
    · simp only [emitOutcome, hp, Bool.false_eq_true, if_false, internalBlockResult]
      exact ExecBlock.consNormal (hcall ht) (ExecBlock.consStatic (ExecStmt.emitStatic he hp))
    · simp only [emitOutcome, hp, if_true, internalBlockResult]
      exact ⟨final, ExecBlock.consNormal (hcall ht)
        (ExecBlock.consNormal (ExecStmt.emit he) .nil)⟩

theorem withdrawCollateralCheck_source {v src recipient asset amount evm result}
    (ht : WithdrawCollateralCheck v src recipient asset amount evm result) (frame : Frame)
    (hf : WithdrawCollateralArgs frame v src recipient asset amount) :
    internalBlockResult config frame evm withdrawCollateralCheckTail result := by
  have hcall {r} (hc : CollateralCheckTrace v true src evm r) :=
    collateralCheck_call hc frame (.var "src") "__c2" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
  have he (value : Bool) (evm' : EVM.State) : evalExpr? config
      { frame with locals := frame.locals.insert "__c2" (.bool value) } evm' (.var "__c2") =
      .ok (.bool value) := by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | rejected ht =>
    exact ExecBlock.consNormal (hcall ht) (ExecBlock.consRevert (ExecStmt.requireFalse (he _ _)))
  | accepted ht tail =>
    exact ((withdrawCollateralTransfer_source tail _
      (hf.insert "__c2" (.bool true) (by decide))).prepend
        (ExecStmt.requireTrue (he _ _))).prepend (hcall ht)

theorem withdrawCollateralMember_source {v src recipient asset amount balance next evm out result}
    (ht : WithdrawCollateralMember v src recipient asset amount balance next evm out result)
    (frame : Frame) (hf : WithdrawCollateralArgs frame v src recipient asset amount)
    (ho : (calldataWord out 0).toNat < 256)
    (ha : frame.locals.get? "assetInfo" = some (assetValue out))
    (hb : frame.locals.get? "srcCollateral" = some (.int balance.toNat))
    (hn : frame.locals.get? "srcCollateralNew" = some (.int next.toNat)) :
    internalBlockResult config frame evm withdrawCollateralMemberTail result := by
  have hc := assetMembership_call frame evm src out balance next (.var "src")
    (.var "assetInfo") (.var "srcCollateral") (.var "srcCollateralNew") "__c1" hf.contract ho
    (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
    (by simp only [evalExpr?, ha, EvalResult.ofOption])
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
  cases ht with
  | reverted hm => rw [hm] at hc; exact ExecBlock.consRevert hc
  | staticViolation hm => rw [hm] at hc; exact ExecBlock.consStatic hc
  | done hm tail =>
    rw [hm] at hc
    exact (withdrawCollateralCheck_source tail _ (hf.insert "__c1" .unit (by decide))).prepend hc

theorem withdrawCollateralTail_source {v src recipient asset amount balance next evm result}
    (ht : WithdrawCollateralTailTrace v src recipient asset amount balance next evm result)
    (frame : Frame) (hf : WithdrawCollateralArgs frame v src recipient asset amount)
    (hb : frame.locals.get? "srcCollateral" = some (.int balance.toNat))
    (hn : frame.locals.get? "srcCollateralNew" = some (.int next.toNat)) :
    internalBlockResult config frame evm withdrawCollateralTail result := by
  have hcall {r} (hc : AssetSearch v asset 0 evm r) :=
    assetSearch_call hc frame (.var "asset") "assetInfo" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | found ht hv tail =>
    apply (withdrawCollateralMember_source tail _
      (hf.insert "assetInfo" _ (by decide)) hv.2.1 ?_ ?_ ?_).prepend (hcall ht)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hb
    · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hn

end Benchmarks.CompoundIII.Comet
