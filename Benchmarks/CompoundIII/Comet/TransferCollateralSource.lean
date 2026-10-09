import Benchmarks.CompoundIII.Comet.TransferCollateralPrefixSource
import Benchmarks.CompoundIII.Comet.TransferCollateralTailSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem transferCollateral_source {v src dst asset amount evm result}
    (ht : TransferCollateralTrace v src dst asset amount evm result) :
    internalSourceResult config (transferCollateralEntry (immStore v) src dst asset amount)
      evm transferCollateralCallable.body result := by
  let frame := transferCollateralEntry (immStore v) src dst asset amount
  have hf : TransferCollateralArgs frame v src dst asset amount := by
    constructor <;> simp only [frame, transferCollateralEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl
  have hp := transferCollateralPrefix_source frame evm hf
  apply internalBlockResult.toSource
  change internalBlockResult config frame evm
    (transferCollateralPrefix ++ transferCollateralTail) result
  cases ht with
  | reverted he =>
    simp only [transferCollateralPrefixResult, he] at hp
    exact execBlockAppendReverted hp
  | staticViolation he =>
    simp only [transferCollateralPrefixResult, he] at hp
    exact execBlock_append_term hp (by intro _ _ he; cases he)
  | done he tail =>
    simp only [transferCollateralPrefixResult, he] at hp
    exact (transferCollateralTail_source tail _ (hf.ready evm)
      (transferCollateralReady_balances frame evm src dst asset amount)).prependBlock hp

theorem transferCollateral_call {v src dst asset amount evm result}
    (ht : TransferCollateralTrace v src dst asset amount evm result) (frame : Frame)
    (srcExpr dstExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hd : evalExpr? config frame evm dstExpr = .ok (.address dst))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "transferCollateral" [srcExpr, dstExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := transferCollateralCallable)
    (locals := (transferCollateralEntry (immStore v) src dst asset amount).locals)
    (argVals := [.address src, .address dst, .address asset, .int amount.toNat])
  · simp only [evalExprs?, hs, hd, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact transferCollateralCallable_lookup
  · rfl
  · simpa only [hc, hi] using transferCollateral_source ht

end Benchmarks.CompoundIII.Comet
