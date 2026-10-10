import Benchmarks.CompoundIII.Comet.WithdrawCollateralPrefixSource
import Benchmarks.CompoundIII.Comet.WithdrawCollateralTailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawCollateral_source {v src recipient asset amount evm result}
    (ht : WithdrawCollateralTrace v src recipient asset amount evm result) :
    internalSourceResult config (withdrawCollateralEntry (immStore v) src recipient asset amount)
      evm withdrawCollateralCallable.body result := by
  let frame := withdrawCollateralEntry (immStore v) src recipient asset amount
  have hf : WithdrawCollateralFrame frame src asset amount := by
    constructor <;> simp only [frame, withdrawCollateralEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl
  have ha : WithdrawCollateralArgs frame v src recipient asset amount := by
    constructor <;> simp only [frame, withdrawCollateralEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] <;> rfl
  have hp := withdrawCollateralPrefix_source frame evm src asset amount hf
  apply internalBlockResult.toSource
  change internalBlockResult config frame evm
    (withdrawCollateralPrefix ++ withdrawCollateralTail) result
  cases ht with
  | reverted he =>
    simp only [withdrawCollateralPrefixResult, he] at hp
    exact execBlock_append_term hp (by intro _ _ he; cases he)
  | staticViolation he =>
    simp only [withdrawCollateralPrefixResult, he] at hp
    exact execBlock_append_term hp (by intro _ _ he; cases he)
  | done he tail =>
    simp only [withdrawCollateralPrefixResult, he] at hp
    have hready := (ha.insert "srcCollateral"
      (.int (withdrawCollateralBalance evm src asset).toNat) (by decide)).insert
      "srcCollateralNew" (.int (UInt256.sub (withdrawCollateralBalance evm src asset) amount).toNat)
      (by decide)
    have hb := withdrawCollateralTail_source tail _ hready
      (by simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
      (by simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    cases result with
    | ok evm' =>
      obtain ⟨final, hb⟩ := hb
      exact ⟨final, execBlock_append hp hb⟩
    | reverted => exact execBlock_append hp hb
    | staticViolation => exact execBlock_append hp hb

theorem withdrawCollateral_call {v src recipient asset amount evm result}
    (ht : WithdrawCollateralTrace v src recipient asset amount evm result) (frame : Frame)
    (srcExpr toExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hto : evalExpr? config frame evm toExpr = .ok (.address recipient))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "withdrawCollateral" [srcExpr, toExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := withdrawCollateralCallable)
    (locals := (withdrawCollateralEntry (immStore v) src recipient asset amount).locals)
    (argVals := [.address src, .address recipient, .address asset, .int amount.toNat])
  · simp only [evalExprs?, hs, hto, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact withdrawCollateralCallable_lookup
  · rfl
  · simpa only [hc, hi] using withdrawCollateral_source ht

end Benchmarks.CompoundIII.Comet
