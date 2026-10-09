import Benchmarks.CompoundIII.Comet.TransferBaseAfterSource
import Benchmarks.CompoundIII.Comet.AccrueInternalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem transferBase_source {v src dst amount evm result}
    (ht : TransferBaseTrace v src dst amount evm result) :
    internalSourceResult config (transferBaseEntry (immStore v) src dst amount)
      evm transferBaseCallable.body result := by
  have ha := accrue_call v (transferBaseEntry (immStore v) src dst amount) evm "__c0" rfl rfl
  apply internalBlockResult.toSource
  change internalBlockResult config (transferBaseEntry (immStore v) src dst amount)
    evm (.internalCall "accrueInternal" [] "__c0" :: transferBaseAfterAccrueBlock) result
  cases ht with
  | reverted he =>
    simp only [he, internalStmtResult] at ha
    exact ExecBlock.consRevert ha
  | staticViolation he =>
    simp only [he, internalStmtResult] at ha
    exact ExecBlock.consStatic ha
  | done he tail =>
    simp only [he, internalStmtResult] at ha
    exact (transferBaseAfterAccrue_source tail).prepend ha

theorem transferBase_call {v src dst amount evm result}
    (ht : TransferBaseTrace v src dst amount evm result) (frame : Frame)
    (srcExpr dstExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hd : evalExpr? config frame evm dstExpr = .ok (.address dst))
    (ha : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm (.internalCall "transferBase" [srcExpr, dstExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := transferBaseCallable)
    (locals := (transferBaseEntry (immStore v) src dst amount).locals)
    (argVals := [.address src, .address dst, .int amount.toNat])
  · simp only [evalExprs?, hs, hd, ha, pure, bind, EvalResult.bind]
  · rw [hc]; exact transferBaseCallable_lookup
  · rfl
  · simpa only [hc, hi] using transferBase_source ht

end Benchmarks.CompoundIII.Comet
