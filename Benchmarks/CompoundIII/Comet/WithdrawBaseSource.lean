import Benchmarks.CompoundIII.Comet.WithdrawBaseAfterSource
import Benchmarks.CompoundIII.Comet.AccrueInternalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem withdrawBase_source {v src recipient amount evm result}
    (ht : WithdrawBaseTrace v src recipient amount evm result) :
    internalSourceResult config (withdrawBaseEntry (immStore v) src recipient amount)
      evm withdrawBaseCallable.body result := by
  have ha := accrue_call v (withdrawBaseEntry (immStore v) src recipient amount) evm "__c0" rfl rfl
  apply internalBlockResult.toSource
  change internalBlockResult config (withdrawBaseEntry (immStore v) src recipient amount)
    evm (.internalCall "accrueInternal" [] "__c0" :: withdrawBaseAfterAccrueBlock) result
  cases ht with
  | reverted he =>
    simp only [he, internalStmtResult] at ha
    exact ExecBlock.consRevert ha
  | staticViolation he =>
    simp only [he, internalStmtResult] at ha
    exact ExecBlock.consStatic ha
  | done he tail =>
    simp only [he, internalStmtResult] at ha
    exact (withdrawBaseAfterAccrue_source tail).prepend ha

theorem withdrawBase_call {v src recipient amount evm result}
    (ht : WithdrawBaseTrace v src recipient amount evm result) (frame : Frame)
    (srcExpr toExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hto : evalExpr? config frame evm toExpr = .ok (.address recipient))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm (.internalCall "withdrawBase" [srcExpr, toExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := withdrawBaseCallable)
    (locals := (withdrawBaseEntry (immStore v) src recipient amount).locals)
    (argVals := [.address src, .address recipient, .int amount.toNat])
  · simp only [evalExprs?, hs, hto, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact withdrawBaseCallable_lookup
  · rfl
  · simpa only [hc, hi] using withdrawBase_source ht

end Benchmarks.CompoundIII.Comet
