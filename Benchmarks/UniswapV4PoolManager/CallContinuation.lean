import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def continueCallResult (next : State → Option (List Value) → ExecResult) : ExecResult → ExecResult
  | .returned _ post values => next post values
  | .staticViolation => .staticViolation
  | _ => .reverted

theorem continueCallResult_ok {next : State → Option (List Value) → ExecResult} {result : ExecResult}
    {f : Frame} {post : State} (h : continueCallResult next result = .ok f post) :
    ∃ callee before values, result = .returned callee before values ∧ next before values = .ok f post := by
  cases result with
  | returned callee before values => exact ⟨callee, before, values, rfl, h⟩
  | ok | reverted | «break» | «continue» | staticViolation => cases h

-- LIBRARY CANDIDATE: compose an internal call with its successful continuation.
theorem execBlock_continueCall {cfg : Config} {f : Frame} {evm : State} {stmt : Stmt} {ret : Ident}
    {rest : List Stmt} {result : ExecResult} {next : State → Option (List Value) → ExecResult}
    (hc : ExecStmt cfg f evm stmt (resumeCallResult f ret result))
    (hn : ∀ cf post values, result = .returned cf post values →
      ExecBlock cfg (resumeAfterInternalCall f ret values) post rest (next post values)) :
    ExecBlock cfg f evm (stmt :: rest) (continueCallResult next result) := by
  cases result with
  | returned cf post values => exact ExecBlock.consNormal hc (hn cf post values rfl)
  | staticViolation => exact ExecBlock.consStatic hc
  | ok | reverted | «break» | «continue» => exact ExecBlock.consRevert hc

-- LIBRARY CANDIDATE: compose a callee trace with its return continuation.
theorem functionResultTrace_continueCall {code : ByteArray} {g : Sat256} {s0 : State}
    {before after : State → Option (List Value) → Prop} {result : ExecResult}
    {next : State → Option (List Value) → ExecResult}
    (hr : functionResultTrace code g s0 before result)
    (hn : ∀ post values, before post values → functionResultTrace code g s0 after (next post values)) :
    functionResultTrace code g s0 after (continueCallResult next result) := by
  cases result with
  | returned cf post values => exact hn post values hr
  | reverted | staticViolation => exact hr
  | ok | «break» | «continue» => exact False.elim hr
end Benchmarks.UniswapV4PoolManager
