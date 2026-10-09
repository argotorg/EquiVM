import Benchmarks.CompoundIII.Comet.InternalValueOutcome
import Benchmarks.CompoundIII.Comet.AssetSearch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalBlockResult to returned data and a postcondition on the final frame.
def internalValueBlockResult {α : Type} (cfg : Config) (frame : Frame) (evm : State)
    (body : List Stmt) (post : α → Frame → Prop) : InternalValueOutcome α → Prop
  | .ok evm' value => ∃ final, ExecBlock cfg frame evm body (.ok final evm') ∧ post value final
  | .reverted => ExecBlock cfg frame evm body .reverted
  | .staticViolation => ExecBlock cfg frame evm body .staticViolation

-- GENERALIZES execBlock_while_step to source executions with a data-dependent postcondition.
theorem internalValueBlockResult.while_step {α : Type} {cfg : Config} {f f' : Frame}
    {e e' : State} {cond : Expr} {body : List Stmt} {post : α → Frame → Prop}
    {result : InternalValueOutcome α}
    (hc : evalExpr? cfg f e cond = .ok (.bool true))
    (hb : ExecBlock cfg f e body (.ok f' e'))
    (ht : internalValueBlockResult cfg f' e' [.while cond body] post result) :
    internalValueBlockResult cfg f e [.while cond body] post result := by
  cases result with
  | reverted => exact execBlock_while_step hc hb ht
  | staticViolation => exact execBlock_while_step hc hb ht
  | ok evm value =>
      obtain ⟨final, ht, hp⟩ := ht
      exact ⟨final, execBlock_while_step hc hb ht, hp⟩

end Benchmarks.CompoundIII.Comet
