import Benchmarks.UniswapV4PoolManager.BlockContinuation
import Benchmarks.UniswapV4PoolManager.CallContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: trace a block's normal and return continuations separately.
def blockResultTrace (code : ByteArray) (g : Sat256) (s0 : State)
    (onNormal : Frame → State → Prop) (onReturn : State → Option (List Value) → Prop) : ExecResult → Prop
  | .ok f post => onNormal f post
  | .returned _ post values => onReturn post values
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

-- LIBRARY CANDIDATE: strengthen or transform the normal continuation of a block trace.
theorem blockResultTrace_mono {code : ByteArray} {g : Sat256} {s0 : State}
    {before after : Frame → State → Prop} {onReturn : State → Option (List Value) → Prop}
    {result : ExecResult} (hr : blockResultTrace code g s0 before onReturn result)
    (hn : ∀ f post, result = .ok f post → before f post → after f post) :
    blockResultTrace code g s0 after onReturn result := by
  cases result with
  | ok f post => exact hn f post rfl hr
  | returned | reverted | staticViolation => exact hr
  | «break» | «continue» => exact False.elim hr

-- LIBRARY CANDIDATE: compose a block trace without losing its terminal outcomes.
theorem blockResultTrace_continueBlock {code : ByteArray} {g : Sat256} {s0 : State}
    {before after : Frame → State → Prop} {onReturn : State → Option (List Value) → Prop}
    {result : ExecResult} {next : Frame → State → ExecResult}
    (hr : blockResultTrace code g s0 before onReturn result)
    (hn : ∀ f post, result = .ok f post → before f post →
      blockResultTrace code g s0 after onReturn (next f post)) :
    blockResultTrace code g s0 after onReturn (continueBlockResult next result) := by
  cases result with
  | ok f post => exact hn f post rfl hr
  | returned | reverted | staticViolation => exact hr
  | «break» | «continue» => exact False.elim hr

-- LIBRARY CANDIDATE: connect a callee's return trace to the remaining source block.
theorem blockResultTrace_continueCall {code : ByteArray} {g : Sat256} {s0 : State}
    {before : State → Option (List Value) → Prop} {after : Frame → State → Prop}
    {onReturn : State → Option (List Value) → Prop}
    {result : ExecResult} {next : State → Option (List Value) → ExecResult}
    (hr : functionResultTrace code g s0 before result)
    (hn : ∀ f post values, result = .returned f post values → before post values →
      blockResultTrace code g s0 after onReturn (next post values)) :
    blockResultTrace code g s0 after onReturn (continueCallResult next result) := by
  cases result with
  | returned f post values => exact hn f post values rfl hr
  | reverted | staticViolation => exact hr
  | ok | «break» | «continue» => exact False.elim hr

-- LIBRARY CANDIDATE: trace an internal call after binding its return in the caller.
theorem blockResultTrace_resumeCall {code : ByteArray} {g : Sat256} {s0 : State}
    {before : State → Option (List Value) → Prop} {after : Frame → State → Prop}
    {onReturn : State → Option (List Value) → Prop} {caller : Frame} {ret : Ident} {result : ExecResult}
    (hr : functionResultTrace code g s0 before result)
    (hn : ∀ f post values, result = .returned f post values → before post values →
      after (resumeAfterInternalCall caller ret values) post) :
    blockResultTrace code g s0 after onReturn (resumeCallResult caller ret result) := by
  cases result with
  | returned f post values => exact hn f post values rfl hr
  | reverted | staticViolation => exact hr
  | ok | «break» | «continue» => exact False.elim hr

-- LIBRARY CANDIDATE: finish a block with a function trace while retaining its terminal outcomes.
theorem functionResultTrace_continueBlock {code : ByteArray} {g : Sat256} {s0 : State}
    {before : Frame → State → Prop} {after : State → Option (List Value) → Prop}
    {result : ExecResult} {next : Frame → State → ExecResult}
    (hr : blockResultTrace code g s0 before (fun _ _ => False) result)
    (hn : ∀ f post, result = .ok f post → before f post →
      functionResultTrace code g s0 after (next f post)) :
    functionResultTrace code g s0 after (continueBlockResult next result) := by
  cases result with
  | ok f post => exact hn f post rfl hr
  | reverted | staticViolation => exact hr
  | returned | «break» | «continue» => exact False.elim hr

-- LIBRARY CANDIDATE: turn normal block completion into a void function return.
theorem functionResultTrace_finishNormal {code : ByteArray} {g : Sat256} {s0 : State}
    {before : Frame → State → Prop} {after : State → Option (List Value) → Prop} {result : ExecResult}
    (hr : blockResultTrace code g s0 before (fun _ _ => False) result)
    (hn : ∀ f post, result = .ok f post → before f post → after post none) :
    functionResultTrace code g s0 after (finishBlockResult result) := by
  cases result with
  | ok f post => exact hn f post rfl hr
  | reverted | staticViolation => exact hr
  | returned | «break» | «continue» => exact False.elim hr

end Benchmarks.UniswapV4PoolManager
