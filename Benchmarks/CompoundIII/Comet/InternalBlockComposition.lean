import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: specialize a void-call outcome without unfolding the caller's state.
theorem internalStmtResult.cast {cfg frame evm stmt final ret result result'}
    (hb : ExecStmt cfg frame evm stmt (internalStmtResult final ret result))
    (he : result = result') :
    ExecStmt cfg frame evm stmt (internalStmtResult final ret result') := by
  cases he
  exact hb

-- GENERALIZES internalBlockResult.prepend from one statement to a completed block.
theorem internalBlockResult.prependBlock {cfg frame evm frame' evm' first rest result}
    (hb : internalBlockResult cfg frame' evm' rest result)
    (hp : ExecBlock cfg frame evm first (.ok frame' evm')) :
    internalBlockResult cfg frame evm (first ++ rest) result := by
  cases result with
  | ok evm'' =>
    obtain ⟨final, hb⟩ := hb
    exact ⟨final, Reasoning.Theory.execBlock_append hp hb⟩
  | reverted => exact Reasoning.Theory.execBlock_append hp hb
  | staticViolation => exact Reasoning.Theory.execBlock_append hp hb

end Benchmarks.CompoundIII.Comet
