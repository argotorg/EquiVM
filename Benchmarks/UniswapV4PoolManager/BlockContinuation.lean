import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: sequence result models while preserving every terminal outcome.
def continueBlockResult (next : Frame → State → ExecResult) : ExecResult → ExecResult
  | .ok f post => next f post
  | result => result

theorem continueBlockResult_ok {next : Frame → State → ExecResult} {result : ExecResult}
    {f : Frame} {post : State} (h : continueBlockResult next result = .ok f post) :
    ∃ before initial, result = .ok before initial ∧ next before initial = .ok f post := by
  cases result with
  | ok before initial => exact ⟨before, initial, rfl, h⟩
  | returned | reverted | «break» | «continue» | staticViolation => cases h

theorem execBlock_continue {cfg : Config} {f : Frame} {evm : State} {pre rest : List Stmt}
    {result : ExecResult} {next : Frame → State → ExecResult}
    (hp : ExecBlock cfg f evm pre result)
    (hn : ∀ f' post, result = .ok f' post → ExecBlock cfg f' post rest (next f' post)) :
    ExecBlock cfg f evm (pre ++ rest) (continueBlockResult next result) := by
  cases result with
  | ok f' post => exact execBlock_append hp (hn f' post rfl)
  | returned | reverted | «break» | «continue» | staticViolation =>
    exact execBlock_append_term hp (by intros; intro he; cases he)

end Benchmarks.UniswapV4PoolManager
