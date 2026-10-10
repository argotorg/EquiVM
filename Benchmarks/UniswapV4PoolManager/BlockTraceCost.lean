import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: rebase a block's successful cursor to preserve the incoming cost floor.
theorem blockResultTrace_retainCost {code : ByteArray} {I J : ExecutionEnv} {g : Sat256}
    {s0 : State} {entry : Cursor} {k C : Nat} {result : ExecResult}
    {facts : Frame → State → Prop} {next : Frame → State → Cursor}
    (routine : ∀ (budget : Sat256) (start : State) (ki Ci : Nat),
      RDc code I budget start entry ki Ci →
      blockResultTrace code budget start
        (fun f post => facts f post ∧ ∃ kr Cr, RDc code J budget start (next f post) kr Cr)
        (fun _ _ => False) result)
    (h : RDc code I g s0 entry k C) :
    blockResultTrace code g s0
      (fun f post => facts f post ∧ ∃ kr Cr, C ≤ Cr ∧ RDc code J g s0 (next f post) kr Cr)
      (fun _ _ => False) result := by
  have hr := routine g s0 k C h
  cases result with
  | ok f post =>
    refine ⟨hr.1, RD_retainCost ?_ h⟩
    intro budget start hin
    exact (routine budget start 0 0 hin).2
  | reverted | staticViolation => exact hr
  | returned | «break» | «continue» => exact False.elim hr

end Benchmarks.UniswapV4PoolManager
