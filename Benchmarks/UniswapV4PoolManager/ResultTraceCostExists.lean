import Benchmarks.UniswapV4PoolManager.ReachCostExists
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: preserve costs with existential stack or result witnesses.
theorem blockResultTrace_retainCost_exists {α : Type} {code : ByteArray} {I J : ExecutionEnv}
    {g : Sat256} {s0 : State} {entry : Cursor} {k C : Nat} {result : ExecResult}
    {facts : Frame → State → α → Prop} {next : Frame → State → α → Cursor}
    (routine : ∀ (budget : Sat256) (start : State) (ki Ci : Nat),
      RDc code I budget start entry ki Ci →
      blockResultTrace code budget start
        (fun f post => ∃ a kr Cr, facts f post a ∧ RDc code J budget start (next f post a) kr Cr)
        (fun _ _ => False) result)
    (h : RDc code I g s0 entry k C) :
    blockResultTrace code g s0
      (fun f post => ∃ a kr Cr, facts f post a ∧ C ≤ Cr ∧ RDc code J g s0 (next f post a) kr Cr)
      (fun _ _ => False) result := by
  have hr := routine g s0 k C h
  cases result with
  | ok f post => exact RD_retainCost_exists (fun budget start hin => routine budget start 0 0 hin) h
  | reverted | staticViolation => exact hr
  | returned | «break» | «continue» => exact False.elim hr

theorem functionResultTrace_retainCost_exists {α : Type} {code : ByteArray} {I J : ExecutionEnv}
    {g : Sat256} {s0 : State} {entry : Cursor} {k C : Nat} {result : ExecResult}
    {facts : State → Option (List Value) → α → Prop}
    {next : State → Option (List Value) → α → Cursor}
    (routine : ∀ (budget : Sat256) (start : State) (ki Ci : Nat),
      RDc code I budget start entry ki Ci →
      functionResultTrace code budget start
        (fun post values => ∃ a kr Cr, facts post values a ∧
          RDc code J budget start (next post values a) kr Cr) result)
    (h : RDc code I g s0 entry k C) :
    functionResultTrace code g s0
      (fun post values => ∃ a kr Cr, facts post values a ∧ C ≤ Cr ∧
        RDc code J g s0 (next post values a) kr Cr) result := by
  have hr := routine g s0 k C h
  cases result with
  | returned f post values => exact RD_retainCost_exists (fun budget start hin => routine budget start 0 0 hin) h
  | reverted | staticViolation => exact hr
  | ok | «break» | «continue» => exact False.elim hr

end Benchmarks.UniswapV4PoolManager
