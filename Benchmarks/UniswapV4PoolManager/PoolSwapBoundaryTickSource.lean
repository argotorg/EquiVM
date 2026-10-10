import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapTickSyntax
import Benchmarks.UniswapV4PoolManager.WordNarrowArithmeticSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapBoundaryTick (zeroForOne : Bool) (tick : UInt256) : UInt256 :=
  if zeroForOne then UInt256.signextend (UInt256.ofNat 2) (UInt256.sub tick ⟨1⟩) else tick

theorem poolSwapBoundaryTickSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecStmt config f evm poolSwapBoundaryTickStmt
      (.ok (valueLocal f "result" (poolSwapResultValue {r with tick := poolSwapBoundaryTick zeroForOne s.tickNext})) evm) := by
  have he : evalExpr? config f evm
      (.ite (.var "zeroForOne")
        (.cast (.binary .sub (.field (.var "step") "tickNext") (.intLit 1)) (.elem (.int (.sint ⟨24, by decide⟩))))
        (.field (.var "step") "tickNext")) =
      .ok (.int (EVM.signed (poolSwapBoundaryTick zeroForOne s.tickNext))) := by
    rw [evalExpr?, evalLocalValue hz]
    cases zeroForOne with
    | false => exact poolSwapStep_tick_eval hs
    | true =>
      exact evalSigned24Sub (poolSwapStep_tick_eval hs)
        (show evalExpr? config f evm (.intLit 1) = .ok (.int (EVM.signed (⟨1⟩ : UInt256))) by
          simp only [evalExpr?, pure]; rfl)
  exact ExecStmt.assign he (assignLocalField hr rfl rfl)

end Benchmarks.UniswapV4PoolManager
