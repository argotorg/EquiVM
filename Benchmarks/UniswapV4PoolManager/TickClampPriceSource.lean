import Benchmarks.UniswapV4PoolManager.TickClampSource
import Benchmarks.UniswapV4PoolManager.TickSqrtSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickClampPriceFrame (f : Frame) (s : PoolSwapStepWords) : Frame :=
  valueLocal (tickClampFrame f s) "__c13"
    (.int (Int.ofNat (tickSqrtPrice (EVM.signed (tickClampWord s.tickNext))).toNat))

theorem tickClampPriceSource {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hf : f.contract = contract) (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hc : int24Canonical s.tickNext) :
    ExecBlock config f evm ((poolSwapLoopBody.drop 5).take 3) (.ok (tickClampPriceFrame f s) evm) := by
  have hstep := tickClampFrame_step hs hc
  have hb := tickClampWord_natAbs s.tickNext
  have hcall := tickSqrtCall ((tickClampFrame_contract f s).trans hf)
    (poolSwapStep_tick_eval (evm := evm) hstep) (by change (EVM.signed (tickClampWord s.tickNext)).natAbs < 2^256; omega) "__c13"
  rw [if_pos hb] at hcall
  exact execBlock_append (tickClampSource hs hc) (execBlock_singleton hcall)

end Benchmarks.UniswapV4PoolManager
