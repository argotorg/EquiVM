import Benchmarks.UniswapV3.Pool.TickSqrtReadySource
import Benchmarks.UniswapV3.Pool.TickSqrtTailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem tickSqrtReturns (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (h : tick.natAbs ≤ 887272) :
    ∃ out, ExecFuncBody config (tickSqrtFrame imms tick) evm tickSqrtFunction.body
      (.returned out evm (some [.int (Int.ofNat (tickSqrtValue tick).toNat)])) := by
  obtain ⟨frame, hp, hr, ht, hs⟩ := tickSqrtRatiosSource imms evm tick hlo hhi h
  obtain ⟨out, hb⟩ := tickSqrtTailSource (evm := evm) tick
    (tickSqrtRatio (UInt256.ofNat tick.natAbs)) ht hr hs (tickSqrtRatio_bounds _).1
  refine ⟨out, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 23 tickSqrtFunction.body]
  exact execBlock_append_ok hp hb

end Benchmarks.UniswapV3.Pool
