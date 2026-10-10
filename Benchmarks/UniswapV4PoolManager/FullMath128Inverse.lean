import Benchmarks.UniswapV4PoolManager.FullMath128Reduce
import Benchmarks.UniswapV4PoolManager.FullMathInverse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- The inverse of the reduced denominator 1 remains 1 through all six source updates.
theorem fullMath128Inverse {f : Frame} {evm : EVM.State} {w : UInt256} {old : Value}
    (hd : f.locals.get? "denominator" = some (.int 1))
    (hp : f.locals.get? "prod0" = some (.int (Int.ofNat w.toNat)))
    (hr : f.locals.get? "result" = some old) :
    ∃ f', ExecFuncBody config f evm (fullMathFunction.body.drop 16)
      (.returned f' evm (some [.int (Int.ofNat w.toNat)])) := by
  obtain ⟨f', h⟩ := fullMathInverseBody (evm := evm) (d := ⟨1⟩) hd hp hr
  exact ⟨f', by simpa only [fullMathInverse_one, wordMulOne] using h⟩

end Benchmarks.UniswapV4PoolManager
