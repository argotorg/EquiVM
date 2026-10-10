import Benchmarks.UniswapV3.Pool.OracleWriteTrace
import Benchmarks.UniswapV3.Pool.OracleObserveZeroPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem oracleWriteMemory_prefix (mem : ByteArray) (p : UInt256) (a : OracleWriteArgs)
    (evm : EVM.State) (hb : p.toNat + 384 ≤ 2 ^ 200) :
    MemoryPrefix mem (oracleWriteMemory mem p a evm) p.toNat := by
  simpa only [oracleWriteMemory, oracleWriteSame, oracleObserveZeroMemory, decide_eq_true_eq] using
    oracleObserveZeroMemory_prefix mem p (oracleWriteLast a evm) a.time a.tick a.liquidity hb

theorem oracleWriteFree_bounds (p : UInt256) (a : OracleWriteArgs)
    (evm : EVM.State) (hb : p.toNat + 384 ≤ 2 ^ 200) :
    p.toNat ≤ (oracleWriteFree p a evm).toNat ∧
      (oracleWriteFree p a evm).toNat ≤ p.toNat + 384 := by
  constructor
  · simpa only [oracleWriteFree, oracleWriteSame, oracleObserveZeroFree, decide_eq_true_eq] using
      oracleObserveZeroFree_lower p (oracleWriteLast a evm) a.time hb
  · simpa only [oracleWriteFree, oracleWriteSame, oracleObserveZeroFree, decide_eq_true_eq] using
      oracleObserveZeroFree_bound p (oracleWriteLast a evm) a.time hb

end Benchmarks.UniswapV3.Pool
