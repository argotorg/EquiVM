import Benchmarks.UniswapV3.Pool.OracleSearchBefore
import Benchmarks.UniswapV3.Pool.ObservationPair

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchInitializeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cardRaw indexRaw targetRaw timeRaw ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20379⟩
      (cardRaw :: indexRaw :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200) (hov : R.length + 26 ≤ 1024) :
    ∃ aw' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨20395⟩
        ((p + ⟨128⟩) :: p :: cardRaw :: indexRaw :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
        (oracleSearchZeroMem mem p) aw' rdata σ k' C' ∧
      HeapMemory (oracleSearchZeroMem mem p) aw' (p + ⟨128⟩ + ⟨128⟩) ∧
      MemoryPrefix mem (oracleSearchZeroMem mem p) p.toNat ∧
      (p + ⟨128⟩ + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  exact observationPairInitializeX (v := v) true rd hm hb (by evm_ov)

end Benchmarks.UniswapV3.Pool
