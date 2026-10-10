import Benchmarks.UniswapV3.Pool.OracleObserveSingleResult
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free card liquidity index : UInt256}
    {tickArg secondsAgoRaw timeRaw ret time secondsAgo tickRaw secondsRaw : UInt256}
    {tick tickValue secondsValue : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13584⟩
      (secondsRaw :: tickRaw :: card :: liquidity :: index :: tickArg :: secondsAgoRaw ::
        timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hrun : OracleObserveSingleRun time secondsAgo tick index liquidity card σ ee
      [.int tickValue, .int secondsValue])
    (htw : UInt256.signextend (UInt256.ofNat 6) tickRaw = EVM.wordOfInt tickValue)
    (hsw : UInt256.land secondsRaw (UInt256.ofNat (2 ^ 160 - 1)) = EVM.wordOfInt secondsValue)
    (htr : -(2 ^ 55 : Int) ≤ tickValue ∧ tickValue < 2 ^ 55)
    (hsr : 0 ≤ secondsValue ∧ secondsValue < 2 ^ 160)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    Nonempty (OracleObserveSingleExit v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C) := by
  have r := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) hov hret rd
  exact ⟨{ mem := mem
           aw := aw
           free := free
           tickRaw := tickRaw
           secondsRaw := secondsRaw
           tickValue := tickValue
           secondsValue := secondsValue
           k := k + 12
           cost := C + 32
           rd := r
           run := hrun
           tick_word := htw
           seconds_word := hsw
           tick_range := htr
           seconds_range := hsr
           heap := hm
           free_mono := le_refl _
           memory_prefix := MemoryPrefix.refl _ _
           cover := hcover
           cost_bound := by omega }⟩

end Benchmarks.UniswapV3.Pool
