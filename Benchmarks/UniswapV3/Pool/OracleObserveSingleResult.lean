import Benchmarks.UniswapV3.Pool.OracleObservationTypes
import Benchmarks.UniswapV3.Pool.OracleReadMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure OracleObserveSingleExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) where
  mem : ByteArray
  aw : UInt256
  free : UInt256
  tickRaw : UInt256
  secondsRaw : UInt256
  tickValue : Int
  secondsValue : Int
  k : Nat
  cost : Nat
  rd : RD (deployedRuntime v) ee g s0 ret (secondsRaw :: tickRaw :: R) mem aw rdata σ k cost
  run : OracleObserveSingleRun time secondsAgo tick index liquidity card σ ee
    [.int tickValue, .int secondsValue]
  tick_word : UInt256.signextend (UInt256.ofNat 6) tickRaw = EVM.wordOfInt tickValue
  seconds_word : UInt256.land secondsRaw (UInt256.ofNat (2 ^ 160 - 1)) = EVM.wordOfInt secondsValue
  tick_range : -(2 ^ 55 : Int) ≤ tickValue ∧ tickValue < 2 ^ 55
  seconds_range : 0 ≤ secondsValue ∧ secondsValue < 2 ^ 160
  heap : HeapMemory mem aw free
  free_mono : initFree.toNat ≤ free.toNat
  memory_prefix : MemoryPrefix initMem mem initFree.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + (Cₘ aw - Cₘ initAw) ≤ cost

abbrev OracleObserveSingleOutcome (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) : Prop :=
  X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
  (OracleObserveSingleFailure time secondsAgo tick index liquidity card σ ee ∧
    (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
  Nonempty (OracleObserveSingleExit v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
    initMem initAw initFree initCost)

def OracleObserveSingleExit.lift {v : UniswapV3PoolImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {rdata : ByteArray} {ret : UInt256} {R : List UInt256}
    {time secondsAgo index liquidity card : UInt256} {tick : Int}
    {initMem nextMem : ByteArray} {initAw initFree nextAw nextFree : UInt256}
    {initCost nextCost : Nat}
    (out : OracleObserveSingleExit v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      nextMem nextAw nextFree nextCost)
    (hcost : initCost + (Cₘ nextAw - Cₘ initAw) ≤ nextCost)
    (hfree : initFree.toNat ≤ nextFree.toNat)
    (hpre : MemoryPrefix initMem nextMem initFree.toNat) :
    OracleObserveSingleExit v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      initMem initAw initFree initCost :=
  { out with
    free_mono := Nat.le_trans hfree out.free_mono
    memory_prefix := hpre.trans (out.memory_prefix.mono hfree)
    cost_bound := by have h := out.cost_bound; omega }

end Benchmarks.UniswapV3.Pool
