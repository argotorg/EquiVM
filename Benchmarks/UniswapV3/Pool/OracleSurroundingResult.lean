import Benchmarks.UniswapV3.Pool.OracleSurroundingSource
import Benchmarks.UniswapV3.Pool.OracleReadMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure OracleSurroundingExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time target : UInt256) (tick : Int) (index liquidity card : UInt256) (initMem : ByteArray) (initAw initFree : UInt256)
    (initCost : Nat) where
  mem : ByteArray
  aw : UInt256
  free : UInt256
  beforePtr : UInt256
  afterPtr : UInt256
  before : OracleObservation
  after : OracleObservation
  k : Nat
  cost : Nat
  rd : RD (deployedRuntime v) ee g s0 ret (afterPtr :: beforePtr :: R) mem aw rdata σ k cost
  run : OracleSurroundingRun time target tick index liquidity card σ ee before after
  heap : HeapMemory mem aw free
  before_mem : ObservationMemory mem beforePtr before
  after_mem : ObservationMemory mem afterPtr after
  before_lower : 128 ≤ beforePtr.toNat
  before_end : beforePtr.toNat + 128 ≤ free.toNat
  after_lower : 128 ≤ afterPtr.toNat
  after_end : afterPtr.toNat + 128 ≤ free.toNat
  free_mono : initFree.toNat ≤ free.toNat
  memory_prefix : MemoryPrefix initMem mem initFree.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + (Cₘ aw - Cₘ initAw) ≤ cost

def OracleSurroundingExit.lift {v : UniswapV3PoolImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {rdata : ByteArray} {ret : UInt256} {R : List UInt256}
    {time target index liquidity card : UInt256} {tick : Int}
    {initMem nextMem : ByteArray} {initAw initFree nextAw nextFree : UInt256}
    {initCost nextCost : Nat}
    (out : OracleSurroundingExit v ee g s0 σ rdata ret R time target tick index liquidity card
      nextMem nextAw nextFree nextCost)
    (hcost : initCost + (Cₘ nextAw - Cₘ initAw) ≤ nextCost)
    (hfree : initFree.toNat ≤ nextFree.toNat)
    (hpre : MemoryPrefix initMem nextMem initFree.toNat) :
    OracleSurroundingExit v ee g s0 σ rdata ret R time target tick index liquidity card
      initMem initAw initFree initCost :=
  { out with
    free_mono := Nat.le_trans hfree out.free_mono
    memory_prefix := hpre.trans (out.memory_prefix.mono hfree)
    cost_bound := by have h := out.cost_bound; omega }

end Benchmarks.UniswapV3.Pool
