import Benchmarks.UniswapV3.Pool.OracleSearchBefore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure OracleSearchExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time target card left right : UInt256) (initMem : ByteArray) (initAw initFree : UInt256)
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
  run : OracleSearchRun time target card σ ee left right before after
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

def OracleSearchExit.lift {v : UniswapV3PoolImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {rdata : ByteArray} {ret : UInt256} {R : List UInt256}
    {time target card left right nextLeft nextRight : UInt256}
    {initMem nextMem : ByteArray} {initAw initFree nextAw nextFree : UInt256}
    {initCost nextCost : Nat}
    (out : OracleSearchExit v ee g s0 σ rdata ret R time target card nextLeft nextRight
      nextMem nextAw nextFree nextCost)
    (hrun : ∀ before after, OracleSearchRun time target card σ ee nextLeft nextRight before after →
      OracleSearchRun time target card σ ee left right before after)
    (hcost : initCost + (Cₘ nextAw - Cₘ initAw) ≤ nextCost)
    (hfree : initFree.toNat ≤ nextFree.toNat)
    (hpre : MemoryPrefix initMem nextMem initFree.toNat) :
    OracleSearchExit v ee g s0 σ rdata ret R time target card left right
      initMem initAw initFree initCost :=
  { out with
    run := hrun _ _ out.run
    free_mono := Nat.le_trans hfree out.free_mono
    memory_prefix := hpre.trans (out.memory_prefix.mono hfree)
    cost_bound := by have h := out.cost_bound; omega }

end Benchmarks.UniswapV3.Pool
