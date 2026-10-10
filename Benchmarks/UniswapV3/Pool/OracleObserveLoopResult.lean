import Benchmarks.UniswapV3.Pool.OracleObserveArrays
import Benchmarks.UniswapV3.Pool.OracleObserveRun

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

def oracleObserveCleanAgos (rawAgos : List UInt256) : List UInt256 :=
  rawAgos.map (UInt256.land (UInt256.ofNat 4294967295))

structure OracleObserveLoopExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time : UInt256) (rawAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (agoPtr ticksPtr secondsPtr : UInt256) (i : Nat) (initTicks initSeconds : List Int)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) where
  mem : ByteArray
  aw : UInt256
  free : UInt256
  ticks : List Int
  seconds : List Int
  k : Nat
  cost : Nat
  rd : RD (deployedRuntime v) ee g s0 ret (secondsPtr :: ticksPtr :: R) mem aw rdata σ k cost
  run : OracleObserveLoopRun time (oracleObserveCleanAgos rawAgos) tick index liquidity card σ ee i
    (initTicks.map Value.int) (initSeconds.map Value.int) (ticks.map Value.int) (seconds.map Value.int)
  heap : MemoryCursor mem aw free
  layout : OracleObserveLayout free agoPtr ticksPtr secondsPtr rawAgos.length
  arrays : OracleObserveArrays mem agoPtr ticksPtr secondsPtr rawAgos ticks seconds
  free_mono : initFree.toNat ≤ free.toNat
  memory_prefix : MemoryPrefix initMem mem ticksPtr.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + (Cₘ aw - Cₘ initAw) ≤ cost

abbrev OracleObserveLoopOutcome (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time : UInt256) (rawAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (agoPtr ticksPtr secondsPtr : UInt256) (i : Nat) (initTicks initSeconds : List Int)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) : Prop :=
  X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
  (OracleObserveLoopFailure time (oracleObserveCleanAgos rawAgos) tick index liquidity card σ ee i
    (initTicks.map Value.int) (initSeconds.map Value.int) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
  Nonempty (OracleObserveLoopExit v ee g s0 σ rdata ret R time rawAgos tick index liquidity card
    agoPtr ticksPtr secondsPtr i initTicks initSeconds initMem initAw initFree initCost)

end Benchmarks.UniswapV3.Pool
