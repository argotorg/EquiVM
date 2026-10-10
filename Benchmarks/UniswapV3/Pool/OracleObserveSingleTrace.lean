import Benchmarks.UniswapV3.Pool.OracleObserveZeroTrace
import Benchmarks.UniswapV3.Pool.OracleObserveNonzeroTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem oracleObserveSingleCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time secondsAgo : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = secondsAgo)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : MemoryCursor mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 53 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C := by
  by_cases hz : secondsAgo = ⟨0⟩
  · simpa only [hz] using oracleObserveSingleZeroCursorX (v := v) rd hi htime
      (hago.trans hz) htick hliq hm hbudget hallowance hcover hret (by omega)
  · exact oracleObserveSingleNonzeroCursorX (v := v) rd hi hc htime hago hz htick hliq hm hbudget
      hallowance hcover hret hov

theorem oracleObserveSingleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time secondsAgo : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = secondsAgo)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 53 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C := by
  exact oracleObserveSingleCursorX (v := v) rd hi hc htime hago htick hliq hm.cursor hbudget hallowance hcover hret hov

end Benchmarks.UniswapV3.Pool
