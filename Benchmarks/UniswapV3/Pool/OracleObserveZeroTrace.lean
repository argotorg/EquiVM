import Benchmarks.UniswapV3.Pool.OracleObserveZeroFinishTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveSingleZeroCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = ⟨0⟩)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : MemoryCursor mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time ⟨0⟩ tick index liquidity card
      mem aw free C := by
  rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
  · exact Or.inl hoog
  have hindex : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hi
  have r1 := uniswapV3Pool_block_13193_fallthrough (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [u256_land_comm]; exact hago) rd
  simp only [uniswapV3Pool_block_13193_fallthrough_stack] at r1
  by_cases hin : index.toNat < 65535
  · have r2 := uniswapV3Pool_block_13208_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [hindex, ult_one (a := index) (b := UInt256.ofNat 65535) hin]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_13208_taken_stack, hindex] at r2
    obtain ⟨k3, C3, hC3, r3⟩ := observationReadCursorX (v := v) r2 hm (by omega) (by evm_ov)
    obtain ⟨out⟩ := oracleObserveZeroFinishCursorX (v := v) (time := time) (tick := tick)
      r3 hm (by omega) hin (by rw [u256_land_comm]; exact htime) htick hliq hret hov
    exact Or.inr (Or.inr ⟨out.lift (by omega) (le_refl _) (MemoryPrefix.refl _ _)⟩)
  · have r2 := uniswapV3Pool_block_13208_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hindex]; exact ult_zero (by change 65535 ≤ index.toNat; omega)) r1
    have rbad := uniswapV3Pool_block_13225 (immWords := wordsOf (immStore v)) r2
    exact Or.inr (Or.inl ⟨.zeroIndex rfl hin, Or.inr rbad⟩)

theorem oracleObserveSingleZeroOutcomeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = ⟨0⟩)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time ⟨0⟩ tick index liquidity card
      mem aw free C := by
  exact oracleObserveSingleZeroCursorX (v := v) rd hi htime hago htick hliq hm.cursor hbudget hallowance hcover hret hov

end Benchmarks.UniswapV3.Pool
