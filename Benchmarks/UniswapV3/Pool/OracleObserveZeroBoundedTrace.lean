import Benchmarks.UniswapV3.Pool.OracleObserveZeroCanonical
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveSingleZeroBoundedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p card liquidity index tickRaw timeRaw time ret : UInt256}
    {tick : Int} {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: ⟨0⟩ :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    (¬index.toNat < 65535 ∧ RDinvalid (deployedRuntime v) g s0) ∨
      (index.toNat < 65535 ∧ ∃ aw' k' C',
        let last := oracleStoredObservation index σ ee
        RD (deployedRuntime v) ee g s0 ret
          ((oracleObserveZeroResult last time tick liquidity).secondsPerLiquidity ::
            EVM.wordOfInt (oracleObserveZeroResult last time tick liquidity).tickCumulative :: R)
          (oracleObserveZeroMemory mem p last time tick liquidity) aw' rdata σ k' C' ∧
        HeapMemory (oracleObserveZeroMemory mem p last time tick liquidity) aw'
          (oracleObserveZeroFree p last time)) := by
  have hc : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hi
  have r1 := uniswapV3Pool_block_13193_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by decide) rd
  simp only [uniswapV3Pool_block_13193_fallthrough_stack] at r1
  by_cases hin : index.toNat < 65535
  · have r2 := uniswapV3Pool_block_13208_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hc, ult_one (a := index) (b := UInt256.ofNat 65535) hin]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_13208_taken_stack, hc] at r2
    obtain ⟨_, _, _, r3⟩ := observationReadMonoX (v := v) r2 hm (by omega) (by evm_ov)
    exact Or.inr ⟨hin, oracleObserveZeroCanonicalFinishX (v := v) r3 hm hb htime htick hliq hret hov⟩
  · have r2 := uniswapV3Pool_block_13208_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hc]; exact ult_zero (by change 65535 ≤ index.toNat; omega)) r1
    exact Or.inl ⟨hin, uniswapV3Pool_block_13225 (immWords := wordsOf (immStore v)) r2⟩

end Benchmarks.UniswapV3.Pool
