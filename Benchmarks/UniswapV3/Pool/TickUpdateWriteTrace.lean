import Benchmarks.UniswapV3.Pool.TickUpdateRawModel
import Benchmarks.UniswapV3.Pool.TickUpdateStorage
import Benchmarks.UniswapV3.Pool.TickUpdateWords
import Benchmarks.UniswapV3.Pool.TickHistoryWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateOutsideX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw after before flipped ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20956⟩
      (after :: before :: tickClearBase a.tick :: flipped :: tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.TraceFits) (hp : ee.perm = true) (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21082⟩
      (after :: before :: tickClearBase a.tick :: flipped :: tickUpdateWords a ++ ret :: R)
      mem aw rdata (tickUpdateOutsideMap a σ ee) k' C' := by
  have hb := hfit.2.2.2.2
  have hc : UInt256.signextend (UInt256.ofNat 6) (EVM.wordOfInt a.cumulative) =
      EVM.wordOfInt a.cumulative := by
    rw [signextend_wordOfInt ⟨56, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨56, by decide⟩ _ hb.1 hb.2]
  obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_20956 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 17 ≤ 1024; omega) hp rd
  refine ⟨kf, Cf, ?_⟩
  simpa only [tickUpdateOutsideMap, tickUpdateOutsideWord, tickHistorySecondsWord,
    tickHistoryCumulativeWord, tickHistorySecondsPerLiquidityWord, tickFieldSlot, tickClearBase, hc]
    using rf

theorem tickUpdateInitializedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw after before : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21082⟩
      (after :: before :: tickClearBase tick :: R) mem aw rdata σ k C)
    (hp : ee.perm = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21130⟩
      (after :: before :: tickClearBase tick :: R) mem aw rdata
      (tickHistoryMap σ ee tick .initialized ⟨1⟩) k' C' := by
  obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21082 (immWords := wordsOf (immStore v)) hov hp rd
  exact ⟨kf, Cf, by simpa only [tickHistoryMap, tickHistoryInitializedWord, tickFieldSlot,
    tickClearBase] using rf⟩

theorem tickUpdateGrossX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw after before flipped ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21130⟩
      (after :: before :: tickClearBase a.tick :: flipped :: tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hp : ee.perm = true) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if a.upper then ⟨21203⟩ else ⟨21161⟩)
      (after :: before :: tickClearBase a.tick :: flipped :: tickUpdateWords a ++ ret :: R)
      mem aw rdata (tickLiquidityMap σ ee a.tick false after) k' C' := by
  cases hu : a.upper
  · obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21130_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 10 + 10 ≤ 1024; omega) hp
      (by rw [hu]; rfl) rd
    exact ⟨kf, Cf, by simpa only [tickUpdateWords, hu, Bool.false_eq_true, if_false, tickLiquidityMap,
      protocolFeeUpdateWord, uint128Word, solcMask128, u256_land_comm] using rf⟩
  · obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21130_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 10 + 10 ≤ 1024; omega) hp
      (by rw [hu]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    exact ⟨kf, Cf, by simpa only [tickUpdateWords, hu, if_true, tickLiquidityMap, protocolFeeUpdateWord,
      Bool.false_eq_true, if_false, uint128Word, solcMask128, u256_land_comm] using rf⟩

end Benchmarks.UniswapV3.Pool
