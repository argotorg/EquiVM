import Benchmarks.UniswapV3.Pool.TickCrossWords
import Benchmarks.UniswapV3.Pool.TickUpdateMemory
import Benchmarks.UniswapV3.Pool.TickUpdateNetEntryTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickCrossWords (a : TickCrossArgs) : List UInt256 :=
  [a.time, EVM.wordOfInt a.cumulative, a.secondsPerLiquidity, a.global1, a.global0,
   EVM.wordOfInt a.tick, ⟨5⟩]

def tickCrossHistoryStack (a : TickCrossArgs) (σ : AccountMap) (ee : ExecutionEnv) : List UInt256 :=
  let old := solcSlotWordAt (tickFieldSlot a.tick 3) σ ee
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
    (UInt256.ofNat 1)
  [a.secondsPerLiquidity, UInt256.land mask (UInt256.div old (UInt256.ofNat 72057594037927936)),
   mask, UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216), UInt256.ofNat 4294967295,
   old, tickFieldSlot a.tick 3, UInt256.ofNat 72057594037927936,
   tickClearBase a.tick, EVM.wordOfInt a.cumulative, a.time]

theorem tickCrossFeesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickCrossArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13596⟩ (tickCrossWords a ++ R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23)
    (hp : ee.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨13683⟩
      (tickCrossHistoryStack a (tickCrossFeesMap a σ ee) ee ++ R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw)
      rdata (tickCrossFeesMap a σ ee) k' C' := by
  have ht' : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.tick) =
      EVM.wordOfInt a.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ ht.1 ht.2]
  obtain ⟨k', C', r'⟩ := uniswapV3Pool_block_13596 (immWords := wordsOf (immStore v)) hov hp rd
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (uniswapV3Pool_block_13596_memory (mem := mem) (x5 := EVM.wordOfInt a.tick)
        (x6 := ⟨5⟩)) = tickClearBase a.tick := by
    simp only [uniswapV3Pool_block_13596_memory, ht']
    exact twoWordHashMem_solcMappingSlot_any _ _ _
  simp only [uniswapV3Pool_block_13596_stack, uniswapV3Pool_block_13596_memory, ht'] at r' hh
  rw [hh] at r'
  refine ⟨k', C', ?_⟩
  simpa only [tickCrossHistoryStack, tickCrossFeesMap, tickCrossFeeMap, tickCrossFeeWord,
    TickCrossArgs.global, tickFeeOutside, tickFieldSlot, tickClearBase, if_true,
    Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using r'

theorem tickCrossHistoryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickCrossArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13683⟩
      (tickCrossHistoryStack a σ ee ++ ret :: R) mem aw rdata σ k C)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    let σ' := sstoreAccountMap ee.codeOwner σ (tickFieldSlot a.tick 3)
      (tickCrossOutsideWord a (solcSlotWordAt (tickFieldSlot a.tick 3) σ ee))
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (tickNetValue σ' ee a.tick) :: R) mem aw rdata σ' k' C' := by
  dsimp only
  obtain ⟨kw, Cw, rw⟩ := uniswapV3Pool_block_13683 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 11 ≤ 1024; omega) hp rd
  simp only [uniswapV3Pool_block_13683_stack] at rw
  change RD (deployedRuntime v) ee g s0 ⟨13801⟩
    (solcSlotWordAt (tickClearBase a.tick)
      (sstoreAccountMap ee.codeOwner σ (tickFieldSlot a.tick 3)
        (tickCrossSecondsRawWord a.time (tickCrossCumulativeRawWord (EVM.wordOfInt a.cumulative)
          (tickCrossLiquidityRawWord a.secondsPerLiquidity
            (solcSlotWordAt (tickFieldSlot a.tick 3) σ ee))))) ee ::
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) :: ret :: R)
    mem aw rdata (sstoreAccountMap ee.codeOwner σ (tickFieldSlot a.tick 3)
      (tickCrossSecondsRawWord a.time (tickCrossCumulativeRawWord (EVM.wordOfInt a.cumulative)
        (tickCrossLiquidityRawWord a.secondsPerLiquidity
          (solcSlotWordAt (tickFieldSlot a.tick 3) σ ee))))) kw Cw at rw
  simp only [← tickCrossLiquidityWord, ← tickCrossCumulativeWord, ← tickCrossSecondsWord] at rw
  have rr := uniswapV3Pool_block_13801 (immWords := wordsOf (immStore v))
    (by evm_ov) hret rw
  refine ⟨kw + 5, Cw + 24, ?_⟩
  simpa only [uniswapV3Pool_block_13801_stack, ← tickNetValue_word, tickCrossOutsideWord] using rr

theorem tickCrossX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickCrossArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13596⟩
      (tickCrossWords a ++ ret :: R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (tickNetValue (tickCrossMap a σ ee) ee a.tick) :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw)
      rdata (tickCrossMap a σ ee) k' C' := by
  obtain ⟨kf, Cf, rf⟩ := tickCrossFeesX (v := v) a rd ht hp (by simpa using hov)
  exact tickCrossHistoryX (v := v) a rf hp hret (by omega)

end Benchmarks.UniswapV3.Pool
