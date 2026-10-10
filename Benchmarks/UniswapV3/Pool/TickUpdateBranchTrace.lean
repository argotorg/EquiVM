import Benchmarks.UniswapV3.Pool.TickUpdateWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickUpdateWorkingWords (a : TickUpdateArgs) (evm : EVM.State) : List UInt256 :=
  EVM.wordOfInt (tickUpdateGrossAfter a evm) :: EVM.wordOfInt (tickUpdateGrossBefore a evm) ::
    tickClearBase a.tick :: (tickUpdateFlipped a evm).toUInt256 :: tickUpdateWords a

def tickUpdateFirstWritePC (a : TickUpdateArgs) (evm : EVM.State) : UInt256 :=
  if tickUpdateGrossBefore a evm = 0 then
    if a.tick ≤ a.current then ⟨20956⟩ else ⟨21082⟩
  else ⟨21130⟩

theorem tickUpdateFirstWriteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw unused ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20916⟩
      (EVM.wordOfInt (tickUpdateGrossAfter a evm) :: EVM.wordOfInt (tickUpdateGrossBefore a evm) ::
        tickClearBase a.tick :: unused :: tickUpdateWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.TraceFits) (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (tickUpdateFirstWritePC a evm)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (EVM.wordOfInt (tickUpdateGrossBefore a evm)) = EVM.wordOfInt (tickUpdateGrossBefore a evm) :=
    by rw [tickUpdateGrossBefore_word]; exact uint128Word_clean (tickGrossWord_lt _ _ _)
  have hb := tickUpdateGrossBefore_bounds a evm
  have hz : UInt256.isZero (EVM.wordOfInt (tickUpdateGrossBefore a evm)) =
      (decide (tickUpdateGrossBefore a evm = 0)).toUInt256 :=
    isZero_wordOfInt _ (by omega) (by omega)
  have hf : UInt256.isZero (UInt256.eq
      (UInt256.isZero (UInt256.land (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
        (EVM.wordOfInt (tickUpdateGrossBefore a evm))))
      (UInt256.isZero (UInt256.land (EVM.wordOfInt (tickUpdateGrossAfter a evm))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1))))) = (tickUpdateFlipped a evm).toUInt256 := by
    simpa only [tickUpdateGrossBefore_word] using tickUpdateFlipped_word a evm
  by_cases h0 : tickUpdateGrossBefore a evm = 0
  · have r0 := uniswapV3Pool_block_20916_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 7 ≤ 1024; omega)
      (by rw [solcMask128, hc, hz, decide_eq_true h0]; rfl) rd
    simp only [uniswapV3Pool_block_20916_fallthrough_stack, hf] at r0
    by_cases ht : a.tick ≤ a.current
    · have r1 := uniswapV3Pool_block_20943_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 17 ≤ 1024; omega)
        (by rw [tickUpdateCompare_word a hfit, if_neg (by omega)]; rfl) r0
      exact ⟨_, _, by simpa only [tickUpdateFirstWritePC, if_pos h0, if_pos ht,
        tickUpdateWorkingWords, List.cons_append] using r1⟩
    · have r1 := uniswapV3Pool_block_20943_taken (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 17 ≤ 1024; omega)
        (by rw [tickUpdateCompare_word a hfit, if_pos (by omega)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r0
      exact ⟨_, _, by simpa only [tickUpdateFirstWritePC, if_pos h0, if_neg ht,
        tickUpdateWorkingWords, List.cons_append] using r1⟩
  · have r0 := uniswapV3Pool_block_20916_taken (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 7 ≤ 1024; omega)
      (by rw [solcMask128, hc, hz, decide_eq_false h0]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_20916_taken_stack, hf,
      tickUpdateFirstWritePC, if_neg h0, tickUpdateWorkingWords, List.cons_append] using r0⟩

end Benchmarks.UniswapV3.Pool
