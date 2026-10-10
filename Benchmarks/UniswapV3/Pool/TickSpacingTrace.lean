import Benchmarks.UniswapV3.Pool.TickSpacingWords
import Benchmarks.UniswapV3.Pool.SignedWordZero
import Benchmarks.UniswapV3.Pool.CreationBlocks_001
import Benchmarks.UniswapV3.Pool.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open uniswapV3PoolCreationBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickSpacingCreationX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret word : UInt256} {mem rdata tail : ByteArray}
    {R : List UInt256} (spacing : Int)
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨271⟩
      (word :: ret :: R) mem aw rdata σ k C)
    (hclean : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat) = spacing)
    (hlo : -(2 ^ 23 : Int) ≤ spacing) (hhi : spacing < 2 ^ 23)
    (hret : (D_J uniswapV3PoolCreationBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    (RDinvalid (uniswapV3PoolCreationBytecode ++ tail) g s0 ∧
      (spacing = 0 ∨ spacingCount spacing = 0)) ∨
    (spacing ≠ 0 ∧ spacingCount spacing ≠ 0 ∧ ∃ k' C',
      RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ret
        (EVM.wordOfInt (spacingLiquidity spacing) :: R) mem aw rdata σ k' C') := by
  have hz : UInt256.signextend (UInt256.ofNat 2) word = ⟨0⟩ ↔ spacing = 0 := by
    rw [spacingWord_clean word spacing hclean]
    exact wordOfInt_zero_iff_signed spacing (by omega) (by omega)
  by_cases hspacing : spacing = 0
  · have rbad := uniswapV3PoolCreation_block_271_fallthrough (by evm_ov) (hz.mpr hspacing) rd
    exact Or.inl ⟨uniswapV3PoolCreation_block_292 rbad, Or.inl hspacing⟩
  have hn : UInt256.signextend (UInt256.ofNat 2) word ≠ ⟨0⟩ :=
    fun h ↦ hspacing (hz.mp h)
  have rmin := uniswapV3PoolCreation_block_271_taken (by evm_ov) hn (by native_decide) rd
  simp only [uniswapV3PoolCreation_block_271_taken_stack] at rmin
  have rmax := uniswapV3PoolCreation_block_293_taken (by evm_ov) hn (by native_decide) rmin
  simp only [uniswapV3PoolCreation_block_293_taken_stack] at rmax
  have rdelta := uniswapV3PoolCreation_block_317_taken (by evm_ov) hn (by native_decide) rmax
  change RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨341⟩
    (spacingDeltaRaw word ::
      UInt256.signextend (UInt256.ofNat 2) word :: ⟨0⟩ ::
      spacingMaxRaw word :: spacingMinRaw word ::
      ⟨0⟩ :: word :: ret :: R) mem aw rdata σ _ _ at rdelta
  have hc := spacingCount_bounds spacing
  have hzCount : spacingCountRaw word = ⟨0⟩ ↔ spacingCount spacing = 0 := by
    rw [spacingCountRaw_eq word spacing hclean hlo hhi]
    exact wordOfInt_zero_iff_signed _ (by omega) (by omega)
  by_cases hcount : spacingCount spacing = 0
  · have rbad := uniswapV3PoolCreation_block_341_fallthrough (by evm_ov) (hzCount.mpr hcount) rdelta
    exact Or.inl ⟨uniswapV3PoolCreation_block_370 rbad, Or.inr hcount⟩
  have rdiv := uniswapV3PoolCreation_block_341_taken (by evm_ov)
    (show spacingCountRaw word ≠ ⟨0⟩ from fun h ↦ hcount (hzCount.mp h))
    (by native_decide) rdelta
  simp only [uniswapV3PoolCreation_block_341_taken_stack] at rdiv
  have rout := uniswapV3PoolCreation_block_371 (by evm_ov) hret rdiv
  change RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ret
    (spacingLiquidityRaw word :: R) mem aw rdata σ _ _ at rout
  rw [spacingLiquidityRaw_eq word spacing hclean hlo hhi] at rout
  exact Or.inr ⟨hspacing, hcount, _, _, rout⟩

end Benchmarks.UniswapV3.Pool
