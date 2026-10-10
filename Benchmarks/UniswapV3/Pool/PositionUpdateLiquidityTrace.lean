import Benchmarks.UniswapV3.Pool.PositionUpdateWords
import Benchmarks.UniswapV3.Pool.LiquidityDeltaTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_073

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionUpdateLiquidityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21637⟩
      (⟨0⟩ :: p :: a.growth1 :: a.growth0 :: EVM.wordOfInt a.delta ::
        solcMappingSlot ⟨7⟩ a.key :: ret :: R) mem aw rdata σ k C)
    (hm : WordArrayMemory mem p (positionSnapshotWords a.key evm.accountMap evm.executionEnv))
    (ha : ActiveWords aw) (hb : p.toNat + 160 ≤ 2 ^ 200)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hov : R.length + 18 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ positionUpdateLiquidityValid a evm) ∨
      (positionUpdateLiquidityValid a evm ∧ ∃ aw' k' C',
        RD (deployedRuntime v) ee g s0 ⟨21733⟩
          (EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
            EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
          mem aw' rdata σ k' C' ∧ ActiveWords aw') := by
  have hload := positionSnapshotLoadLiquidity a evm hm
    (show p.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
  have hclean : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad p mem) = positionUpdateLiquidityWord a evm := by
    rw [solcMask128, hload]
    exact uint128Word_clean (positionUpdateLiquidityWord_lt a evm)
  have ha1 := activeWords_expand32 ha (show p.toNat + 32 ≤ 2 ^ 200 by omega)
  by_cases hz : a.delta = 0
  · have r1 := uniswapV3Pool_block_21637_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [positionUpdateDelta_word a hdlo hdhi, hz]; rfl) rd
    by_cases hl : positionUpdateLiquidityWord a evm = ⟨0⟩
    · have r2 := uniswapV3Pool_block_21646_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hclean]; exact hl) r1
      exact Or.inl ⟨uniswapV3Pool_block_21661 (immWords := wordsOf (immStore v)) (by evm_ov) r2,
        by simp [positionUpdateLiquidityValid, hz, positionUpdateLiquidityBefore, hl]⟩
    · have hv : positionUpdateLiquidityValid a evm := by
        simp only [positionUpdateLiquidityValid, if_pos hz]
        change (0 : Int) < (positionUpdateLiquidityWord a evm).toNat
        exact_mod_cast Nat.pos_of_ne_zero (fun hh ↦ hl (u256_inj hh))
      have r2 := uniswapV3Pool_block_21646_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hclean]; exact hl)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := uniswapV3Pool_block_21710 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      apply Or.inr
      refine ⟨hv, ?_⟩
      simp only [positionUpdateLiquidityNext, if_pos hz, positionUpdateLiquidityBefore_word]
      simp only [uniswapV3Pool_block_21710_stack, hload] at r3
      exact ⟨_, _, _, r3,
        activeWords_expand32 ha1 (show p.toNat + 32 ≤ 2 ^ 200 by omega)⟩
  · have hw : EVM.wordOfInt a.delta ≠ ⟨0⟩ := fun h ↦ hz
      ((wordOfInt_zero_iff_signed a.delta (by omega) (by omega)).mp h)
    have r1 := uniswapV3Pool_block_21637_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [positionUpdateDelta_word a hdlo hdhi]; exact hw)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_21718 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_21718_stack, hload,
      ← positionUpdateLiquidityBefore_word a evm] at r2
    have hl := positionUpdateLiquidityBefore_bounds a evm
    rcases liquidityDeltaCanonicalX (v := v) (positionUpdateLiquidityBefore a evm) a.delta r2
      hl.1 hl.2 hdlo hdhi (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hr, hv⟩ | ⟨hv, k3, C3, r3⟩
    · exact Or.inl ⟨hr, by simpa only [positionUpdateLiquidityValid, if_neg hz] using hv⟩
    · have r4 := uniswapV3Pool_block_21730 (immWords := wordsOf (immStore v)) (by evm_ov) r3
      apply Or.inr
      refine ⟨by simpa only [positionUpdateLiquidityValid, if_neg hz] using hv, ?_⟩
      simp only [positionUpdateLiquidityNext, if_neg hz]
      simp only [uniswapV3Pool_block_21730_stack] at r4
      exact ⟨_, _, _, r4, ha1⟩

end Benchmarks.UniswapV3.Pool
