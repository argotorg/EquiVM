import Benchmarks.UniswapV3.Pool.BitmapNextResultWords
import Benchmarks.UniswapV3.Pool.BitLsbTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_035
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextResultRightX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret spacingRaw tickRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (compressed : Int) (masked : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 (if masked = ⟨0⟩ then ⟨11572⟩ else ⟨11590⟩)
      (masked :: bitmapNextMask compressed false ::
        bitmapPositionBitRaw (bitmapNextPosition compressed false) ::
        EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed false)) ::
        EVM.wordOfInt compressed ::
        bitmapNextFlag masked :: ⟨0⟩ :: ⟨0⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (bitmapNextFlag masked :: bitmapNextResultRaw compressed spacingRaw false masked :: R)
      mem aw rdata σ k' C' := by
  have hmiddle : ∃ km Cm, RD (deployedRuntime v) ee g s0 ⟨11612⟩
      (bitmapNextResultRaw compressed spacingRaw false masked :: masked ::
        bitmapNextMask compressed false ::
        bitmapPositionBitRaw (bitmapNextPosition compressed false) ::
        EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed false)) ::
        EVM.wordOfInt compressed ::
        bitmapNextFlag masked :: ⟨0⟩ :: ⟨0⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata σ km Cm := by
    by_cases hz : masked = ⟨0⟩
    · rw [if_pos hz] at rd
      have r1 := uniswapV3Pool_block_11572 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_11572_stack, bitmapNextResultRaw,
        bitmapNextDistanceRaw, bitmapNextPosition, Bool.false_eq_true, if_false, if_pos hz]
        using RD.pack r1
    · rw [if_neg hz] at rd
      have hp : 0 < masked.toNat := by
        by_contra hn
        exact hz (uint256_toNat_eq_zero (by omega))
      have r1 := uniswapV3Pool_block_11590 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      rcases bitLsbX (v := v) masked r1
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
        ⟨hn, _⟩ | ⟨_, km, Cm, rm⟩
      · exact (hn hp).elim
      · have r2 := uniswapV3Pool_block_11601 (immWords := wordsOf (immStore v)) (by evm_ov) rm
        simpa only [uniswapV3Pool_block_11601_stack, bitmapNextResultRaw,
          bitmapNextDistanceRaw, bitmapNextPosition, Bool.false_eq_true, if_false, if_neg hz]
          using RD.pack r2
  obtain ⟨km, Cm, rm⟩ := hmiddle
  have r3 := uniswapV3Pool_block_11612 (immWords := wordsOf (immStore v))
    (by evm_ov) rm
  have r4 := uniswapV3Pool_block_11619 (immWords := wordsOf (immStore v)) (by evm_ov) hret r3
  exact RD.pack r4

end Benchmarks.UniswapV3.Pool
