import Benchmarks.UniswapV3.Pool.BitmapNextReadWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextReadLeftX {evm : EVM.State} {g : Sat256} {s0 : EVM.State} {k C : Nat}
    {aw spacingRaw tickRaw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables} (compressed : Int)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11394⟩
      (bitmapPositionBitRaw compressed :: EVM.wordOfInt (bitmapWordPos compressed) ::
        ⟨0⟩ :: ⟨0⟩ :: EVM.wordOfInt compressed :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨1⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: R) mem aw rdata evm.accountMap k C)
    (hov : R.length + 15 ≤ 1024) :
    let masked := bitmapNextMasked evm compressed true
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0
      (if masked = ⟨0⟩ then ⟨11451⟩ else ⟨11463⟩)
      (masked :: bitmapNextMask compressed true :: bitmapPositionBitRaw compressed ::
        EVM.wordOfInt (bitmapWordPos compressed) :: EVM.wordOfInt compressed ::
        bitmapNextFlag masked :: ⟨0⟩ :: ⟨1⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: R)
      (bitmapNextMemory mem compressed true)
      (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata evm.accountMap k' C' := by
  dsimp only
  have hmem : uniswapV3Pool_block_11394_taken_memory (mem := mem)
      (x1 := EVM.wordOfInt (bitmapWordPos compressed)) (x10 := ⟨6⟩) =
      bitmapNextMemory mem compressed true := by
    simp only [uniswapV3Pool_block_11394_taken_memory, bitmapWordPos_clean]
    rfl
  have hread : UInt256.land (bitmapNextMask compressed true)
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (bitmapNextMemory mem compressed true))
        evm.accountMap evm.executionEnv) = bitmapNextMasked evm compressed true := by
    change UInt256.land (bitmapNextMask compressed true)
      (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ (bitmapNextMemory mem compressed true))
        evm.accountMap evm.executionEnv) = _
    rw [bitmapNextHash]
    exact u256_land_comm _ _
  dsimp only [solcSlotWordAt] at hread
  dsimp only [uniswapV3Pool_block_11394_taken_memory] at hmem
  by_cases hz : bitmapNextMasked evm compressed true = ⟨0⟩
  · obtain ⟨k', C', r'⟩ := uniswapV3Pool_block_11394_fallthrough
      (immWords := wordsOf (immStore v)) hov
      (by simp only [bitmapNextLeftMaskWord, hmem, hread, hz]; rfl) rd
    simpa only [if_pos hz, uniswapV3Pool_block_11394_fallthrough_stack,
      uniswapV3Pool_block_11394_fallthrough_memory, hmem, hread,
      bitmapNextLeftMaskWord, bitmapNextFlag_isZero] using RD.pack r'
  · obtain ⟨k', C', r'⟩ := uniswapV3Pool_block_11394_taken
      (immWords := wordsOf (immStore v)) hov
      (by simp only [bitmapNextLeftMaskWord, hmem, hread, isZero_eq_zero_of_ne hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [if_neg hz, uniswapV3Pool_block_11394_taken_stack,
      uniswapV3Pool_block_11394_taken_memory, hread,
      bitmapNextLeftMaskWord, bitmapNextFlag_isZero, hmem] using RD.pack r'

end Benchmarks.UniswapV3.Pool
