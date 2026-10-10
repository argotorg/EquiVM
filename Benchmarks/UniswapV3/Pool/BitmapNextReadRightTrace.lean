import Benchmarks.UniswapV3.Pool.BitmapNextReadWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextReadRightX {evm : EVM.State} {g : Sat256} {s0 : EVM.State} {k C : Nat}
    {aw spacingRaw tickRaw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables} (compressed : Int)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11508⟩
      (bitmapPositionBitRaw (bitmapNextPosition compressed false) ::
        EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed false)) ::
        ⟨0⟩ :: ⟨0⟩ :: EVM.wordOfInt compressed :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨0⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: R) mem aw rdata evm.accountMap k C)
    (hov : R.length + 16 ≤ 1024) :
    let masked := bitmapNextMasked evm compressed false
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0
      (if masked = ⟨0⟩ then ⟨11572⟩ else ⟨11590⟩)
      (masked :: bitmapNextMask compressed false ::
        bitmapPositionBitRaw (bitmapNextPosition compressed false) ::
        EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed false)) ::
        EVM.wordOfInt compressed ::
        bitmapNextFlag masked :: ⟨0⟩ :: ⟨0⟩ :: spacingRaw :: tickRaw :: ⟨6⟩ :: R)
      (bitmapNextMemory mem compressed false)
      (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata evm.accountMap k' C' := by
  dsimp only
  have h32 : UInt256.ofNat 32 + UInt256.ofNat 0 = UInt256.ofNat 32 := by decide
  have h64 : UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 := by decide
  have hmem : uniswapV3Pool_block_11508_taken_memory (mem := mem)
      (x1 := EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed false))) (x10 := ⟨6⟩) =
      bitmapNextMemory mem compressed false := by
    simp only [uniswapV3Pool_block_11508_taken_memory, bitmapWordPos_clean, h32]
    rfl
  have hread : UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (bitmapNextMemory mem compressed false)) evm.accountMap evm.executionEnv)
      (bitmapNextMask compressed false) = bitmapNextMasked evm compressed false := by
    change UInt256.land
      (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ (bitmapNextMemory mem compressed false))
        evm.accountMap evm.executionEnv) (bitmapNextMask compressed false) = _
    rw [bitmapNextHash]
    rfl
  dsimp only [solcSlotWordAt] at hread
  dsimp only [uniswapV3Pool_block_11508_taken_memory] at hmem
  simp only [h32] at hmem
  by_cases hz : bitmapNextMasked evm compressed false = ⟨0⟩
  · obtain ⟨k', C', r'⟩ := uniswapV3Pool_block_11508_fallthrough
      (immWords := wordsOf (immStore v)) hov
      (by simp only [h32, h64, bitmapNextRightMaskWord, hmem, hread, hz]; rfl) rd
    simpa only [if_pos hz, h32, h64, uniswapV3Pool_block_11508_fallthrough_stack,
      uniswapV3Pool_block_11508_fallthrough_memory, hmem, hread,
      bitmapNextRightMaskWord, bitmapNextFlag_eq] using RD.pack r'
  · obtain ⟨k', C', r'⟩ := uniswapV3Pool_block_11508_taken
      (immWords := wordsOf (immStore v)) hov
      (by simp only [h32, h64, bitmapNextRightMaskWord, hmem, hread,
        bitmapNextFlag_eq, bitmapNextFlag, if_neg hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [if_neg hz, h32, h64, uniswapV3Pool_block_11508_taken_stack,
      uniswapV3Pool_block_11508_taken_memory, hread,
      bitmapNextRightMaskWord, bitmapNextFlag_eq, hmem] using RD.pack r'

end Benchmarks.UniswapV3.Pool
