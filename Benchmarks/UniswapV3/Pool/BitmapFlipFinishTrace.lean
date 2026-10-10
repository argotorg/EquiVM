import Benchmarks.UniswapV3.Pool.BitmapFlipPrefixTrace
import Benchmarks.UniswapV3.Pool.BitmapFlipSource
import Benchmarks.UniswapV3.Pool.BitmapPositionLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def bitmapFlipMemory (mem : ByteArray) (tick spacing : Int) : ByteArray :=
  twoWordHashMem (EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing))) ⟨6⟩ mem

theorem bitmapFlipMaskWord (tick spacing : Int) :
    UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.land (bitmapPositionBitRaw (tick.tdiv spacing)) (UInt256.ofNat 255)) =
      bitmapFlipMask tick spacing :=
  bitmapPositionShift (tick.tdiv spacing)

theorem bitmapFlipFinishRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret spacingRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21341⟩
      (bitmapPositionBitRaw (tick.tdiv spacing) :: EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing)) ::
        ⟨0⟩ :: ⟨0⟩ :: spacingRaw :: EVM.wordOfInt tick :: ⟨6⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hperm : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing)
      (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
      k' C' := by
  have hp : UInt256.signextend (UInt256.ofNat 1)
      (EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing))) =
      EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing)) :=
    bitmapWordPos_clean (tick.tdiv spacing)
  obtain ⟨k', C', rout⟩ := uniswapV3Pool_block_21341 (immWords := wordsOf (immStore v))
    hov hperm hret rd
  simp only [uniswapV3Pool_block_21341_stack, uniswapV3Pool_block_21341_memory, hp] at rout
  change RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing) _ rdata
    (sstoreAccountMap ee.codeOwner σ
      (keccakWord ⟨0⟩ ⟨64⟩ (bitmapFlipMemory mem tick spacing))
      (UInt256.xor (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (bitmapFlipMemory mem tick spacing)) σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1)
          (UInt256.land (bitmapPositionBitRaw (tick.tdiv spacing)) (UInt256.ofNat 255))))) k' C' at rout
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (bitmapFlipMemory mem tick spacing) =
      bitmapSlot (bitmapWordPos (tick.tdiv spacing)) := twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh, bitmapFlipMaskWord] at rout
  exact ⟨k', C', rout⟩


theorem bitmapFlipFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21341⟩
      (bitmapPositionBitRaw (tick.tdiv spacing) :: EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing)) ::
        ⟨0⟩ :: ⟨0⟩ :: EVM.wordOfInt spacing :: EVM.wordOfInt tick :: ⟨6⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hperm : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing)
      aw' rdata (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
      k' C' := by
  obtain ⟨k', C', r'⟩ := bitmapFlipFinishRawX (v := v) tick spacing rd hperm hret hov
  exact ⟨k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool
