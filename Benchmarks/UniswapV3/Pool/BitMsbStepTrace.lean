import Benchmarks.UniswapV3.Pool.BitScanBounds
import Benchmarks.UniswapV3.Pool.ObserveEncodeArithmetic
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_056
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitMsbPC : Nat → UInt256
  | 0 => ⟨17622⟩
  | 1 => ⟨17641⟩
  | 2 => ⟨17665⟩
  | 3 => ⟨17685⟩
  | 4 => ⟨17703⟩
  | 5 => ⟨17720⟩
  | 6 => ⟨17736⟩
  | _ => ⟨17752⟩

theorem bitMsbStepX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (i : Fin 7)
    (rd : RD (deployedRuntime v) ee g s0 (bitMsbPC i.val)
      (UInt256.ofNat state.1 :: state.2 :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (bitMsbPC (i.val + 1))
      (UInt256.ofNat (tickLogMsbStep state (2 ^ (7 - i.val))).1 ::
        (tickLogMsbStep state (2 ^ (7 - i.val))).2 :: R) mem aw rdata σ k' C' := by
  have hb : 2 ^ (7 - i.val) < 256 := by
    change 2 ^ (7 - i.val) < 2 ^ 8
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hpow : (UInt256.ofNat (2 ^ (2 ^ (7 - i.val)))).toNat = 2 ^ (2 ^ (7 - i.val)) :=
    UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hb)
  have h128 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
      UInt256.ofNat (2 ^ 128) := by decide
  by_cases h : 2 ^ (2 ^ (7 - i.val)) ≤ state.2.toNat
  · have hc : UInt256.lt state.2 (UInt256.ofNat (2 ^ (2 ^ (7 - i.val)))) = ⟨0⟩ :=
      ult_zero (by rw [hpow]; exact h)
    rcases i with ⟨i, hi⟩
    interval_cases i
    · have r1 := uniswapV3Pool_block_17622_fallthrough
        (immWords := wordsOf (immStore v)) hov
        (by simpa only [h128] using hc) rd
      have r2 := uniswapV3Pool_block_17634 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17634_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17641_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17658 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17658_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17665_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17678 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17678_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17685_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17696 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17696_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17703_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17713 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17713_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17720_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17729 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17729_stack, wordNat_add, Nat.add_comm] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17736_fallthrough
        (immWords := wordsOf (immStore v)) hov
        hc rd
      have r2 := uniswapV3Pool_block_17745 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitMsbPC, tickLogMsbStep, if_pos h,
        uniswapV3Pool_block_17745_stack, wordNat_add, Nat.add_comm] using RD.pack r2
  · have hc : UInt256.lt state.2 (UInt256.ofNat (2 ^ (2 ^ (7 - i.val)))) ≠ ⟨0⟩ := by
      rw [ult_one (by rw [hpow]; omega)]
      decide
    rcases i with ⟨i, hi⟩
    interval_cases i
    · have r1 := uniswapV3Pool_block_17622_taken
        (immWords := wordsOf (immStore v)) hov
        (by simpa only [h128] using hc)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17641_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17665_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17685_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17703_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17720_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1
    · have r1 := uniswapV3Pool_block_17736_taken
        (immWords := wordsOf (immStore v)) hov
        hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [bitMsbPC, tickLogMsbStep, if_neg h] using RD.pack r1

end Benchmarks.UniswapV3.Pool
