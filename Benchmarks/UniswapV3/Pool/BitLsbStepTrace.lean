import Benchmarks.UniswapV3.Pool.BitLsbModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_058
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitLsbPC : Nat → UInt256
  | 0 => ⟨17817⟩
  | 1 => ⟨17850⟩
  | 2 => ⟨17879⟩
  | 3 => ⟨17906⟩
  | 4 => ⟨17932⟩
  | 5 => ⟨17958⟩
  | _ => ⟨17984⟩

theorem bitLsbStepX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (i : Fin 6) (hb : state.1 < 256) (hle : 2 ^ (6 - i.val) ≤ state.1)
    (rd : RD (deployedRuntime v) ee g s0 (bitLsbPC i.val)
      (UInt256.ofNat state.1 :: state.2 :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (bitLsbPC (i.val + 1))
      (UInt256.ofNat (bitLsbStep state (2 ^ (6 - i.val))).1 ::
        (bitLsbStep state (2 ^ (6 - i.val))).2 :: R) mem aw rdata σ k' C' := by
  by_cases h : 0 < (bitLsbLow state.2 (2 ^ (6 - i.val))).toNat
  · have hc : UInt256.isZero (bitLsbLow state.2 (2 ^ (6 - i.val))) = ⟨0⟩ := by
      apply isZero_eq_zero_of_ne
      intro hz
      rw [hz] at h
      exact Nat.not_lt_zero _ h
    have hd := wordLnot_add_nat (show 0 < 2 ^ (6 - i.val) by positivity) hle
      (lt_trans hb (by decide))
    rcases i with ⟨i, hi⟩
    interval_cases i
    all_goals simp only [Fin.val_mk, Nat.reduceSub, Nat.reducePow] at hd
    · have r1 := uniswapV3Pool_block_17817_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17834 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17834_stack, hd] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17850_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17863 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17863_stack, hd] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17879_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17890 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17890_stack, hd] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17906_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17916 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17916_stack, hd] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17932_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17942 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17942_stack, hd] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17958_fallthrough
        (immWords := wordsOf (immStore v)) hov hc rd
      have r2 := uniswapV3Pool_block_17968 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [bitLsbPC, bitLsbStep, if_pos h,
        uniswapV3Pool_block_17968_stack, hd] using RD.pack r2
  · have hz : bitLsbLow state.2 (2 ^ (6 - i.val)) = ⟨0⟩ :=
      uint256_toNat_eq_zero (by omega)
    have hc : UInt256.isZero (bitLsbLow state.2 (2 ^ (6 - i.val))) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    rcases i with ⟨i, hi⟩
    interval_cases i
    · have r1 := uniswapV3Pool_block_17817_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17842 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17842_stack] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17850_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17871 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17871_stack] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17879_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17898 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17898_stack] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17906_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17924 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17924_stack] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17932_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17950 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17950_stack] using RD.pack r2
    · have r1 := uniswapV3Pool_block_17958_taken
        (immWords := wordsOf (immStore v)) hov hc
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_17976 (immWords := wordsOf (immStore v)) hov r1
      simpa only [bitLsbPC, bitLsbStep, if_neg h,
        uniswapV3Pool_block_17976_stack] using RD.pack r2

end Benchmarks.UniswapV3.Pool
