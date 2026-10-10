import Benchmarks.UniswapV3.Pool.BitMsbSource
import Benchmarks.UniswapV3.Pool.BitMsbFoldTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitMsbLastX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17752⟩
      (UInt256.ofNat state.1 :: state.2 :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (tickLogMsbStep state 1).1 :: R) mem aw rdata σ k' C' := by
  by_cases h : 2 ^ 1 ≤ state.2.toNat
  · have hc : UInt256.lt state.2 (UInt256.ofNat 2) = ⟨0⟩ := ult_zero h
    have r1 := uniswapV3Pool_block_17752_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc rd
    have r2 := uniswapV3Pool_block_17761 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    simpa only [tickLogMsbStep, if_pos h, uniswapV3Pool_block_17761_stack,
      wordNat_add, Nat.add_comm] using RD.pack r2
  · have hc : UInt256.lt state.2 (UInt256.ofNat 2) ≠ ⟨0⟩ := by
      rw [ult_one (by change state.2.toNat < 2; omega)]
      decide
    have r1 := uniswapV3Pool_block_17752_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_11243 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    simpa only [tickLogMsbStep, if_neg h] using RD.pack r2

theorem bitMsbX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17608⟩ (x :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    (¬0 < x.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
      (0 < x.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (UInt256.ofNat (tickLogMsbCount x) :: R) mem aw rdata σ k' C') := by
  by_cases hx : 0 < x.toNat
  · have r0 := uniswapV3Pool_block_17608_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [ugt_one (a := x) (b := UInt256.ofNat 0) hx]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨k1, C1, r1⟩ := bitMsbFoldX (v := v) (R := ret :: R) (0, x) 0 7 (by decide) r0
      (by simpa only [List.length_cons] using hov)
    have rp : RD (deployedRuntime v) ee g s0 ⟨17752⟩
        (UInt256.ofNat (bitMsbPrefix x).1 :: (bitMsbPrefix x).2 :: ret :: R)
          mem aw rdata σ k1 C1 := by
      simpa only [bitMsbRun_prefix] using r1
    have hf := bitMsbLastX (bitMsbPrefix x) rp hret hov
    exact Or.inr ⟨hx, by simpa only [bitMsbPrefix_result] using hf⟩
  · have r0 := uniswapV3Pool_block_17608_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (ugt_zero (a := x) (b := UInt256.ofNat 0) (by change x.toNat ≤ 0; omega)) rd
    exact Or.inl ⟨hx, uniswapV3Pool_block_17618 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r0⟩

end Benchmarks.UniswapV3.Pool
