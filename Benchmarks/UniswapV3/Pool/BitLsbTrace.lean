import Benchmarks.UniswapV3.Pool.BitLsbSource
import Benchmarks.UniswapV3.Pool.BitLsbFoldTrace
import Benchmarks.UniswapV3.Pool.BitLsbEndsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitLsbX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨17768⟩ (x :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    (¬0 < x.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
      (0 < x.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (UInt256.ofNat (bitLsbCount x) :: R) mem aw rdata σ k' C') := by
  by_cases hx : 0 < x.toNat
  · have r0 := uniswapV3Pool_block_17768_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [ugt_one (a := x) (b := UInt256.ofNat 0) hx]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨k1, C1, r1⟩ := bitLsbFirstX (v := v) x r0 (by evm_ov)
    have hb := bitLsbStep_bounds (255, x) 128
    obtain ⟨k2, C2, r2⟩ := bitLsbFoldX (v := v) (bitLsbStep (255, x) 128) 0 6 (by decide)
      (by omega) (by change 126 ≤ (bitLsbStep (255, x) 128).1; omega) r1 (by evm_ov)
    have rp : RD (deployedRuntime v) ee g s0 ⟨17984⟩
        (UInt256.ofNat (bitLsbPrefix x).1 :: (bitLsbPrefix x).2 :: ret :: R)
          mem aw rdata σ k2 C2 := by
      simpa only [bitLsbRun_prefix] using r2
    exact Or.inr ⟨hx, bitLsbLastX (bitLsbPrefix x)
      (bitLsbPrefix_bounds x).2 (bitLsbPrefix_bounds x).1 rp hret (by omega)⟩
  · have r0 := uniswapV3Pool_block_17768_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (ugt_zero (a := x) (b := UInt256.ofNat 0) (by change x.toNat ≤ 0; omega)) rd
    exact Or.inl ⟨hx, uniswapV3Pool_block_17778 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r0⟩

end Benchmarks.UniswapV3.Pool
