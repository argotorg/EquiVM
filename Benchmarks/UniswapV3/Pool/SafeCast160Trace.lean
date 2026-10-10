import Benchmarks.UniswapV3.Pool.SafeCast160Source
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_074

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem safeCast160X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (y : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨22008⟩ (y :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬safeCast160Valid y) ∨
      (safeCast160Valid y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (y :: R) mem aw rdata σ k' C') := by
  by_cases hy : safeCast160Valid y
  · have he := u256LandMaskCleanOfToNat (bits := 160) y (UInt256.ofNat (2 ^ 160 - 1))
      (by decide) ((safeCast160Valid_iff y).mp hy)
    have r1 := uniswapV3Pool_block_22008_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [amountDeltaMask160, he, u256_eq_refl]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_11243 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r1
    exact Or.inr ⟨hy, _, _, r2⟩
  · have hc : UInt256.eq y (UInt256.land y
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) =
        UInt256.ofNat 0 := by
      rw [amountDeltaMask160]
      apply u256_eq_of_ne
      intro he
      apply hy
      apply (safeCast160Valid_iff y).mpr
      have hb := u256LandMaskToNatLtOfToNat (bits := 160) y (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
      rwa [← he] at hb
    have r1 := uniswapV3Pool_block_22008_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc rd
    exact Or.inl ⟨uniswapV3Pool_block_22026 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r1, hy⟩

end Benchmarks.UniswapV3.Pool
