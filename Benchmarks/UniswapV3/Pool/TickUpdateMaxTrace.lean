import Benchmarks.UniswapV3.Pool.TickUpdateLiquidityTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateMaxRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw after unused before slot flipped maximum : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20838⟩
      (after :: unused :: before :: slot :: flipped :: maximum :: R) mem aw rdata σ k C)
    (ha : after.toNat < 2 ^ 128)
    (hov : R.length + 10 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ after.toNat ≤ (uint128Word maximum).toNat) ∨
    (after.toNat ≤ (uint128Word maximum).toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20916⟩
      (after :: before :: slot :: flipped :: maximum :: R) mem aw rdata σ k' C') := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide
  have hca : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) after = after := uint128Word_clean ha
  have hcm : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) maximum =
      uint128Word maximum := rfl
  by_cases hc : after.toNat ≤ (uint128Word maximum).toNat
  · have rf := uniswapV3Pool_block_20838_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hmask, hca, hcm, ugt_zero hc]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    exact Or.inr ⟨hc, _, _, rf⟩
  · have rf := uniswapV3Pool_block_20838_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hmask, hca, hcm, ugt_one (by omega)]; rfl) rd
    exact Or.inl ⟨uniswapV3Pool_block_20867 (immWords := wordsOf (immStore v))
      (by change R.length + 5 + 5 ≤ 1024; omega) rf, hc⟩


theorem tickUpdateMaxX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw after unused before slot flipped maximum : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20838⟩
      (after :: unused :: before :: slot :: flipped :: maximum :: R) mem aw rdata σ k C)
    (ha : after.toNat < 2 ^ 128) (hm : maximum.toNat < 2 ^ 128)
    (hov : R.length + 10 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ after.toNat ≤ maximum.toNat) ∨
    (after.toNat ≤ maximum.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20916⟩
      (after :: before :: slot :: flipped :: maximum :: R) mem aw rdata σ k' C') := by
  have h := tickUpdateMaxRawX (v := v) rd ha hov
  rw [uint128Word_clean hm] at h
  exact h

end Benchmarks.UniswapV3.Pool
