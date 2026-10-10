import Benchmarks.UniswapV3.Pool.TickLogPrefix
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogPrice (price : UInt256) : UInt256 :=
  UInt256.land price (UInt256.ofNat (2 ^ 160 - 1))

theorem tickLogPrice_lt (price : UInt256) : (tickLogPrice price).toNat < 2 ^ 160 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem tickLogStartX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13989⟩ (price :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ tickLogValid (tickLogPrice price)) ∨
      (tickLogValid (tickLogPrice price) ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14102⟩
        (⟨0⟩ :: price :: R) mem aw rdata σ k' C') := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  have hprice : UInt256.land price (UInt256.ofNat (2 ^ 160 - 1)) = tickLogPrice price := rfl
  have hfail {k' C' : Nat}
      (r : RD (deployedRuntime v) ee g s0 ⟨14049⟩
        (⟨0⟩ :: ⟨0⟩ :: price :: R) mem aw rdata σ k' C') :
      RDrev (deployedRuntime v) g s0 := by
    have rf := uniswapV3Pool_block_14049_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl r
    exact uniswapV3Pool_block_14054 (immWords := wordsOf (immStore v))
      (by simp only [uniswapV3Pool_block_14049_fallthrough_stack, List.length_cons]; omega) rf
  by_cases hlo : 4295128739 ≤ (tickLogPrice price).toNat
  · have hlt : UInt256.lt (tickLogPrice price) (UInt256.ofNat 4295128739) = ⟨0⟩ :=
      ult_zero hlo
    have rlo := uniswapV3Pool_block_13989_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask]; exact hlt) rd
    have rhi := uniswapV3Pool_block_14016 (immWords := wordsOf (immStore v))
      (by evm_ov) rlo
    by_cases hhi : (tickLogPrice price).toNat < 1461446703485210103287273052203988822378723970342
    · have hlt' : UInt256.lt (tickLogPrice price)
          (UInt256.ofNat 1461446703485210103287273052203988822378723970342) = ⟨1⟩ :=
        ult_one hhi
      have rguard : RD (deployedRuntime v) ee g s0 ⟨14049⟩
          (⟨1⟩ :: ⟨0⟩ :: price :: R) mem aw rdata σ (k + 16 + 10) (C + 53 + 29) := by
        simpa only [uniswapV3Pool_block_14016_stack,
          uniswapV3Pool_block_13989_fallthrough_stack, hmask, hprice, hlt'] using rhi
      have rout := uniswapV3Pool_block_14049_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rguard
      exact Or.inr ⟨⟨hlo, hhi⟩, _, _, rout⟩
    · have hlt' : UInt256.lt (tickLogPrice price)
          (UInt256.ofNat 1461446703485210103287273052203988822378723970342) = ⟨0⟩ :=
        ult_zero (Nat.le_of_not_gt hhi)
      have rguard : RD (deployedRuntime v) ee g s0 ⟨14049⟩
          (⟨0⟩ :: ⟨0⟩ :: price :: R) mem aw rdata σ (k + 16 + 10) (C + 53 + 29) := by
        simpa only [uniswapV3Pool_block_14016_stack,
          uniswapV3Pool_block_13989_fallthrough_stack, hmask, hprice, hlt'] using rhi
      exact Or.inl ⟨hfail rguard, fun hv ↦ hhi hv.2⟩
  · have hlt : UInt256.lt (tickLogPrice price) (UInt256.ofNat 4295128739) = ⟨1⟩ :=
      ult_one (Nat.lt_of_not_ge hlo)
    have rlo := uniswapV3Pool_block_13989_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hmask]; change UInt256.lt (tickLogPrice price) _ ≠ _; rw [hlt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rguard : RD (deployedRuntime v) ee g s0 ⟨14049⟩
        (⟨0⟩ :: ⟨0⟩ :: price :: R) mem aw rdata σ (k + 16) (C + 53) := by
      simpa only [uniswapV3Pool_block_13989_taken_stack, hmask, hprice, hlt,
        show UInt256.isZero ⟨1⟩ = ⟨0⟩ from rfl] using rlo
    exact Or.inl ⟨hfail rguard, fun hv ↦ hlo hv.1⟩

end Benchmarks.UniswapV3.Pool
