import Benchmarks.UniswapV3.Pool.NextSqrt0PrefixTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_068

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0AddChoiceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20017⟩
      (nextSqrt0Product a :: a.amount :: a.price :: nextSqrt0Product a ::
        nextSqrt0Numerator a :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    (¬nextSqrt0Fast a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20066⟩
      (nextSqrt0Product a :: nextSqrt0Numerator a :: R) mem aw rdata σ k' C') ∨
    (nextSqrt0Fast a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20035⟩
      ((nextSqrt0Numerator a + nextSqrt0Product a) :: nextSqrt0Product a ::
        nextSqrt0Numerator a :: R) mem aw rdata σ k' C') := by
  by_cases he : nextSqrt0ProductExact a
  · have heq : UInt256.eq (UInt256.div (nextSqrt0Product a) a.amount) a.price = ⟨1⟩ := by
      rw [show UInt256.div (nextSqrt0Product a) a.amount = a.price from he, uInt256_eq_self]
    have r0 := uniswapV3Pool_block_20017_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [heq]; rfl) rd
    by_cases hadd : (nextSqrt0Numerator a).toNat ≤
        (nextSqrt0Numerator a + nextSqrt0Product a).toNat
    · have r1 := uniswapV3Pool_block_20025_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [u256_add_comm (nextSqrt0Product a), ult_zero hadd]; rfl) r0
      refine Or.inr ⟨⟨he, hadd⟩, ?_⟩
      simpa only [uniswapV3Pool_block_20025_fallthrough_stack,
        u256_add_comm (nextSqrt0Product a)] using RD.pack r1
    · have r1 := uniswapV3Pool_block_20025_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by
          rw [u256_add_comm (nextSqrt0Product a), ult_one (Nat.lt_of_not_ge hadd)]
          decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      have r2 := uniswapV3Pool_block_20064 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      exact Or.inl ⟨fun h ↦ hadd h.2, RD.pack r2⟩
  · have heq : UInt256.eq (UInt256.div (nextSqrt0Product a) a.amount) a.price = ⟨0⟩ :=
      u256_eq_of_ne he
    have r0 := uniswapV3Pool_block_20017_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [heq]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inl ⟨fun h ↦ he h.1, RD.pack r0⟩

theorem nextSqrt0SubtractGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20136⟩
      (nextSqrt0Product a :: a.amount :: a.price :: nextSqrt0Product a ::
        nextSqrt0Numerator a :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    (¬nextSqrt0SubtractGuard a ∧ RDrev (deployedRuntime v) g s0) ∨
    (nextSqrt0SubtractGuard a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20158⟩
      (nextSqrt0Product a :: nextSqrt0Numerator a :: R) mem aw rdata σ k' C') := by
  by_cases he : nextSqrt0ProductExact a
  · have heq : UInt256.eq (UInt256.div (nextSqrt0Product a) a.amount) a.price = ⟨1⟩ := by
      rw [show UInt256.div (nextSqrt0Product a) a.amount = a.price from he, uInt256_eq_self]
    have r0 := uniswapV3Pool_block_20136_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [heq]; rfl) rd
    have r1 := uniswapV3Pool_block_20145 (immWords := wordsOf (immStore v)) (by evm_ov) r0
    by_cases hs : (nextSqrt0Product a).toNat < (nextSqrt0Numerator a).toNat
    · have r2 := uniswapV3Pool_block_20149_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_one hs]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      exact Or.inr ⟨⟨he, hs⟩, RD.pack r2⟩
    · have r2 := uniswapV3Pool_block_20149_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (ugt_zero (Nat.le_of_not_gt hs)) r1
      refine Or.inl ⟨fun h ↦ hs h.2, ?_⟩
      exact uniswapV3Pool_block_20154 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_20149_fallthrough_stack]; evm_ov) r2
  · have heq : UInt256.eq (UInt256.div (nextSqrt0Product a) a.amount) a.price = ⟨0⟩ :=
      u256_eq_of_ne he
    have r0 := uniswapV3Pool_block_20136_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [heq]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1 := uniswapV3Pool_block_20149_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) heq r0
    refine Or.inl ⟨fun h ↦ he h.1, ?_⟩
    exact uniswapV3Pool_block_20154 (immWords := wordsOf (immStore v))
      (by simp only [uniswapV3Pool_block_20149_fallthrough_stack]; evm_ov) r1

end Benchmarks.UniswapV3.Pool
