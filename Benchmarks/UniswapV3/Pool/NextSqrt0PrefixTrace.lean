import Benchmarks.UniswapV3.Pool.NextSqrt0Model
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_060
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_066
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_067

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0PrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19939⟩
      ((if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    (a.amount.toNat = 0 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (priceRaw :: R) mem aw rdata σ k' C') ∨
    (a.amount.toNat ≠ 0 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (if a.add then ⟨19995⟩ else ⟨20113⟩)
      (nextSqrt0Numerator a :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C') := by
  by_cases hz : a.amount.toNat = 0
  · have hw : a.amount = UInt256.ofNat 0 := uint256_toNat_eq_zero hz
    have r0 := uniswapV3Pool_block_19939_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hw rd
    have r1 := uniswapV3Pool_block_19947 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    have r2 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r1
    exact Or.inl ⟨hz, RD.pack r2⟩
  · have hw : a.amount ≠ UInt256.ofNat 0 := fun h ↦ hz (congrArg UInt256.toNat h)
    have r0 := uniswapV3Pool_block_19939_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hw (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine Or.inr ⟨hz, ?_⟩
    cases ha : a.add
    · simp only [ha, Bool.false_eq_true, if_false] at r0 ⊢
      have r1 := uniswapV3Pool_block_19953_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      simpa only [uniswapV3Pool_block_19953_taken_stack, nextSqrt0NumeratorClean _ a hl]
        using RD.pack r1
    · simp only [ha, if_true] at r0 ⊢
      have r1 := uniswapV3Pool_block_19953_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide) r0
      simpa only [uniswapV3Pool_block_19953_fallthrough_stack, nextSqrt0NumeratorClean _ a hl]
        using RD.pack r1

theorem nextSqrt0ProductX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 (if a.add then ⟨19995⟩ else ⟨20113⟩)
      (nextSqrt0Numerator a :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hn : a.amount.toNat ≠ 0) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if a.add then ⟨20017⟩ else ⟨20136⟩)
      (nextSqrt0Product a :: a.amount :: a.price :: nextSqrt0Product a ::
        nextSqrt0Numerator a :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C' := by
  have hw : a.amount ≠ UInt256.ofNat 0 := fun h ↦ hn (congrArg UInt256.toNat h)
  have hm : UInt256.mul a.price a.amount = nextSqrt0Product a := u256_mul_comm _ _
  cases ha : a.add
  · simp only [ha, Bool.false_eq_true, if_false] at rd ⊢
    have r0 := uniswapV3Pool_block_20113_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hw (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [uniswapV3Pool_block_20113_taken_stack, amountDeltaMask160, hp, hm]
      using RD.pack r0
  · simp only [ha, if_true] at rd ⊢
    have r0 := uniswapV3Pool_block_19995_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hw (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [uniswapV3Pool_block_19995_taken_stack, amountDeltaMask160, hp, hm]
      using RD.pack r0

end Benchmarks.UniswapV3.Pool
