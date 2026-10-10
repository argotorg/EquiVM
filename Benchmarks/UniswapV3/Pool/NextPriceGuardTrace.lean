import Benchmarks.UniswapV3.Pool.NextPriceModel
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextPriceEntry (input : Bool) : UInt256 := if input then ⟨18314⟩ else ⟨18390⟩

def nextPriceLiquidityPC (input : Bool) : UInt256 := if input then ⟨18337⟩ else ⟨18413⟩

def nextPriceDirectionPC (input : Bool) : UInt256 := if input then ⟨18359⟩ else ⟨18435⟩

theorem nextPricePriceGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceEntry input)
      ((if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw ::
        priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hov : R.length + 11 ≤ 1024) :
    (¬0 < a.price.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (0 < a.price.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (nextPriceLiquidityPC input)
      (⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C') := by
  have hp' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = a.price := by
    rw [u256_land_comm]; exact hp
  by_cases hz : 0 < a.price.toNat
  · have hgt : UInt256.gt a.price (UInt256.ofNat 0) = ⟨1⟩ := ugt_one hz
    refine Or.inr ⟨hz, ?_⟩
    cases input
    · exact RD.pack (uniswapV3Pool_block_18390_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp', hgt]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd)
    · exact RD.pack (uniswapV3Pool_block_18314_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp', hgt]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd)
  · refine Or.inl ⟨hz, ?_⟩
    cases input
    · have r0 := uniswapV3Pool_block_18390_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp']; exact ugt_zero (Nat.le_of_not_gt hz)) rd
      exact uniswapV3Pool_block_18409 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_18390_fallthrough_stack]; evm_ov) r0
    · have r0 := uniswapV3Pool_block_18314_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp']; exact ugt_zero (Nat.le_of_not_gt hz)) rd
      exact uniswapV3Pool_block_18333 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_18314_fallthrough_stack]; evm_ov) r0

theorem nextPriceLiquidityGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceLiquidityPC input)
      (⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hov : R.length + 11 ≤ 1024) :
    (¬0 < a.liquidity.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (0 < a.liquidity.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (nextPriceDirectionPC input)
      (⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C') := by
  have hl' : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) liquidityRaw = a.liquidity := by
    rw [u256_land_comm]; exact hl
  by_cases hz : 0 < a.liquidity.toNat
  · have hgt : UInt256.gt a.liquidity (UInt256.ofNat 0) = ⟨1⟩ := ugt_one hz
    refine Or.inr ⟨hz, ?_⟩
    cases input
    · exact RD.pack (uniswapV3Pool_block_18413_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hl', hgt]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd)
    · exact RD.pack (uniswapV3Pool_block_18337_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hl', hgt]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd)
  · refine Or.inl ⟨hz, ?_⟩
    cases input
    · have r0 := uniswapV3Pool_block_18413_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hl']; exact ugt_zero (Nat.le_of_not_gt hz)) rd
      exact uniswapV3Pool_block_18431 (immWords := wordsOf (immStore v)) (by evm_ov) r0
    · have r0 := uniswapV3Pool_block_18337_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hl']; exact ugt_zero (Nat.le_of_not_gt hz)) rd
      exact uniswapV3Pool_block_18355 (immWords := wordsOf (immStore v)) (by evm_ov) r0

theorem nextPriceGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceEntry input)
      ((if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw ::
        priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hov : R.length + 11 ≤ 1024) :
    (¬nextPriceGuard a ∧ RDrev (deployedRuntime v) g s0) ∨
    (nextPriceGuard a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 (nextPriceDirectionPC input)
      (⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C') := by
  rcases nextPricePriceGuardX (v := v) input a rd hp hov with ⟨hb, hr⟩ | ⟨hp, kp, Cp, rp⟩
  · exact Or.inl ⟨fun h ↦ hb h.1, hr⟩
  · rcases nextPriceLiquidityGuardX (v := v) input a rp hl hov with ⟨hb, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨fun h ↦ hb h.2, hr⟩
    · exact Or.inr ⟨⟨hp, hl⟩, hr⟩

end Benchmarks.UniswapV3.Pool
