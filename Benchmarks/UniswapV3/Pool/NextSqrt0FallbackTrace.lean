import Benchmarks.UniswapV3.Pool.NextSqrt0PrefixTrace
import Benchmarks.UniswapV3.Pool.LowGasSafeAdd
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0FallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20066⟩
      (nextSqrt0Product a :: nextSqrt0Numerator a :: ⟨0⟩ ::
        (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    (¬nextSqrt0FallbackValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextSqrt0FallbackValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (unsafeDivRoundResult (nextSqrt0Numerator a) (nextSqrt0FallbackSum a) :: R)
      mem aw rdata σ k' C') := by
  have hp' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = a.price := by
    rw [u256_land_comm]; exact hp
  by_cases hz : a.price.toNat = 0
  · have hw : a.price = UInt256.ofNat 0 := uint256_toNat_eq_zero hz
    have r0 := uniswapV3Pool_block_20066_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [amountDeltaMask160, hp']; exact hw) rd
    refine Or.inl ⟨fun h ↦ h.1 hz, Or.inr ?_⟩
    exact uniswapV3Pool_block_20091 (immWords := wordsOf (immStore v)) r0
  · have hw : a.price ≠ UInt256.ofNat 0 := fun h ↦ hz (congrArg UInt256.toNat h)
    have r0 := uniswapV3Pool_block_20066_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [amountDeltaMask160, hp']; exact hw)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1 := uniswapV3Pool_block_20092 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    simp only [uniswapV3Pool_block_20092_stack, amountDeltaMask160, hp'] at r1
    rcases safeAddX (v := v) r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hb, hr⟩ | ⟨hv, ka, Ca, _, ra⟩
    · exact Or.inl ⟨fun h ↦ hb h.2, Or.inl hr⟩
    · have r2 := uniswapV3Pool_block_20099 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) ra
      obtain ⟨ku, Cu, ru⟩ := unsafeDivRoundX (v := v) r2
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
      have r3 := uniswapV3Pool_block_20104 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) ru
      have r4 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r3
      exact Or.inr ⟨⟨hz, hv⟩, RD.pack r4⟩

end Benchmarks.UniswapV3.Pool
