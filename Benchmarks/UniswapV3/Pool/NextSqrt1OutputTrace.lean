import Benchmarks.UniswapV3.Pool.NextSqrt1PrefixTrace
import Benchmarks.UniswapV3.Pool.LowGasSafeAdd
import Benchmarks.UniswapV3.Pool.SafeCast160Trace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt1OutputX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 (if a.add then ⟨19792⟩ else ⟨19898⟩)
      (nextSqrt1Quotient a :: ⟨0⟩ :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) ::
        a.amount :: liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    (¬nextSqrt1OutputValid a ∧ RDrev (deployedRuntime v) g s0) ∨
      (nextSqrt1OutputValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (nextSqrt1Result a :: R) mem aw rdata σ k' C') := by
  have hp' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = a.price := by
    rw [u256_land_comm]; exact hp
  cases ha : a.add
  · simp only [ha, Bool.false_eq_true, if_false] at rd
    by_cases hv : (nextSqrt1Quotient a).toNat < a.price.toNat
    · have r0 := uniswapV3Pool_block_19898_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp', ugt_one hv]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r1 := uniswapV3Pool_block_19921 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      have r2 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r1
      refine Or.inr ⟨by simpa only [nextSqrt1OutputValid, ha, Bool.false_eq_true, if_false]
        using hv, ?_⟩
      simpa only [uniswapV3Pool_block_18117_stack, amountDeltaMask160, hp,
        nextSqrt1Result, ha, Bool.false_eq_true, if_false] using RD.pack r2
    · have r0 := uniswapV3Pool_block_19898_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [amountDeltaMask160, hp']; exact ugt_zero (Nat.le_of_not_gt hv)) rd
      refine Or.inl ⟨?_, uniswapV3Pool_block_19917 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_19898_fallthrough_stack]; evm_ov) r0⟩
      simpa only [nextSqrt1OutputValid, ha, Bool.false_eq_true, if_false] using hv
  · simp only [ha, if_true] at rd
    have r0 := uniswapV3Pool_block_19792 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_19792_stack, amountDeltaMask160, hp] at r0
    rcases safeAddX (v := v) r0
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hbad, hr⟩ | ⟨hadd, ka, Ca, _, ra⟩
    · refine Or.inl ⟨?_, hr⟩
      simp only [nextSqrt1OutputValid, ha, if_true]
      exact fun h ↦ hbad h.1
    · have r1 := uniswapV3Pool_block_19816 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) ra
      rcases safeCast160X (v := v) (a.price + nextSqrt1Quotient a) r1
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
        ⟨hr, hbad⟩ | ⟨hcast, kc, Cc, rc⟩
      · refine Or.inl ⟨?_, hr⟩
        simp only [nextSqrt1OutputValid, ha, if_true]
        exact fun h ↦ hbad h.2
      · have r2 := uniswapV3Pool_block_19821 (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rc
        have r3 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v))
          (by evm_ov) hret r2
        refine Or.inr ⟨?_, ?_⟩
        · simpa only [nextSqrt1OutputValid, ha, if_true] using And.intro hadd hcast
        · simpa only [nextSqrt1Result, ha, if_true] using RD.pack r3

end Benchmarks.UniswapV3.Pool
