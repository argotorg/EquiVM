import Benchmarks.UniswapV3.Pool.NextSqrtModel
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_065
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_066

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt1QuotientPC (a : NextSqrtArgs) : UInt256 :=
  if a.add then if nextSqrt1Small a then ⟨19768⟩ else ⟨19740⟩
  else if nextSqrt1Small a then ⟨19875⟩ else ⟨19847⟩

theorem nextSqrt1SmallWord (a : NextSqrtArgs) :
    UInt256.gt a.amount (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      if nextSqrt1Small a then ⟨0⟩ else ⟨1⟩ := by
  rw [amountDeltaMask160]
  have hmask : (UInt256.ofNat (2 ^ 160 - 1)).toNat = 2 ^ 160 - 1 := by decide
  by_cases h : nextSqrt1Small a
  · rw [if_pos h]
    apply ugt_zero
    rw [hmask]
    change a.amount.toNat < 2 ^ 160 at h
    omega
  · rw [if_neg h]
    apply ugt_one
    rw [hmask]
    change ¬a.amount.toNat < 2 ^ 160 at h
    omega

theorem nextSqrt1PrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19714⟩
      ((if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (nextSqrt1QuotientPC a)
      (⟨0⟩ :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C' := by
  cases ha : a.add
  · simp only [ha, Bool.false_eq_true, if_false] at rd
    have r0 := uniswapV3Pool_block_19714_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    by_cases h : nextSqrt1Small a
    · have r1 := uniswapV3Pool_block_19829_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [nextSqrt1SmallWord, if_pos h]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      simpa only [nextSqrt1QuotientPC, ha, Bool.false_eq_true, if_false, if_pos h,
        uniswapV3Pool_block_19829_taken_stack] using RD.pack r1
    · have r1 := uniswapV3Pool_block_19829_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [nextSqrt1SmallWord, if_neg h]; rfl) r0
      simpa only [nextSqrt1QuotientPC, ha, Bool.false_eq_true, if_false, if_neg h,
        uniswapV3Pool_block_19829_fallthrough_stack] using RD.pack r1
  · simp only [ha, if_true] at rd
    have r0 := uniswapV3Pool_block_19714_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) rd
    by_cases h : nextSqrt1Small a
    · have r1 := uniswapV3Pool_block_19723_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [nextSqrt1SmallWord, if_pos h]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      simpa only [nextSqrt1QuotientPC, ha, if_true, if_pos h,
        uniswapV3Pool_block_19723_taken_stack] using RD.pack r1
    · have r1 := uniswapV3Pool_block_19723_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [nextSqrt1SmallWord, if_neg h]; rfl) r0
      simpa only [nextSqrt1QuotientPC, ha, if_true, if_neg h,
        uniswapV3Pool_block_19723_fallthrough_stack] using RD.pack r1

end Benchmarks.UniswapV3.Pool
