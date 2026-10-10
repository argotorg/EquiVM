import Benchmarks.UniswapV3.Pool.NextPriceGuardTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextPriceCalleePC (input : Bool) (a : NextPriceArgs) : UInt256 :=
  if nextPriceOne input a then ⟨19714⟩ else ⟨19939⟩

def nextPriceReturnPC (a : NextPriceArgs) : UInt256 :=
  if a.zeroForOne then ⟨18114⟩ else ⟨18074⟩

theorem nextPriceDirectionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceDirectionPC input)
      (⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (nextPriceCalleePC input a)
      ((if input then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw ::
        nextPriceReturnPC a :: ⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) ::
        a.amount :: liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C' := by
  cases input <;> cases hz : a.zeroForOne
  · simp only [nextPriceDirectionPC, hz, Bool.false_eq_true, if_false] at rd
    have r0 := uniswapV3Pool_block_18435_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r1 := uniswapV3Pool_block_18441 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    simpa only [nextPriceCalleePC, nextPriceOne, nextPriceReturnPC, hz,
      Bool.false_eq_true, if_false] using RD.pack r1
  · simp only [nextPriceDirectionPC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have r0 := uniswapV3Pool_block_18435_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1 := uniswapV3Pool_block_18453 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    simpa only [nextPriceCalleePC, nextPriceOne, nextPriceReturnPC, hz,
      Bool.false_eq_true, if_false, if_true] using RD.pack r1
  · simp only [nextPriceDirectionPC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have r0 := uniswapV3Pool_block_18359_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r1 := uniswapV3Pool_block_18365 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    simpa only [nextPriceCalleePC, nextPriceOne, nextPriceReturnPC, hz, Bool.not_false,
      Bool.false_eq_true, if_false, if_true] using RD.pack r1
  · simp only [nextPriceDirectionPC, hz, if_true] at rd
    have r0 := uniswapV3Pool_block_18359_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1 := uniswapV3Pool_block_18377 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    simpa only [nextPriceCalleePC, nextPriceOne, nextPriceReturnPC, hz, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] using RD.pack r1

theorem nextPriceReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw result : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceReturnPC a)
      (result :: ⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (result :: R) mem aw rdata σ k' C' := by
  have hr : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨18114⟩
      (result :: ⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C' := by
    cases hz : a.zeroForOne
    · simp only [nextPriceReturnPC, hz, Bool.false_eq_true, if_false] at rd ⊢
      exact RD.pack (uniswapV3Pool_block_18074 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd)
    · simpa only [nextPriceReturnPC, hz, if_true] using RD.pack rd
  obtain ⟨kr, Cr, rr⟩ := hr
  have r0 := uniswapV3Pool_block_18114 (immWords := wordsOf (immStore v)) (by evm_ov) rr
  exact RD.pack (uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r0)

end Benchmarks.UniswapV3.Pool
