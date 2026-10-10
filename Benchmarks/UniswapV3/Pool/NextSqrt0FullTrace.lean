import Benchmarks.UniswapV3.Pool.NextSqrt0PrefixTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_068
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace
import Benchmarks.UniswapV3.Pool.SafeCast160Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0FullReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw result denominator : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20054⟩
      (result :: denominator :: nextSqrt0Product a :: nextSqrt0Numerator a :: ⟨0⟩ ::
        (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (result :: R) mem aw rdata σ k' C' := by
  have r0 := uniswapV3Pool_block_20054 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  exact RD.pack (uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r0)

theorem nextSqrt0FastFullX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20035⟩
      ((nextSqrt0Numerator a + nextSqrt0Product a) :: nextSqrt0Product a ::
        nextSqrt0Numerator a :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (ha : a.add = true)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    (¬nextSqrt0FullValid a ∧ RDrev (deployedRuntime v) g s0) ∨
    (nextSqrt0FullValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (nextSqrt0FullResult a :: R) mem aw rdata σ k' C') := by
  have hp' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = a.price := by
    rw [u256_land_comm]; exact hp
  have r0 := uniswapV3Pool_block_20035 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_20035_stack, amountDeltaMask160, hp'] at r0
  rcases fullMathRoundX (v := v) r0
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
    ⟨hb, hr⟩ | ⟨hv, kr, Cr, _, rr⟩
  · exact Or.inl ⟨by simpa only [nextSqrt0FullValid, nextSqrt0Denominator, ha, if_true]
      using hb, hr⟩
  · refine Or.inr ⟨by simpa only [nextSqrt0FullValid, nextSqrt0Denominator, ha, if_true]
      using hv, ?_⟩
    have hr := nextSqrt0FullReturnX (v := v) a rr hret (by omega)
    simpa only [nextSqrt0FullResult, nextSqrt0Denominator, ha, if_true] using hr

theorem nextSqrt0SubtractFullX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20158⟩
      (nextSqrt0Product a :: nextSqrt0Numerator a :: ⟨0⟩ ::
        (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (ha : a.add = false)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 31 ≤ 1024) :
    (¬(nextSqrt0FullValid a ∧ safeCast160Valid (nextSqrt0FullResult a)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (nextSqrt0FullValid a ∧ safeCast160Valid (nextSqrt0FullResult a) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (nextSqrt0FullResult a :: R) mem aw rdata σ k' C') := by
  have hd : UInt256.sub (nextSqrt0Numerator a) (nextSqrt0Product a) =
      nextSqrt0Denominator a := by
    simp only [nextSqrt0Denominator, ha, Bool.false_eq_true, if_false]
  have r0 := uniswapV3Pool_block_20158 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_20158_stack, amountDeltaMask160, hp, hd] at r0
  rcases fullMathRoundX (v := v) r0
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
    ⟨hb, hr⟩ | ⟨hv, kr, Cr, _, rr⟩
  · exact Or.inl ⟨fun h ↦ hb h.1, hr⟩
  · have r1 := uniswapV3Pool_block_19816 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    rcases safeCast160X (v := v) (nextSqrt0FullResult a) r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hr, hb⟩ | ⟨hc, kc, Cc, rc⟩
    · exact Or.inl ⟨fun h ↦ hb h.2, hr⟩
    · exact Or.inr ⟨hv, hc, nextSqrt0FullReturnX (v := v) a rc hret (by omega)⟩

end Benchmarks.UniswapV3.Pool
