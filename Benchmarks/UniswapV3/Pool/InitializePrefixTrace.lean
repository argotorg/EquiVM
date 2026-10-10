import Benchmarks.UniswapV3.Pool.TickLogTrace
import Benchmarks.UniswapV3.Pool.BlockTimestamp
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem initializeGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨10715⟩ (price :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 0 20 σ ee ≠ ⟨0⟩) ∨
      (slot0FieldWord 0 20 σ ee = ⟨0⟩ ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨10782⟩
        (price :: R) mem aw rdata σ k' C') := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  have hfield : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (solcSlotWordAt ⟨0⟩ σ ee) =
      slot0FieldWord 0 20 σ ee := by
    unfold slot0FieldWord
    change UInt256.land _ _ = UInt256.land (UInt256.div _ ⟨1⟩) _
    rw [word_div_one, u256_land_comm]
    congr 1 <;> decide
  by_cases hz : slot0FieldWord 0 20 σ ee = ⟨0⟩
  · obtain ⟨k', C', out⟩ := uniswapV3Pool_block_10715_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by
        rw [hmask]
        change UInt256.isZero
          (UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (solcSlotWordAt ⟨0⟩ σ ee)) ≠ _
        rw [hfield, hz]
        decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inr ⟨hz, k', C', out⟩
  · obtain ⟨k', C', rbad⟩ := uniswapV3Pool_block_10715_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by
        rw [hmask]
        change UInt256.isZero
          (UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (solcSlotWordAt ⟨0⟩ σ ee)) = _
        rw [hfield]
        exact isZero_eq_zero_of_ne hz) rd
    exact Or.inl ⟨uniswapV3Pool_block_10733 (immWords := wordsOf (immStore v)) (by evm_ov) rbad, hz⟩

theorem initializeBeforeOracleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨10782⟩ (price :: R) mem aw rdata σ k C)
    (hp : price.toNat < 2 ^ 160) (hov : R.length + 24 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ (tickLogValid price ∧ tickLogSafe (tickLogResult price))) ∨
      (tickLogValid price ∧ tickLogSafe (tickLogResult price) ∧ ∃ k' C',
        RD (deployedRuntime v) ee g s0 ⟨17514⟩
          (UInt256.ofNat ee.header.timestamp :: ⟨8⟩ :: ⟨10817⟩ :: ⟨0⟩ :: ⟨0⟩ ::
            tickLogChoiceRaw (tickLogResult price) price :: price :: R) mem aw rdata σ k' C') := by
  have hprice : tickLogPrice price = price :=
    u256LandMaskCleanOfToNat _ _ (by decide) hp
  have rcall := uniswapV3Pool_block_10782 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_10782_stack] at rcall
  rcases tickLogX (v := v) rcall
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by simp only [List.length_cons]; omega) with ⟨rrev, hv⟩ | ⟨hv, hs, k', C', rdone⟩
  · exact Or.inl ⟨rrev, by simpa only [hprice] using hv⟩
  rw [hprice] at hv hs rdone
  have rtcall := uniswapV3Pool_block_10793 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdone
  simp only [uniswapV3Pool_block_10793_stack] at rtcall
  obtain ⟨k'', C'', rtime⟩ := blockTimestampX (v := v) rtcall
    (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rout := uniswapV3Pool_block_10809 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rtime
  exact Or.inr ⟨hv, hs, _, _, rout⟩

end Benchmarks.UniswapV3.Pool
