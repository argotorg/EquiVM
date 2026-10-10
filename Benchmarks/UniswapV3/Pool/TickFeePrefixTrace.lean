import Benchmarks.UniswapV3.Pool.TickFeeModel
import Benchmarks.UniswapV3.Pool.MappingScratchMemory
import Benchmarks.UniswapV3.Pool.SignedComparison
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_072

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickFeeMemory (mem : ByteArray) (a : TickFeeArgs) : ByteArray :=
  wordAt0Mem (EVM.wordOfInt a.upper) (twoWordHashMem (EVM.wordOfInt a.lower) ⟨5⟩ mem)

def TickFeeArgs.Fits (a : TickFeeArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.lower ∧ a.lower < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.upper ∧ a.upper < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.current ∧ a.current < 2 ^ 23)

def tickFeeMemoryWords (aw : UInt256) : UInt256 :=
  M (M (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩

theorem tickFeePrefixExactX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21387⟩
      (a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21476⟩
      (tickFeeSide a σ ee false true :: tickFeeSide a σ ee false false ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.upper) ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.lower) :: ⟨0⟩ :: ⟨0⟩ ::
        a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R)
      (tickFeeMemory mem a) (tickFeeMemoryWords aw) rdata σ k' C' := by
  rcases hfit with ⟨hlb, hub, hcb⟩
  have hl : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.lower) =
      EVM.wordOfInt a.lower := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hlb.1 hlb.2]
  have hu : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.upper) =
      EVM.wordOfInt a.upper := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hub.1 hub.2]
  have hc : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.current) =
      EVM.wordOfInt a.current := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hcb.1 hcb.2]
  have hcmp : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.current))
      (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.lower)) =
      if a.current < a.lower then ⟨1⟩ else ⟨0⟩ := by
    rw [hc, hl]
    exact slt_wordOfInt _ _ (by omega) (by omega) (by omega) (by omega)
  have rpre : ∃ k' C', RD (deployedRuntime v) ee g s0
      (if a.lower ≤ a.current then ⟨21441⟩ else ⟨21457⟩)
      (uniswapV3Pool_block_21387_fallthrough_stack (mem := mem) (x0 := a.global1)
        (x1 := a.global0) (x2 := EVM.wordOfInt a.current) (x3 := EVM.wordOfInt a.upper)
        (x4 := EVM.wordOfInt a.lower) (x5 := ⟨5⟩) (R := ret :: R))
      (uniswapV3Pool_block_21387_fallthrough_memory (mem := mem)
        (x3 := EVM.wordOfInt a.upper) (x4 := EVM.wordOfInt a.lower) (x5 := ⟨5⟩))
      (tickFeeMemoryWords aw) rdata σ k' C' := by
    by_cases hd : a.lower ≤ a.current
    · have rr := uniswapV3Pool_block_21387_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcmp, if_neg (by omega)]; rfl) rd
      rw [if_pos hd]
      exact ⟨_, _, rr⟩
    · have rr := uniswapV3Pool_block_21387_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcmp, if_pos (by omega)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      rw [if_neg hd]
      exact ⟨_, _, rr⟩
  obtain ⟨kp, Cp, rp⟩ := rpre
  simp only [uniswapV3Pool_block_21387_fallthrough_stack,
    uniswapV3Pool_block_21387_fallthrough_memory, hl, hu] at rp
  change RD (deployedRuntime v) ee g s0
    (if a.lower ≤ a.current then ⟨21441⟩ else ⟨21457⟩)
    (⟨0⟩ :: ⟨0⟩ :: keccakWord ⟨0⟩ ⟨64⟩ (tickFeeMemory mem a) ::
      keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.lower) ⟨5⟩ mem) ::
      ⟨0⟩ :: ⟨0⟩ :: a.global1 :: a.global0 :: EVM.wordOfInt a.current ::
      EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R)
    (tickFeeMemory mem a) (tickFeeMemoryWords aw) rdata σ kp Cp at rp
  have hh0 : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.lower) ⟨5⟩ mem) =
      solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.lower) := twoWordHashMem_solcMappingSlot_any _ _ _
  have hh1 : keccakWord ⟨0⟩ ⟨64⟩ (tickFeeMemory mem a) =
      solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.upper) :=
    wordAt0Mem_twoWordHashMem_slot_any _ _ _ _
  rw [hh0, hh1] at rp
  by_cases hd : a.lower ≤ a.current
  · rw [if_pos hd] at rp
    obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21441 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rp
    refine ⟨kf, Cf, ?_⟩
    simpa only [uniswapV3Pool_block_21441_stack, tickFeeSide, TickFeeArgs.direct,
      TickFeeArgs.boundary, Bool.false_eq_true, if_false, if_pos hd, tickFeeOutside,
      tickFieldSlot, if_true] using rf
  · rw [if_neg hd] at rp
    obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21457 (immWords := wordsOf (immStore v))
      (by evm_ov) rp
    refine ⟨kf, Cf, ?_⟩
    simpa only [uniswapV3Pool_block_21457_stack, tickFeeSide, TickFeeArgs.direct,
      TickFeeArgs.boundary, TickFeeArgs.global, Bool.false_eq_true, if_false, if_neg hd,
      tickFeeOutside, tickFieldSlot, if_true, u256_add_comm] using rf


theorem tickFeePrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21387⟩
      (a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ⟨21476⟩
      (tickFeeSide a σ ee false true :: tickFeeSide a σ ee false false ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.upper) ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.lower) :: ⟨0⟩ :: ⟨0⟩ ::
        a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R)
      (tickFeeMemory mem a) aw' rdata σ k' C' := by
  obtain ⟨k', C', r'⟩ := tickFeePrefixExactX (v := v) a rd hfit hov
  exact ⟨k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool
