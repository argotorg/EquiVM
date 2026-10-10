import Benchmarks.UniswapV3.Pool.SwapStepDeltaTrace
import Benchmarks.UniswapV3.Pool.SwapStepPrefixTrace
import Benchmarks.UniswapV3.Pool.SwapStepInitialModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepInputDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12504⟩
      (swapStepBudget a :: ⟨0⟩ ::
        swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hov : R.length + 42 ≤ 1024) :
    (¬amountDeltaValid (swapStepDeltaOne a true) (swapStepDeltaArgs a a.target true) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (amountDeltaValid (swapStepDeltaOne a true) (swapStepDeltaArgs a a.target true) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12542⟩
        (swapStepInitialAmount a true :: swapStepBudget a ::
          swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ k' C') := by
  simp only [swapStepReadyWords, swapStepRawWords, List.cons_append, List.nil_append] at rd
  cases hz : swapStepZeroForOne a
  · simp only [hz] at rd
    have r1 := uniswapV3Pool_block_12504_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r2 := uniswapV3Pool_block_12512 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0
        (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a true)))
        (swapStepDeltaRawWords a true currentRaw targetRaw liquidityRaw ++ ⟨12524⟩ ::
          swapStepBudget a :: swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 6 + 7) (C + 22 + 26) := by
      simpa only [uniswapV3Pool_block_12512_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepReadyWords, swapStepRawWords, hz, Bool.not_false,
        Bool.false_eq_true, if_false, if_true, List.cons_append, List.nil_append] using r2
    rcases swapStepDeltaX (v := v) a a.target true currentRaw targetRaw liquidityRaw rcall
      hc ht hl ha ha.2.1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 12 + 30 ≤ 1024; omega) with ⟨hb, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · exact Or.inl ⟨hb, rr⟩
    · have r3 := uniswapV3Pool_block_12524 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      exact Or.inr ⟨hv, _, _, r3⟩
  · simp only [hz] at rd
    have r1 := uniswapV3Pool_block_12504_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_12529 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0
        (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a true)))
        (swapStepDeltaRawWords a true currentRaw targetRaw liquidityRaw ++ ⟨12542⟩ ::
          swapStepBudget a :: swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 6 + 8) (C + 22 + 27) := by
      simpa only [uniswapV3Pool_block_12529_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepReadyWords, swapStepRawWords, hz, Bool.not_true,
        Bool.false_eq_true, if_false, if_true, List.cons_append, List.nil_append] using r2
    rcases swapStepDeltaX (v := v) a a.target true currentRaw targetRaw liquidityRaw rcall
      hc ht hl ha ha.2.1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 12 + 30 ≤ 1024; omega) with ⟨hb, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · exact Or.inl ⟨hb, rr⟩
    · exact Or.inr ⟨hv, kr, Cr, rr⟩

theorem swapStepOutputDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12580⟩
      (swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hov : R.length + 41 ≤ 1024) :
    (¬amountDeltaValid (swapStepDeltaOne a false) (swapStepDeltaArgs a a.target false) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (amountDeltaValid (swapStepDeltaOne a false) (swapStepDeltaArgs a a.target false) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12616⟩
        (swapStepInitialAmount a false ::
          swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ k' C') := by
  simp only [swapStepReadyWords, swapStepRawWords, List.cons_append, List.nil_append] at rd
  cases hz : swapStepZeroForOne a
  · simp only [hz] at rd
    have r1 := uniswapV3Pool_block_12580_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r2 := uniswapV3Pool_block_12586 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0
        (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a false)))
        (swapStepDeltaRawWords a false currentRaw targetRaw liquidityRaw ++ ⟨12598⟩ ::
          swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 4 + 7) (C + 17 + 26) := by
      simpa only [uniswapV3Pool_block_12586_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepReadyWords, swapStepRawWords, hz, Bool.false_eq_true,
        if_false, if_true, List.cons_append, List.nil_append] using r2
    rcases swapStepDeltaX (v := v) a a.target false currentRaw targetRaw liquidityRaw rcall
      hc ht hl ha ha.2.1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 11 + 30 ≤ 1024; omega) with ⟨hb, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · exact Or.inl ⟨hb, rr⟩
    · have r3 := uniswapV3Pool_block_12598 (immWords := wordsOf (immStore v))
        (by change R.length + 12 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      exact Or.inr ⟨hv, _, _, r3⟩
  · simp only [hz] at rd
    have r1 := uniswapV3Pool_block_12580_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_12603 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0
        (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a false)))
        (swapStepDeltaRawWords a false currentRaw targetRaw liquidityRaw ++ ⟨12616⟩ ::
          swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 4 + 8) (C + 17 + 27) := by
      simpa only [uniswapV3Pool_block_12603_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepReadyWords, swapStepRawWords, hz, Bool.false_eq_true,
        if_false, if_true, List.cons_append, List.nil_append] using r2
    rcases swapStepDeltaX (v := v) a a.target false currentRaw targetRaw liquidityRaw rcall
      hc ht hl ha ha.2.1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 11 + 30 ≤ 1024; omega) with ⟨hb, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · exact Or.inl ⟨hb, rr⟩
    · exact Or.inr ⟨hv, kr, Cr, rr⟩

end Benchmarks.UniswapV3.Pool
