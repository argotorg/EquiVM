import Benchmarks.UniswapV3.Pool.SignedAmountDeltaEntryTrace
import Benchmarks.UniswapV3.Pool.SafeCast256Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem signedAmountDeltaFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : SignedAmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19616⟩
      (amountDeltaResult second (signedAmountDeltaUnsigned a) ::
        signedAmountDeltaSavedWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hv : signedAmountDeltaValid second a)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (signedAmountDeltaResult second a) :: R) mem aw rdata σ k' C' := by
  have hb : safeCast256Valid (amountDeltaResult second (signedAmountDeltaUnsigned a)) :=
    amountDeltaResult_lt255 second _ (signedAmountDeltaUnsignedFits a hfit) hv
  have hpc : (D_J (deployedRuntime v) 0).contains (signedAmountDeltaReturnPC a) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]
    unfold signedAmountDeltaReturnPC
    split_ifs <;> jump_dest
  simp only [signedAmountDeltaSavedWords, List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_19616 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rcases safeCast256X (v := v) _ r1 hpc (by evm_ov) with ⟨_, hbad⟩ | ⟨_, kr, Cr, rr⟩
  · exact False.elim (hbad hb)
  · by_cases hn : a.liquidity < 0
    · simp only [signedAmountDeltaReturnPC, if_pos hn] at rr
      have r2 := uniswapV3Pool_block_19645 (immWords := wordsOf (immStore v)) (by evm_ov) hret rr
      simp only [uniswapV3Pool_block_19645_stack] at r2
      simp only [signedAmountDeltaResult, if_pos hn, wordOfInt_neg_natCast_eq_sub_zero]
      exact ⟨_, _, r2⟩
    · simp only [signedAmountDeltaReturnPC, if_neg hn] at rr
      have r2 := uniswapV3Pool_block_19621 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      have r3 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r2
      simp only [signedAmountDeltaResult, if_neg hn, wordOfInt_ofNat_toNat]
      exact ⟨_, _, r3⟩

theorem signedAmountDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : SignedAmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (signedAmountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 36 ≤ 1024) :
    (¬signedAmountDeltaValid second a ∧ RDrev (deployedRuntime v) g s0) ∨
      (signedAmountDeltaValid second a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (signedAmountDeltaResult second a) :: R) mem aw rdata σ k' C') := by
  obtain ⟨_, _, r1⟩ := signedAmountDeltaEntryX (v := v) second a rd hfit (by omega)
  rcases amountDeltaX (v := v) second (signedAmountDeltaUnsigned a) r1
    (signedAmountDeltaUnsignedFits a hfit)
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by change R.length + 6 + 30 ≤ 1024; omega) with ⟨hbad, hrev⟩ | ⟨hv, kr, Cr, rr⟩
  · exact Or.inl ⟨hbad, hrev⟩
  · exact Or.inr ⟨hv, signedAmountDeltaFinishX (v := v) second a rr hfit hv hret (by omega)⟩

end Benchmarks.UniswapV3.Pool
