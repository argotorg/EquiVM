import Benchmarks.UniswapV3.Pool.SignedAmountDeltaModel
import Benchmarks.UniswapV3.Pool.AmountDeltaRoutines
import Benchmarks.UniswapV3.Pool.LiquidityDeltaWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def signedAmountDeltaEntry (second : Bool) : Nat := if second then 19656 else 19588

def signedAmountDeltaEntryWords (a : SignedAmountDeltaArgs) : List UInt256 :=
  [EVM.wordOfInt a.liquidity, a.sqrtB, a.sqrtA]

def signedAmountDeltaReturnPC (a : SignedAmountDeltaArgs) : UInt256 :=
  if a.liquidity < 0 then UInt256.ofNat 19645 else UInt256.ofNat 19621

def signedAmountDeltaSavedWords (a : SignedAmountDeltaArgs) : List UInt256 :=
  [signedAmountDeltaReturnPC a, ⟨0⟩, EVM.wordOfInt a.liquidity, a.sqrtB, a.sqrtA]

theorem signedAmountDeltaSign (a : SignedAmountDeltaArgs) (hfit : a.Fits) :
    UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.liquidity))
      (UInt256.ofNat 0) = if a.liquidity < 0 then ⟨1⟩ else ⟨0⟩ := by
  apply liquidityDeltaRawSign
  rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨128, by decide⟩ _ hfit.2.2.1 hfit.2.2.2]

theorem signedAmountDeltaEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : SignedAmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (signedAmountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
      (amountDeltaEntryWords (signedAmountDeltaUnsigned a) ++
        UInt256.ofNat 19616 :: signedAmountDeltaSavedWords a ++ ret :: R)
      mem aw rdata σ k' C' := by
  have hs := signedAmountDeltaSign a hfit
  simp only [signedAmountDeltaEntryWords, List.cons_append, List.nil_append] at rd
  by_cases hn : a.liquidity < 0
  · have hc : UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.liquidity))
        (UInt256.ofNat 0) ≠ UInt256.ofNat 0 := by rw [hs, if_pos hn]; decide
    have hp : ¬0 ≤ a.liquidity := by omega
    have hm : (signedAmountDeltaUnsigned a).liquidity =
        UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.liquidity) := by
      change EVM.wordOfInt (signedAmountDeltaMagnitude a) = _
      rw [signedAmountDeltaMagnitude, if_pos hn, ← zero_sub a.liquidity, wordOfInt_sub]
      rfl
    have r1 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if second then 19684 else 19626))
        (⟨0⟩ :: EVM.wordOfInt a.liquidity :: a.sqrtB :: a.sqrtA :: ret :: R)
        mem aw rdata σ (k + 9) (C + 34) := by
      cases second
      · exact uniswapV3Pool_block_19588_taken (immWords := wordsOf (immStore v))
          (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      · exact uniswapV3Pool_block_19656_taken (immWords := wordsOf (immStore v))
          (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
        (⟨0⟩ :: UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.liquidity) :: a.sqrtB :: a.sqrtA ::
          UInt256.ofNat 19616 :: UInt256.ofNat 19645 :: ⟨0⟩ :: EVM.wordOfInt a.liquidity ::
            a.sqrtB :: a.sqrtA :: ret :: R) mem aw rdata σ (k + 9 + 11) (C + 34 + 36) := by
      cases second
      · exact uniswapV3Pool_block_19626 (immWords := wordsOf (immStore v)) (by evm_ov)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      · exact uniswapV3Pool_block_19684 (immWords := wordsOf (immStore v)) (by evm_ov)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    change EVM.wordOfInt (signedAmountDeltaMagnitude a) = _ at hm
    simp only [amountDeltaEntryWords, hm, signedAmountDeltaSavedWords, signedAmountDeltaReturnPC,
      if_pos hn, signedAmountDeltaUnsigned, decide_eq_false hp, Bool.toUInt256_false,
      List.cons_append, List.nil_append]
    exact ⟨_, _, r2⟩
  · have hc : UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.liquidity))
        (UInt256.ofNat 0) = UInt256.ofNat 0 := by rw [hs, if_neg hn]; rfl
    have hp : 0 ≤ a.liquidity := by omega
    have hm : (signedAmountDeltaUnsigned a).liquidity = EVM.wordOfInt a.liquidity := by
      simp only [signedAmountDeltaUnsigned, signedAmountDeltaMagnitude, if_neg hn]
    have r1 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if second then 19669 else 19601))
        (⟨0⟩ :: EVM.wordOfInt a.liquidity :: a.sqrtB :: a.sqrtA :: ret :: R)
        mem aw rdata σ (k + 9) (C + 34) := by
      cases second
      · exact uniswapV3Pool_block_19588_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) hc rd
      · exact uniswapV3Pool_block_19656_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) hc rd
    have r2 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
        (⟨1⟩ :: EVM.wordOfInt a.liquidity :: a.sqrtB :: a.sqrtA :: UInt256.ofNat 19616 ::
          UInt256.ofNat 19621 :: ⟨0⟩ :: EVM.wordOfInt a.liquidity :: a.sqrtB :: a.sqrtA :: ret :: R)
        mem aw rdata σ (k + 9 + 8) (C + 34 + 29) := by
      cases second
      · exact uniswapV3Pool_block_19601 (immWords := wordsOf (immStore v)) (by evm_ov)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      · exact uniswapV3Pool_block_19669 (immWords := wordsOf (immStore v)) (by evm_ov)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    change EVM.wordOfInt (signedAmountDeltaMagnitude a) = _ at hm
    simp only [amountDeltaEntryWords, hm, signedAmountDeltaSavedWords, signedAmountDeltaReturnPC,
      if_neg hn, signedAmountDeltaUnsigned, decide_eq_true hp, Bool.toUInt256_true,
      List.cons_append, List.nil_append]
    exact ⟨_, _, r2⟩

end Benchmarks.UniswapV3.Pool
