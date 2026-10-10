import Benchmarks.UniswapV4PoolManager.NextAmount0FallbackTrace
import Benchmarks.UniswapV4PoolManager.NextAmount0RoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount0AddCoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hp : price ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23895⟩
      ([UInt256.div (nextAmount0Product price amount) amount, price, nextAmount0Product price amount,
        price, amount, amount0Numerator1 liquidity, solcAddrMask, ret] ++ R) mem aw rdata σ k C) :
    if nextAmount0CoreFits price liquidity amount true then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (nextAmount0CoreWord price liquidity amount true :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hprod : UInt256.div (nextAmount0Product price amount) amount = price
  · have rd1 := poolManagerBlocks.poolManager_block_23895_taken
      (x0 := UInt256.div (nextAmount0Product price amount) amount) (x1 := price)
      (by change R.length+8 ≤ 1024; omega)
      (by rw [hprod, uInt256_eq_self]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    by_cases hb : (amount0Numerator1 liquidity).toNat ≤
        (amount0Numerator1 liquidity+nextAmount0Product price amount).toNat
    · have hd : nextAmount0Direct price liquidity amount := ⟨hprod, hb⟩
      simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hd]
      have rd2 := poolManagerBlocks.poolManager_block_23933_fallthrough
        (by change R.length+8 ≤ 1024; omega) (ult_zero hb) rd1
      have rd3 := poolManagerBlocks.poolManager_block_23943 (by change R.length+7 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have hr := nextAmount0RoundTrace v false hstack hret rd3
      by_cases hf : nextAmount0RoundFits (amount0Numerator1 liquidity) price
          (amount0Numerator1 liquidity+nextAmount0Product price amount) false
      · rw [if_pos hf] at hr ⊢
        obtain ⟨k4, C4, hC4, rd4⟩ := hr
        exact ⟨k4, C4, by omega, rd4⟩
      · rw [if_neg hf] at hr ⊢
        exact hr
    · have hd : ¬nextAmount0Direct price liquidity amount := fun hh => hb hh.2
      simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hd, if_false]
      have hlt : UInt256.lt (amount0Numerator1 liquidity+nextAmount0Product price amount)
          (amount0Numerator1 liquidity) ≠ ⟨0⟩ := by
        rw [ult_one (Nat.lt_of_not_ge hb)]
        decide
      have rd2 := poolManagerBlocks.poolManager_block_23933_taken (by change R.length+8 ≤ 1024; omega) hlt
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := nextAmount0FallbackTrace v (by omega) hp hret rd2
      by_cases hf : nextAmount0FallbackFits price liquidity amount
      · rw [if_pos hf] at hr ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hr
        exact ⟨k3, C3, by omega, rd3⟩
      · rw [if_neg hf] at hr ⊢
        exact hr
  · have hd : ¬nextAmount0Direct price liquidity amount := fun hh => hprod hh.1
    simp only [nextAmount0CoreFits, nextAmount0CoreWord, if_true, hd, if_false]
    have heq := uInt256_eq_zero_of_ne (fun hh => hprod (uInt256_eq_one_eq hh))
    have rd1 := poolManagerBlocks.poolManager_block_23895_fallthrough (by change R.length+8 ≤ 1024; omega) heq h
    have hr := nextAmount0FallbackTrace v (by omega) hp hret rd1
    by_cases hf : nextAmount0FallbackFits price liquidity amount
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hr ⊢
      exact hr

end Benchmarks.UniswapV4PoolManager
