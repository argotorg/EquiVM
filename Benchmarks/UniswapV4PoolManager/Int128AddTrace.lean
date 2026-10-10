import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem int128AddTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {a b : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (ha : signedFits ⟨128, by decide⟩ a) (hb : signedFits ⟨128, by decide⟩ b)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15674⟩ (EVM.wordOfInt a :: EVM.wordOfInt b :: ret :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ (a+b) then ∃ k' C',
      RD (deployedRuntime v) I g s0 ret (EVM.wordOfInt (a+b) :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hsa : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a) = EVM.wordOfInt a :=
    signextend128_wordOfInt ha.1 ha.2
  have hsb : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt b) = EVM.wordOfInt b :=
    signextend128_wordOfInt hb.1 hb.2
  have hs : EVM.wordOfInt (a+b) = EVM.wordOfInt a+EVM.wordOfInt b := by
    simpa only [signed_wordOfInt (signedFits128_int256 ha), signed_wordOfInt (signedFits128_int256 hb)] using
      wordOfInt_signed_add (EVM.wordOfInt a) (EVM.wordOfInt b)
  have hr : int256Fits (a+b) := by
    have ha0 := ha.1; have ha1 := ha.2; have hb0 := hb.1; have hb1 := hb.2
    change -(2^127 : Int) ≤ a at ha0
    change a < (2^127 : Int) at ha1
    change -(2^127 : Int) ≤ b at hb0
    change b < (2^127 : Int) at hb1
    constructor
    · change -(2^255 : Int) ≤ a+b; omega
    · change a+b < (2^255 : Int); omega
  have hg := int128RangeGuard hr
  rw [hs] at hg
  norm_num only at hg
  by_cases hfit : signedFits ⟨128, by decide⟩ (a+b)
  · rw [if_pos hfit]
    have rd1 := poolManagerBlocks.poolManager_block_15674_fallthrough hstack
      (by rw [hsa, hsb, hg, decide_eq_false (not_not.mpr hfit)]; rfl) h
    have rd2 := poolManagerBlocks.poolManager_block_15744 (by change R.length+2 ≤ 1024; omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_15744_stack, hsa, hsb, ← hs] at rd2
    exact ⟨_, _, rd2⟩
  · rw [if_neg hfit]
    have rd1 := poolManagerBlocks.poolManager_block_15674_taken hstack
      (by rw [hsa, hsb, hg, decide_eq_true hfit]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_7572 (by change R.length+4 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
