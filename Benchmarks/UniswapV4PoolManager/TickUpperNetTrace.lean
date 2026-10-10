import Benchmarks.UniswapV4PoolManager.TickNetArithmetic
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickUpperNetTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed gross slot flipped x4 x5 x6 x7 x8 x9 x10 : UInt256}
    {delta : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7132⟩
      (packed :: gross :: slot :: flipped :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: EVM.wordOfInt delta :: R)
      mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true) then ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨7205⟩
        (slot :: gross :: EVM.wordOfInt (tickNetAfter packed delta true) :: flipped ::
          x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: EVM.wordOfInt delta :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hs : UInt256.signextend (UInt256.ofNat 15) (UInt256.sar (UInt256.ofNat 128) packed) = tickNetWord packed :=
    tickNetWord_signextend packed
  have hd' : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  have hw : EVM.wordOfInt (tickNetAfter packed delta true) = UInt256.sub (tickNetWord packed) (EVM.wordOfInt delta) :=
    tickNetAfter_word packed true hd
  have hg := int128RangeGuard (tickNetAfter_int256 packed true hd)
  rw [hw, u256_lor_comm] at hg
  norm_num only at hg
  by_cases hf : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true)
  · rw [if_pos hf]
    have rd := poolManagerBlocks.poolManager_block_7132_fallthrough hstack
      (by rw [hs, hd', hg, decide_eq_false (not_not.mpr hf)]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_7132_fallthrough_stack, hs, hd', ← hw] at rd
    exact ⟨_, _, rd⟩
  · rw [if_neg hf]
    have rd := poolManagerBlocks.poolManager_block_7132_taken hstack
      (by rw [hs, hd', hg, decide_eq_true hf]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_7572 (by change R.length+14 ≤ 1024; omega) rd

end Benchmarks.UniswapV4PoolManager
