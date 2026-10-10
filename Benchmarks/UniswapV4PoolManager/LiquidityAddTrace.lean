import Benchmarks.UniswapV4PoolManager.LiquidityAddSource
import Benchmarks.UniswapV4PoolManager.UnsignedWordRange
import Benchmarks.UniswapV4PoolManager.Signed128
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem liquidityAddWord {x : UInt256} {y : Int} (hx : x.toNat < 2^128)
    (hlo : -(2^127 : Int) ≤ y) (hhi : y < 2^127) :
    EVM.wordOfInt (Int.ofNat x.toNat+y) = x+EVM.wordOfInt y := by
  have hsx : EVM.signed x = Int.ofNat x.toNat := by
    change (if x.toNat < 2^255 then Int.ofNat x.toNat else Int.ofNat x.toNat-Int.ofNat (2^256)) = _
    rw [if_pos (by omega)]
  have hsy := signed_wordOfInt (i := y) (show int256Fits y from ⟨by omega, by omega⟩)
  simpa only [hsx, hsy] using wordOfInt_signed_add x (EVM.wordOfInt y)

theorem liquidityAddTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x ret : UInt256} {y : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hx : x.toNat < 2^128) (hlo : -(2^127 : Int) ≤ y) (hhi : y < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17774⟩ (x :: EVM.wordOfInt y :: ret :: R) mem aw rdata σ k C) :
    if liquidityAddFits x y then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (EVM.wordOfInt (Int.ofNat x.toNat+y) :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land x (UInt256.ofNat 340282366920938463463374607431768211455) = x :=
    u256LandMaskCleanOfToNat _ _ rfl hx
  have hsign : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt y) = EVM.wordOfInt y :=
    signextend128_wordOfInt hlo hhi
  have hword := liquidityAddWord hx hlo hhi
  have hsum : int256Fits (Int.ofNat x.toNat+y) := by
    constructor
    · change -(2^255 : Int) ≤ Int.ofNat x.toNat+y
      simp only [Int.ofNat_eq_natCast]
      omega
    · change Int.ofNat x.toNat+y < (2^255 : Int)
      simp only [Int.ofNat_eq_natCast]
      omega
  have hguard := wordOfInt_unsignedRange ⟨128, by decide⟩ (by decide) hsum
  rw [hword] at hguard
  by_cases hfit : liquidityAddFits x y
  · rw [if_pos hfit]
    have rd1 := poolManagerBlocks.poolManager_block_17774_fallthrough hstack
      (by rw [hclean, hsign]; exact hguard.mpr hfit) h
    have rd2 := poolManagerBlocks.poolManager_block_17809 (by simp only [List.length_cons]; omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_17809_stack, hclean, hsign, ← hword] at rd2
    exact ⟨_, _, rd2⟩
  · rw [if_neg hfit]
    have rd1 := poolManagerBlocks.poolManager_block_17774_taken hstack
      (by rw [hclean, hsign]; exact fun he => hfit (hguard.mp he))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_17810 (by change R.length+4 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
