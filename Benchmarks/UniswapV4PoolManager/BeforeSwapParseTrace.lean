import Benchmarks.UniswapV4PoolManager.BeforeSwapDeltaTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapReplySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000
attribute [local irreducible] beforeSwapDeltaResult

theorem beforeSwapParseTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw ptr amount ret fee : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hview : BytesObjectView mem ptr out) (hsize : 64 ≤ out.size)
    (hfit : ptr.toNat+64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15491⟩
      (accountWord hook :: ptr :: ret :: fee :: ⟨0⟩ :: amount :: R) mem aw out evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ aw' k' C',
      C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
        (fee :: beforeSwapReplyHook hook out :: beforeSwapReplyAmount hook amount out :: R)
          mem aw' out post.accountMap k' C') (fun _ _ => False)
      (if beforeSwapParse hook then beforeSwapDeltaResult f evm amount out else .ok f evm) := by
  by_cases hp : beforeSwapParse hook
  · rw [if_pos hp]
    have hb := poolManager_block_15491_taken (by simp only [List.length_cons]; omega)
      (by rw [u256_land_comm]; exact hp) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_15491_taken_stack] at hb
    have hd : blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ aw' k' C',
        (C+20)+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
          (fee :: calldataWord out 32 :: (amount+beforeSwapSpecified out) :: R) mem aw' out post.accountMap k' C')
        (fun _ _ => False) (beforeSwapDeltaResult f evm amount out) :=
      beforeSwapDeltaTrace (evm := evm) (amount := amount) (fee := fee) (oldHook := ⟨0⟩)
        (R := R) f v hstack hview hsize hfit hret hb
    refine blockResultTrace_mono hd ?_
    rintro f' post _ ⟨he, aw', k', C', hc, hr⟩
    exact ⟨he, aw', k', C', by omega,
      by simpa only [beforeSwapReplyHook, beforeSwapReplyAmount, if_pos hp] using hr⟩
  · rw [if_neg hp]
    have hb := poolManager_block_15491_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [u256_land_comm]; exact not_not.mp hp) h
    obtain ⟨k', C', hc, hr⟩ := beforeSwapReturnTrace v (by simp only [List.length_cons]; omega) hret hb
    exact ⟨rfl, aw, k', C', by omega,
      by simpa only [beforeSwapReplyHook, beforeSwapReplyAmount, if_neg hp] using hr⟩

end Benchmarks.UniswapV4PoolManager
