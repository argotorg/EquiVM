import Benchmarks.UniswapV4PoolManager.HookDeltaSource
import Benchmarks.UniswapV4PoolManager.BytesObjectWord
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_041
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_050
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookDeltaReplyCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {parse : Bool} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hview : BytesObjectView mem ptr out) (ho : out.size < UInt256.size)
    (hfit : ptr.toNat+64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17833⟩
      (ptr :: UInt256.fromBool parse :: ret :: R) mem aw out evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (hookDeltaWord out parse))] ∧ ∃ aw' k' C',
        C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret (hookDeltaWord out parse :: R)
          mem aw' out post.accountMap k' C') (hookDeltaReplyResult f evm out parse) := by
  cases parse with
  | false =>
    have rd1 := poolManagerBlocks.poolManager_block_17833_taken (by simp only [List.length_cons]; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_14989 (by omega) hret rd1
    simp only [hookDeltaReplyResult, Bool.false_eq_true, false_and, if_false]
    exact ⟨rfl, rfl, _, _, _, by omega, rd2⟩
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_17833_fallthrough (by simp only [List.length_cons]; omega)
      (by decide) h
    have hlen : UInt256.sub (memLoad ptr mem) (UInt256.ofNat 64) = ⟨0⟩ ↔ out.size = 64 := by
      rw [hview.lengthWord, u256_sub_eq_zero_iff_eq]
      constructor
      · intro hh
        have he := congrArg UInt256.toNat hh
        rw [UInt256.toNat_ofNat_of_lt ho] at he
        exact he
      · intro hh; rw [hh]
    simp only [hookDeltaReplyResult, true_and]
    by_cases hl : out.size = 64
    · rw [if_neg (not_not.mpr hl)]
      have rd2 := poolManagerBlocks.poolManager_block_17840_fallthrough
        (by simp only [List.length_cons]; omega) (hlen.mpr hl) rd1
      have rd3 := poolManagerBlocks.poolManager_block_17849 (by omega) hret rd2
      have hload : memLoad (UInt256.ofNat 64+ptr) mem = calldataWord out 32 := by
        apply hview.loadWord (by omega)
        rw [u256_add_comm, uadd_word_ofNat_toNat ptr 64 hfit]
      change RD (deployedRuntime v) I g s0 ret (memLoad (UInt256.ofNat 64+ptr) mem :: R)
        mem _ out evm.accountMap _ _ at rd3
      rw [hload] at rd3
      exact ⟨rfl, rfl, _, _, _, by dsimp only [memExpansionCost]; omega, rd3⟩
    · rw [if_pos hl]
      have rd2 := poolManagerBlocks.poolManager_block_17840_taken
        (by simp only [List.length_cons]; omega) (fun hh => hl (hlen.mp hh))
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact poolManagerBlocks.poolManager_block_15621 (by simp only [List.length_cons]; omega) rd2

theorem hookDeltaReplyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {parse : Bool} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hview : BytesObjectView mem ptr out) (ho : out.size < UInt256.size)
    (hfit : ptr.toNat+64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17833⟩
      (ptr :: UInt256.fromBool parse :: ret :: R) mem aw out evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (hookDeltaWord out parse))] ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret (hookDeltaWord out parse :: R)
          mem aw' out post.accountMap k' C') (hookDeltaReplyResult f evm out parse) := by
  exact functionResultTrace_mono (hookDeltaReplyCostTrace f v hstack hview ho hfit hret h)
    (fun _ _ ⟨he, hv, aw', k', C', _, hr⟩ => ⟨he, hv, aw', k', C', hr⟩)

end Benchmarks.UniswapV4PoolManager
