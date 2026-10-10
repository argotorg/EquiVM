import Benchmarks.UniswapV4PoolManager.BeforeSwapParseTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapFeeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000
attribute [local irreducible] beforeSwapDeltaResult

theorem beforeSwapReplyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw ptr keyPtr amount ret : UInt256} {hook : AccountAddress} {key : PoolKeyWords}
    {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : key.fee.toNat < 2^24)
    (hview : BytesObjectView mem ptr out) (hsize : out.size < UInt256.size)
    (hfit : ptr.toNat+96 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15462⟩
      (ptr :: accountWord hook :: keyPtr :: ret :: ⟨0⟩ :: ⟨0⟩ :: amount :: R) mem aw out evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ aw' k' C',
      C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
        (beforeSwapRawFee key out :: beforeSwapReplyHook hook out :: beforeSwapReplyAmount hook amount out :: R)
          mem aw' out post.accountMap k' C') (fun _ _ => False)
      (beforeSwapReplyResult f evm hook key amount out) := by
  have hlen : UInt256.sub (memLoad ptr mem) (UInt256.ofNat 96) = ⟨0⟩ ↔ out.size = 96 := by
    rw [hview.lengthWord, u256_sub_eq_zero_iff_eq]
    constructor
    · intro he
      have he' := congrArg UInt256.toNat he
      rwa [UInt256.toNat_ofNat_of_lt hsize] at he'
    · intro he; rw [he]
  by_cases hs : out.size = 96
  · rw [beforeSwapReplyResult, if_pos hs]
    have hlenTrace := poolManager_block_15462_fallthrough (by simp only [List.length_cons]; omega) (hlen.mpr hs) h
    obtain ⟨aw1, k1, C1, hc1, hfee⟩ := beforeSwapFeeTrace v (by simp only [List.length_cons]; omega)
      hk hc hview (by omega) hfit hlenTrace
    have hp := beforeSwapParseTrace (beforeSwapFeeFrame f key out) v hstack hview (by omega) (by omega) hret hfee
    refine blockResultTrace_mono hp ?_
    rintro f' post _ ⟨he, aw', k', C', hc2, hr⟩
    refine ⟨he, aw', k', C', ?_, hr⟩
    dsimp only [memExpansionCost] at hc1
    omega
  · rw [beforeSwapReplyResult, if_neg hs]
    have hlenTrace := poolManager_block_15462_taken (by simp only [List.length_cons]; omega)
      (fun he => hs (hlen.mp he)) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManager_block_15621 (by simp only [poolManager_block_15462_taken_stack, List.length_cons]; omega) hlenTrace

end Benchmarks.UniswapV4PoolManager
