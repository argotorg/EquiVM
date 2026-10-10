import Benchmarks.UniswapV4PoolManager.DonateHookPrepareTrace
import Benchmarks.UniswapV4PoolManager.HookCallPaidTrace
import Benchmarks.UniswapV4PoolManager.DonateHookReplyMemory
import Benchmarks.UniswapV4PoolManager.HookReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateHookActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free hookPtr keyPtr src amount0 amount1 len delta : UInt256}
    {hook : AccountAddress} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (after : Bool) (hstack : R.length+30 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (donateHookEncodePc after)
      (donateHookEncodeStack after (accountWord hook) hookPtr keyPtr src amount0 amount1 len delta R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      callViaEVM evm hook 0 (donateHookPayload after I.source key amount0 amount1
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true ∧ hookReplyValid (donateHookPayload after I.source key amount0 amount1
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out then
        HookReturnMemory 4000 mem
          (donateHookReplyMemory after I.calldata mem src.toNat free len I.source key amount0 amount1 out)
          free (donateHookReplyFree free len out) ∧
        ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 (donateHookCallRet after)
          (donateHookFree free len :: donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R)
          (donateHookReplyMemory after I.calldata mem src.toNat free len I.source key amount0 amount1 out)
          aw' out post.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  have hsaved : (donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R).length ≤ R.length+6 := by
    cases after <;> simp only [donateHookSavedStack, Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega
  rcases donateHookPrepareTrace v after hstack hk hc hb hf hgas hpaid hfree h with
    hog | ⟨halloc, aw1, k1, C1, hpay1, rd1⟩
  · exact .inl hog
  have he := donateHookFree_toNat free len hf
  have hb' : (donateHookFree free len).toNat ≤ solcMaxU64 := halloc.2
  have hfit : (donateHookFree free len).toNat+32 < UInt256.size := by
    have : solcMaxU64+32 < UInt256.size := by decide
    omega
  have hsize : (I.calldata.extract src.toNat (src.toNat+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  have hdata := donateHookMemory_object after I.calldata mem src.toNat free len I.source key amount0 amount1 hsrc hlo
  have hin := hdata.inBounds
  rcases hookCallPaidTrace v
    (by omega) hI hσ0 (by omega) hdata
    (by rw [donateHookPayload_size]; omega)
    (by
      rw [donateHookPayload_size, hsize]
      have hmax : solcMaxU64 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide
      rw [he] at hb'
      omega)
    (by omega) (by rw [donateHookPayload_size, hsize, he]; omega)
    hfit (donateHookMemory_free _ _ _ _ _ _ _ _ _ _)
    hgas hpay1 (by cases after <;> rw [poolManagerPatchedValidJumps v] <;> jump_dest) rd1 with
      hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  refine .inr ⟨post, z, out, hcall, henv, hworld, ho, ?_⟩
  split_ifs with hv
  · rw [if_pos hv] at hr
    obtain ⟨aw2, k2, C2, hpaid2, hbound, rd2⟩ := hr
    have hfb := donateHookReplyFree_bounds free len out hf hbound
    refine ⟨⟨donateHookReplyMemory_free after I.calldata mem src.toNat free len I.source key amount0 amount1 out hlo hf,
      hfb.1, hfb.2, ?_⟩,
      aw2, k2, C2, hpaid2, rd2⟩
    intro base data hm hbase hlim
    exact hm.donateHookReply after I.calldata src.toNat free len I.source key amount0 amount1 out hsrc hbase hlim hf
  · rwa [if_neg hv] at hr

end Benchmarks.UniswapV4PoolManager
