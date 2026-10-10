import Benchmarks.UniswapV4PoolManager.AfterLiquidityPrepareTrace
import Benchmarks.UniswapV4PoolManager.AfterLiquidityFinishTrace
import Benchmarks.UniswapV4PoolManager.HookDeltaTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterLiquidityReplyMemory (add : Bool) (src mem : ByteArray) (srcOff : Nat) (free len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256)
    (out : ByteArray) : ByteArray :=
  solcReturnDataMem (afterLiquidityMemory add src mem srcOff free len sender key p delta fees)
    (afterLiquidityFree free len) out

def afterLiquidityReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (σ : AccountMap) (ret delta hookDelta : UInt256) (R : List UInt256) : Prop :=
  ∃ aw k C, RD (deployedRuntime v) I g s0 ret (hookDelta :: delta :: R) mem aw rdata σ k C

def afterLiquidityActiveResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 post : State)
    (add : Bool) (mem : ByteArray) (src free len ret : UInt256) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256) (z : Bool) (out : ByteArray)
    (R : List UInt256) : Prop :=
  let payload := afterLiquidityPayload add I.source key p delta fees (I.calldata.extract src.toNat (src.toNat+len.toNat))
  let parse := afterLiquidityParse hook add
  let hookDelta := hookDeltaWord out parse
  if z = true ∧ hookReplyValid payload out then
    if parse = true ∧ out.size ≠ 64 then RDrev (deployedRuntime v) g s0
    else if balanceDeltaCombineFits true delta hookDelta then
      afterLiquidityReturnTrace v I g s0
        (afterLiquidityReplyMemory add I.calldata mem src.toNat free len I.source key p delta fees out)
        out post.accountMap ret (balanceDeltaCombineWord true delta hookDelta) hookDelta R
    else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem afterLiquidityActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (f : Frame) (v : PoolManagerImmutables) (add : Bool) (hstack : R.length+27 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+576 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (afterLiquidityEncodePc add)
      (afterLiquidityEncodeStack add (accountWord hook) keyPtr paramsPtr delta fees src len ret R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, AllocationBounds free (afterLiquidityAllocationSize len) ∧
      callViaEVM evm hook 0 (afterLiquidityPayload add I.source key p delta fees
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      afterLiquidityActiveResult v I g s0 post add mem src free len ret hook key p delta fees z out R := by
  rcases afterLiquidityPrepareTrace v add hstack hk hp hc hl hu hkb hpb hf hgas hpaid hfree h with
    hog | ⟨hb, aw1, k1, C1, _, rd1⟩
  · exact .inl hog
  have he := afterLiquidityFree_toNat free len hf
  have hb' : (afterLiquidityFree free len).toNat ≤ solcMaxU64 := hb.2
  have hfit : (afterLiquidityFree free len).toNat+64 < UInt256.size := by
    have : solcMaxU64+64 < UInt256.size := by decide
    omega
  have hsize : (I.calldata.extract src.toNat (src.toNat+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  have hdata := afterLiquidityMemory_object add I.calldata mem src.toNat free len I.source key p delta fees hsrc hlo
  have hin := hdata.inBounds
  obtain ⟨post, z, out, hcall, henv, hworld, ho, hr⟩ := hookDeltaTrace f v
    (by simp only [List.length_cons]; omega) hI hσ0 (by omega) hdata
    (by rw [afterLiquidityPayload, liquidityHookPayload_size]; change 32 ≤ 452+_; omega)
    (by
      rw [afterLiquidityPayload, liquidityHookPayload_size, hsize]
      change 452+paddedSize len.toNat ≤ Ethereum.EVM.maxReturnDataSizeByGas
      have hmax : solcMaxU64 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide
      rw [he] at hb'
      omega)
    (by omega) (by rw [afterLiquidityPayload, liquidityHookPayload_size, hsize, he]; change _+32+(452+_) ≤ _; omega)
    hfit (afterLiquidityMemory_free _ _ _ _ _ _ _ _ _ _ _)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  refine .inr ⟨post, z, out, hb, hcall, henv, hworld, ho, ?_⟩
  unfold afterLiquidityActiveResult
  by_cases hv : z = true ∧ hookReplyValid (afterLiquidityPayload add I.source key p delta fees
      (I.calldata.extract src.toNat (src.toNat+len.toNat))) out
  · rw [hookDeltaResult, if_pos hv, hookDeltaReplyResult] at hr
    rw [if_pos hv]
    by_cases hbad : afterLiquidityParse hook add = true ∧ out.size ≠ 64
    · rw [if_pos hbad] at hr ⊢
      exact hr
    · rw [if_neg hbad] at hr ⊢
      obtain ⟨_, _, aw2, k2, C2, rd2⟩ := hr
      have hfinish := afterLiquidityFinishTrace f v (by omega) hret rd2
      by_cases hfitDelta : balanceDeltaCombineFits true delta (hookDeltaWord out (afterLiquidityParse hook add))
      · rw [if_pos hfitDelta] at hfinish ⊢
        obtain ⟨k3, C3, rd3⟩ := hfinish
        exact ⟨_, _, _, rd3⟩
      · rw [if_neg hfitDelta] at hfinish ⊢
        exact hfinish
  · rw [hookDeltaResult, if_neg hv] at hr
    rw [if_neg hv]
    exact hr

end Benchmarks.UniswapV4PoolManager
