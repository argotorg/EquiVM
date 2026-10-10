import Benchmarks.UniswapV4PoolManager.HookCallPaidPrefixTrace
import Benchmarks.UniswapV4PoolManager.HookReplyTrace
import Benchmarks.UniswapV4PoolManager.MemoryPaidBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- Hook calls retain paid memory and leave room for the caller's fixed-size allocations. -/
theorem hookCallPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret free : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hlo : 96 ≤ ptr.toNat+32) (hbefore : ptr.toNat+32+data.size ≤ free.toNat)
    (hfit : free.toNat+32 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16165⟩
      (accountWord hook :: ptr :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, callViaEVM evm hook 0 data (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true ∧ hookReplyValid data out then ∃ aw' k' C',
        Cₘ aw' ≤ C' ∧ free.toNat+out.size+4096 ≤ solcMaxU64 ∧
        RD (deployedRuntime v) I g s0 ret (free :: R)
          (solcReturnDataMem mem free out) aw' out post.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  rcases hookCallPaidPrefixTrace v hstack hI hσ0 hdata hsmall (by omega) hpaid h with
    hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  cases z with
  | false => exact .inr ⟨post, false, out, hcall, henv, hworld, ho, hr⟩
  | true =>
    simp only [if_true] at hr
    obtain ⟨k1, C1, hpay1, rd1⟩ := hr
    have ht := hookReplyCostTrace v (by omega) hmem hdata hd (lt_trans ho (by decide))
      hlo hbefore hfit hfree hret rd1
    by_cases hv : hookReplyValid data out
    swap
    · rw [if_neg hv] at ht
      refine .inr ⟨post, true, out, hcall, henv, hworld, ho, ?_⟩
      simpa only [true_and, if_neg hv] using ht
    rw [if_pos hv] at ht
    obtain ⟨aw2, k2, C2, hcost, hspan, rd2⟩ := ht
    have hpay2 : Cₘ aw2 ≤ C2 := by omega
    have hbudget : g.toNat < Cₘ (UInt256.ofNat (2^59-256)) :=
      hgas.trans (by decide +kernel)
    rcases memoryPaidBound hbudget hpay2 rd2 with hog | hwords
    · exact .inl hog
    · have hb : free.toNat+out.size+4096 ≤ solcMaxU64 := by
        change aw2.toNat < 2^59-256 at hwords
        change free.toNat+out.size+4096 ≤ 2^64-1
        omega
      refine .inr ⟨post, true, out, hcall, henv, hworld, ho, ?_⟩
      simp only [true_and, if_pos hv]
      exact ⟨aw2, k2, C2, hpay2, hb, rd2⟩

end Benchmarks.UniswapV4PoolManager
