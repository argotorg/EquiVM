import Benchmarks.UniswapV4PoolManager.HookCallTrace
import Benchmarks.UniswapV4PoolManager.HookReplyGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem hookCallBoundTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret free : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (haw : aw.toNat ≤ 2048) (hf : free.toNat ≤ 2048)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hlo : 96 ≤ ptr.toNat+32) (hbefore : ptr.toNat+32+data.size ≤ free.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16165⟩
      (accountWord hook :: ptr :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ evm' z out, callViaEVM evm hook 0 data (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (z = true → out.size+4096 ≤ solcMaxU64) ∧
      (if z = true ∧ hookReplyValid data out then ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret (free :: R)
          (solcReturnDataMem mem free out) aw' out evm'.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  have hfit : free.toNat+32 < UInt256.size := by change _ < 2^256; omega
  have hp : ptr.toNat+32 < UInt256.size := by omega
  obtain ⟨evm', z, out, k1, C1, hcall, henv, hworld, ho, hr⟩ :=
    hookCallPrefixTrace v hstack hI hσ0 hdata hsmall hp h
  cases z with
  | false =>
    apply Or.inr
    refine ⟨evm', false, out, hcall, henv, hworld, ho, (by simp), ?_⟩
    simpa only [Bool.false_eq_true, false_and, if_false] using hr
  | true =>
    simp only [if_true] at hr
    have hw : (hookCallActiveWords aw ptr data).toNat ≤ 2048 := by
      change (M (M aw ptr ⟨32⟩) (ptr+UInt256.ofNat 32) (UInt256.ofNat data.size)).toNat ≤ 2048
      apply memoryWords_le (memoryWords_le haw (by change ptr.toNat+32 ≤ 32*2048; omega))
      rw [uadd_word_ofNat_toNat ptr 32 hp,
        UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hsmall (by decide))]
      omega
    by_cases hs : out.size+4096 ≤ solcMaxU64
    · apply Or.inr
      refine ⟨evm', true, out, hcall, henv, hworld, ho, (fun _ => hs), ?_⟩
      simp only [true_and]
      exact hookReplyTrace v (by omega) hmem hdata hd (lt_trans ho (by decide)) hlo hbefore hfit hfree hret hr
    · exact .inl (hookLargeReply_outOfGas v (by omega) hgas hw hf (lt_trans ho (by decide))
        (Nat.lt_of_not_ge hs) hfree hr)

end Benchmarks.UniswapV4PoolManager
