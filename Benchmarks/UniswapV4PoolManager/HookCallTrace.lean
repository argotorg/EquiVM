import Benchmarks.UniswapV4PoolManager.HookCallPrefixTrace
import Benchmarks.UniswapV4PoolManager.HookReplyTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem hookCallTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem data rdata : ByteArray} {aw ptr ret free : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+11 ≤ 1024) (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hmem : 96 ≤ mem.size) (hdata : BytesObjectView mem ptr data)
    (hd : 32 ≤ data.size) (hsmall : data.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hlo : 96 ≤ ptr.toNat+32) (hbefore : ptr.toNat+32+data.size ≤ free.toNat)
    (hfit : free.toNat+32 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16165⟩
      (accountWord hook :: ptr :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out, callViaEVM evm hook 0 data (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true ∧ hookReplyValid data out then ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret (free :: R)
          (solcReturnDataMem mem free out) aw' out evm'.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨evm', z, out, k1, C1, hcall, henv, hworld, ho, hr⟩ :=
    hookCallPrefixTrace v hstack hI hσ0 hdata hsmall (by omega) h
  refine ⟨evm', z, out, hcall, henv, hworld, ho, ?_⟩
  cases z with
  | false => simpa only [Bool.false_eq_true, false_and, if_false] using hr
  | true =>
    simp only [if_true] at hr
    simp only [true_and]
    exact hookReplyTrace v (by omega) hmem hdata hd (lt_trans ho (by decide)) hlo hbefore hfit hfree hret hr

end Benchmarks.UniswapV4PoolManager
