import Benchmarks.UniswapV4PoolManager.BeforeSwapBranchTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapEntryTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapReturn
import Benchmarks.UniswapV4PoolManager.FunctionFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] beforeSwapBranchResult beforeSwapReturn

theorem beforeSwapBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hklo : 96 ≤ keyPtr.toNat) (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hroom : free.toNat+4000 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+63)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15172⟩
      (accountWord hook :: keyPtr :: paramsPtr :: src :: len :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm beforeSwapFunction.body result ∧
      functionResultTrace (deployedRuntime v) g s0 (beforeSwapReturn v I g s0 mem free ret R) result := by
  have he := beforeSwapEntryTrace v (by omega) hparams (by omega) hpaid hret h
  by_cases hself : I.source = hook
  · rw [beforeSwapEntryResult, if_pos hself] at he
    obtain ⟨aw', k', C', hpay, rd⟩ := he
    have hcall : evm.executionEnv.source ≠ hook → beforeSwapActive hook →
        callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) (false, evm, .empty) := by
      rw [hI]; intro hn _; exact (hn hself).elim
    refine .inr ⟨_, beforeSwapBody hc hs hk hp hd hcanonical hlimit hcall, ?_⟩
    rw [beforeSwapResult, beforeSwapBlockResult, hI, if_pos hself]
    exact beforeSwapReturn_bypass hI hσ0 hfree hroom hpay rd
  · rw [beforeSwapEntryResult, if_neg hself] at he
    by_cases ha : beforeSwapActive hook
    · rw [if_pos ha] at he
      obtain ⟨aw1, k1, C1, hpay1, rd1⟩ := he
      rcases beforeSwapBranchTrace (beforeSwapPreludeFrame f p) v hstack hI hσ0 hkey hparams hcanonical hlimit
          hkb hpb hklo hf hsrc hgas hpay1 hfree hret rd1 with
        hog | ⟨post, z, out, hcall, henv, hworld, ht⟩
      · exact .inl hog
      have hcall' : evm.executionEnv.source ≠ hook → beforeSwapActive hook →
          callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p
            (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) := by
        rw [hI]; exact fun _ _ => hcall
      refine .inr ⟨_, beforeSwapBody hc hs hk hp hd hcanonical hlimit hcall', ?_⟩
      rw [beforeSwapResult]
      apply functionResultTrace_finishBlock
      rw [beforeSwapBlockResult, hI, if_neg hself, beforeSwapSelectedResult, if_pos ha, hI]
      refine functionResultTrace_continueBlock ht ?_
      rintro f' next _ ⟨rfl, hb, aw', k', C', hpay, rd⟩
      rw [beforeSwapReturnResult, if_pos ha]
      exact beforeSwapReturn_hook henv hworld hsrc (by omega) hf hb hpay rd
    · rw [if_neg ha] at he
      obtain ⟨aw', k', C', hpay, rd⟩ := he
      have hcall : evm.executionEnv.source ≠ hook → beforeSwapActive hook →
          callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p
            (I.calldata.extract src.toNat (src.toNat+len.toNat))) (false, evm, .empty) :=
        fun _ hen => (ha hen).elim
      refine .inr ⟨_, beforeSwapBody hc hs hk hp hd hcanonical hlimit hcall, ?_⟩
      rw [beforeSwapResult, beforeSwapBlockResult, hI, if_neg hself, beforeSwapSelectedResult, if_neg ha]
      change functionResultTrace _ _ _ _ (finishBlockResult (beforeSwapReturnResult _ evm hook key _ .empty))
      rw [beforeSwapReturnResult, if_neg ha]
      exact beforeSwapReturn_bypass hI hσ0 hfree hroom hpay rd

end Benchmarks.UniswapV4PoolManager
