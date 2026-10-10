import Benchmarks.UniswapV4PoolManager.AfterSwapBranchTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapEntryTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapFinishTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapReturn
import Benchmarks.UniswapV4PoolManager.FunctionFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] afterSwapBranchResult afterSwapFinishResult afterSwapReturn

theorem afterSwapBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta src len before ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hbefore : f.locals.get? "beforeSwapHookReturn" = some (.int (EVM.signed before)))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hplo : 96 ≤ paramsPtr.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hroom : free.toNat+64 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+84)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15745⟩
      (accountWord hook :: keyPtr :: paramsPtr :: delta :: src :: len :: before :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm afterSwapFunction.body result ∧
      functionResultTrace (deployedRuntime v) g s0 (afterSwapReturn v I g s0 mem free ret R) result := by
  have he := afterSwapEntryTrace v (by omega) hpaid hret h
  by_cases hself : I.source = hook
  · rw [afterSwapEntryResult, if_pos hself] at he
    obtain ⟨aw', k', C', hpay, rd⟩ := he
    have hcall : evm.executionEnv.source ≠ hook → afterSwapActive hook →
        callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) (false, evm, .empty) := by
      rw [hI]; intro hn _; exact (hn hself).elim
    refine .inr ⟨_, afterSwapBody hc hs hk hp hd hb hbefore hcanonical hlimit hcall, ?_⟩
    rw [afterSwapResult, afterSwapBlockResult, hI, if_pos hself]
    exact afterSwapReturn_unchanged hI hσ0 hfree hroom hpay rd
  · rw [afterSwapEntryResult, if_neg hself] at he
    obtain ⟨aw1, k1, C1, hpay1, rd1⟩ := he
    by_cases ha : afterSwapActive hook
    · rw [if_pos ha] at rd1
      rcases afterSwapBranchTrace (afterSwapPreludeFrame f before) v hstack hI hσ0 hkey hparams hcanonical hlimit
          (balanceDeltaAmount1_fits before) hkb hpb (by omega) hf hsrc hgas hpay1 hfree rd1 with
        hog | ⟨post, z, out, hcall, henv, hworld, ht⟩
      · exact .inl hog
      have hcall' : evm.executionEnv.source ≠ hook → afterSwapActive hook →
          callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta
            (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) := by
        rw [hI]; exact fun _ _ => hcall
      refine .inr ⟨_, afterSwapBody hc hs hk hp hd hb hbefore hcanonical hlimit hcall', ?_⟩
      rw [afterSwapResult]
      apply functionResultTrace_finishBlock
      rw [afterSwapBlockResult, hI, if_neg hself, afterSwapSelectedResult, if_pos ha, hI,
        afterSwapSelectedUnspecified, if_pos ha]
      refine functionResultTrace_continueBlock ht ?_
      rintro f' next hr ⟨rfl, hbound, aw2, k2, C2, hpay2, rd2⟩
      have hfitU := (afterSwapBranchResult_normal hr).2.2
      have hp' := hparams.afterSwapReply I.calldata src.toNat free len I.source key p delta out hsrc hplo
        (by simpa only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil] using hpb) hf
      have hfini := afterSwapFinishTrace f' v (by omega) hp' (by omega)
        (balanceDeltaAmount0_fits before) hfitU hret rd2
      refine functionResultTrace_mono hfini ?_
      rintro next values ⟨rfl, rfl, aw3, k3, C3, hcost, rd3⟩
      exact afterSwapReturn_hook henv hworld hsrc (by omega) hf hbound (by omega) rd3
    · rw [if_neg ha] at rd1
      have hcall : evm.executionEnv.source ≠ hook → afterSwapActive hook →
          callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta
            (I.calldata.extract src.toNat (src.toNat+len.toNat))) (false, evm, .empty) :=
        fun _ hen => (ha hen).elim
      refine .inr ⟨_, afterSwapBody hc hs hk hp hd hb hbefore hcanonical hlimit hcall, ?_⟩
      rw [afterSwapResult]
      apply functionResultTrace_finishBlock
      rw [afterSwapBlockResult, hI, if_neg hself, afterSwapSelectedResult, if_neg ha,
        afterSwapSelectedUnspecified, if_neg ha]
      have hfini := afterSwapFinishTrace (afterSwapPreludeFrame f before) v (by omega) hparams (by omega)
        (balanceDeltaAmount0_fits before) (balanceDeltaAmount1_fits before) hret rd1
      refine functionResultTrace_mono hfini ?_
      rintro next values ⟨rfl, rfl, aw2, k2, C2, hcost, rd2⟩
      exact afterSwapReturn_unchanged hI hσ0 hfree hroom (by omega) rd2

end Benchmarks.UniswapV4PoolManager
