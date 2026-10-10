import Benchmarks.UniswapV4PoolManager.InitializePoolCorrect
import Benchmarks.UniswapV4PoolManager.BeforeInitializeHookTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem initializeHooksCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {key : PoolKeyWords} {price fee free keyPtr junk aw : UInt256}
    {mem rdata : ByteArray} {old : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hprice : price.toNat < 2^160) (hfee : fee.toNat < 2^24)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)))
    (ht : f.locals.get? "tick" = some old) (hn : f.locals.get? "_pools" = none)
    (hv : PoolKeyView mem keyPtr key) (hl : 96 ≤ keyPtr.toNat)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hs : free.toNat ≤ 1024) (haw : aw.toNat ≤ 2048)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4257⟩
      (fee :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) :: keyPtr :: price ::
        (keyPtr+⟨96⟩) :: price :: junk :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm (initializeTransition.body.drop 12) result ∧
      signedResultTrace ⟨24, by decide⟩ (deployedRuntime v) g s0 result := by
  have hw : accountWord (AccountAddress.ofNat key.hooks.toNat) = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
  have halloc : free.toNat+323 ≤ solcMaxU64 := by change _ ≤ 2^64-1; omega
  rcases beforeInitializeHookTrace v (by omega) hI hσ0 hv hc hw hb (by omega)
      hgas haw hs hfree h with hog | ⟨evm', z, out, hcall, henv, hworld, ho, hbound, hr⟩
  · exact .inl hog
  apply Or.inr
  let f1 : Frame := {f with locals := f.locals.insert "__c3" .unit}
  have hkey := evalLocalValue (cfg := config) (evm := evm) hk
  have hstmt := beforeInitializeCall hf (evalStructField hkey (field := "hooks") rfl)
    hkey (evalLocalValue hp) hc hprice
    (by simpa only [hI] using hcall) "__c3"
  simp only [hookInvocationResult, resumeCallResult_ite, resumeCallResult_returned,
    resumeCallResult_reverted, hI] at hstmt
  have hfinish (next : State) (hnext : next.executionEnv = I)
      (htrace : initializePoolTraceResult v I g s0 next key price fee) :
      ∃ result, ExecFuncBody config f1 next (initializeTransition.body.drop 13) result ∧
        signedResultTrace ⟨24, by decide⟩ (deployedRuntime v) g s0 result :=
    initializePoolCorrect v hnext hf hc hprice hfee
      ((store_get_ne _ _ (by decide : ("__c3" == "key") = false)).trans hk)
      ((store_get_ne _ _ (by decide : ("__c3" == "sqrtPriceX96") = false)).trans hp)
      ((store_get_ne _ _ (by decide : ("__c3" == "lpFee") = false)).trans he)
      ((store_get_ne _ _ (by decide : ("__c3" == "tick") = false)).trans ht)
      ((store_get_ne _ _ (by decide : ("__c3" == "_pools") = false)).trans hn) htrace
  unfold beforeInitializeTraceResult at hr
  by_cases hen : hookEnabled I.source (AccountAddress.ofNat key.hooks.toNat) ⟨8192⟩
  · simp only [if_pos hen] at hr hstmt
    by_cases hgood : z = true ∧ hookReplyValid (beforeInitializePayload I.source key price) out
    · rw [if_pos hgood] at hr hstmt
      obtain ⟨a, b, aw1, k1, C1, rd1⟩ := hr
      have hfit : free.toNat+320 < UInt256.size := by change _ < 2^256; omega
      have hv1 := beforeInitializeReplyMemory_key hv hb hl hfit I.source price out
      have hfree1 := beforeInitializeReplyMemory_free mem free I.source key price out hfit
      have hfb := beforeInitializeReplyFree_bounds free out hs (hbound hgood.1)
      have hpool := initializePoolTrace v hstack henv hworld hv1 hc hl (by omega) hfb.2
        hfree1 hprice hfee rd1
      obtain ⟨result, hbody, htrace⟩ := hfinish evm' henv hpool
      exact ⟨result, execFuncBody_prepend (execBlock_singleton hstmt) hbody, htrace⟩
    · rw [if_neg hgood] at hr hstmt
      exact ⟨.reverted, .execBlockRevert (ExecBlock.consRevert hstmt), hr⟩
  · simp only [if_neg hen] at hr hstmt
    obtain ⟨a, b, aw1, k1, C1, rd1⟩ := hr
    have hpool := initializePoolTrace v hstack hI hσ0 hv hc hl hb halloc hfree hprice hfee rd1
    obtain ⟨result, hbody, htrace⟩ := hfinish evm hI hpool
    exact ⟨result, execFuncBody_prepend (execBlock_singleton hstmt) hbody, htrace⟩

end Benchmarks.UniswapV4PoolManager
