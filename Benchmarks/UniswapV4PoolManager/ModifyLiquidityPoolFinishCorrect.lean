import Benchmarks.UniswapV4PoolManager.ModifyLiquidityPoolCorrect
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityDeltaCorrect
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityAfterCorrect
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityAccountingCorrect
import Benchmarks.UniswapV4PoolManager.BlockCorrectComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityPoolFinishCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {before f : Frame} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    {keyPtr paramsPtr src len id junk : UInt256} {R : List UInt256} {oldFees oldCaller : Value}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hf : before.contract = contract)
    (hk : before.locals.get? "key" = some (poolKeyValue key))
    (hp : before.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hi : before.locals.get? "id" = some (wordBytes32Value id))
    (hb : before.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (he : before.locals.get? "feesAccrued" = some oldFees)
    (hcaller : before.locals.get? "callerDelta" = some oldCaller)
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkl : 160 ≤ keyPtr.toNat) (hlen : len.toNat ≤ solcMaxU64)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (h : modifyLiquidityAfterPoolTrace v I g s0 before key p keyPtr paramsPtr src len id junk R f evm) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (modifyLiquidityTransition.body.drop 20) result ∧
      abiResultTrace modifyLiquidityTransition.returnType (deployedRuntime v) g s0 result := by
  obtain ⟨hI, hσ0, principal, fees, mem, rdata, free, rfl, hkey, hparams, hkb, hpb, hfb,
    hfree, j0, j1, j2, aw, k, C, hpaid, rd⟩ := h
  let pf := modifyLiquidityPoolReturnFrame before id p principal fees
  have hf' : pf.contract = contract := hf
  have hkeep (name : Ident) (h0 : ("principalDelta" == name) = false)
      (h1 : ("__c6" == name) = false) (h2 : (modifyLiquidityPoolAlias == name) = false)
      (h3 : ("__c7" == name) = false) : pf.locals.get? name = before.locals.get? name :=
    store_get_ne4 _ _ _ _ _ h0 h1 h2 h3
  have hprincipal : pf.locals.get? "principalDelta" = some (.int 0) :=
    (store_get_ne3 _ _ _ _ (by decide : ("__c6" == "principalDelta") = false)
      (by decide : (modifyLiquidityPoolAlias == "principalDelta") = false)
      (by decide : ("__c7" == "principalDelta") = false)).trans (store_get_self _ _ _)
  have hfit : free.toNat+128 < UInt256.size := by
    change _ ≤ 2^64-1 at hfb
    change _ < 2^256
    omega
  obtain ⟨sumResult, hs, ht⟩ := modifyLiquidityDeltaCorrect (f := pf) v (by omega) hf' hI
    (store_get_self _ _ _) hprincipal
    ((hkeep "feesAccrued" (by decide) (by decide) (by decide) (by decide)).trans he)
    ((hkeep "callerDelta" (by decide) (by decide) (by decide) (by decide)).trans hcaller)
    ((hkeep "id" (by decide) (by decide) (by decide) (by decide)).trans hi)
    ((hkeep "params" (by decide) (by decide) (by decide) (by decide)).trans hp)
    hkey hparams hc.2.2.2.2 hl hu hkb hpb hfit hfree hpaid rd
  apply execBlock_trace_append hs ht
  intro ff post _ hh
  obtain ⟨rfl, rfl, aw1, k1, C1, hpaid1, rd1⟩ := hh
  let ef := modifyLiquidityEventFrame pf principal fees
  have hef : ef.contract = contract := (modifyLiquidityEventFrame_contract pf principal fees).trans hf'
  have hekeep (name : Ident) (h0 : ("principalDelta" == name) = false)
      (h1 : ("feesAccrued" == name) = false) (h2 : ("totalDelta" == name) = false)
      (h3 : ("callerDelta" == name) = false) (h4 : ("hookDelta" == name) = false) :
      ef.locals.get? name = pf.locals.get? name := store_get_ne5 _ _ _ _ _ _ h0 h1 h2 h3 h4
  have hek : ef.locals.get? "key" = some (poolKeyValue key) :=
    (hekeep "key" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hkeep "key" (by decide) (by decide) (by decide) (by decide)).trans hk)
  have hep : ef.locals.get? "params" = some (modifyLiquidityParamsValue p) :=
    (hekeep "params" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hkeep "params" (by decide) (by decide) (by decide) (by decide)).trans hp)
  have heb : ef.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (hekeep "hookData" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hkeep "hookData" (by decide) (by decide) (by decide) (by decide)).trans hb)
  have hecaller : ef.locals.get? "callerDelta" = some (.int (EVM.signed (balanceDeltaCombineWord false principal fees))) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "callerDelta") = false)).trans (store_get_self _ _ _)
  have hefees : ef.locals.get? "feesAccrued" = some (.int (EVM.signed fees)) :=
    (store_get_ne3 _ _ _ _ (by decide : ("totalDelta" == "feesAccrued") = false)
      (by decide : ("callerDelta" == "feesAccrued") = false)
      (by decide : ("hookDelta" == "feesAccrued") = false)).trans (store_get_self _ _ _)
  have hkey1 : PoolKeyView (modifyLiquidityEventMemory mem free p) keyPtr key :=
    ⟨hkey.slice.modifyLiquidityEvent free p (by
      simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hkey.fits⟩
  have hparams1 := hparams.modifyLiquidityEvent free p (by
    simpa only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil] using hpb)
  have hfree1 := (modifyLiquidityEventMemory_free mem free p
    (by have := hkey.inBounds; omega) (by omega)).trans hfree
  rcases modifyLiquidityAfterCorrect (f := ef) v (by omega) hI hσ0 hef hek hep hecaller hefees
      (store_get_self _ _ _) heb hkey1 hparams1 hc hl hu (by omega) hkb hpb hfb hlen hsrc hgas hpaid1 hfree1 rd1 with
    hog | ⟨afterResult, hafter, htrace⟩
  · exact .inl hog
  apply execBlock_trace_append hafter htrace
  intro ff post _ hh
  obtain ⟨hIpost, _, caller, hookDelta, mem2, rdata2, free2, rfl, hkey2, hfit2, hfree2, aw2, k2, C2, rd2⟩ := hh
  have hafterkey : (modifyLiquidityAfterHookFrame ef caller hookDelta).locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne3 _ _ _ _ (by decide : ("__c8" == "key") = false)
      (by decide : ("callerDelta" == "key") = false) (by decide : ("hookDelta" == "key") = false)).trans hek
  have hafterfees : (modifyLiquidityAfterHookFrame ef caller hookDelta).locals.get? "feesAccrued" = some (.int (EVM.signed fees)) :=
    (store_get_ne3 _ _ _ _ (by decide : ("__c8" == "feesAccrued") = false)
      (by decide : ("callerDelta" == "feesAccrued") = false)
      (by decide : ("hookDelta" == "feesAccrued") = false)).trans hefees
  have haf := (modifyLiquidityAfterHookFrame_contract ef caller hookDelta).trans hef
  exact .inr (modifyLiquidityAccountingCorrect (f := modifyLiquidityAfterHookFrame ef caller hookDelta)
    v (by omega) hIpost haf hafterkey
    ((store_get_ne _ _ (by decide : ("hookDelta" == "callerDelta") = false)).trans (store_get_self _ _ _))
    hafterfees (store_get_self _ _ _) hkey2 (by omega) hfit2 hfree2 rd2)

end Benchmarks.UniswapV4PoolManager
