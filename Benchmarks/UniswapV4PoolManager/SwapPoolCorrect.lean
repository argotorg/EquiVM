import Benchmarks.UniswapV4PoolManager.SwapPoolSelectTrace
import Benchmarks.UniswapV4PoolManager.SwapWrapperCallCorrect
import Benchmarks.UniswapV4PoolManager.SwapAfterCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapPoolCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free rawFee fee before amount src len id keyPtr paramsPtr junk : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+49 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some oldDelta)
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hbefore : f.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)))
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hfee : f.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat)))
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkl : 96 ≤ keyPtr.toNat) (hkb : keyPtr.toNat+160 ≤ free.toNat)
    (hpb : paramsPtr.toNat+96 ≤ free.toNat) (hplo : 96 ≤ paramsPtr.toNat)
    (hroom : free.toNat+4000 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hcd : I.calldata.size < 2^255) (hgas : g.toNat < 324518553658429321982441292826060)
    (hclean : UInt256.land rawFee (UInt256.ofNat 16777215) = fee) (hfeeBound : fee.toNat < 2^24)
    (hpaid : Cₘ aw ≤ C) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨1614⟩
      ([rawFee, before, amount, src, len, poolSlot id, paramsPtr+UInt256.ofNat 64,
        keyPtr, id, keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (swapTransition.body.drop 22) result ∧
      abiResultTrace swapTransition.returnType (deployedRuntime v) g s0 result := by
  have hfit : free.toNat+4000 < UInt256.size := by
    change _ ≤ 2^64-1 at hroom
    change _ < 2^256
    omega
  have h160 := uadd_word_ofNat_toNat free 160 (by omega)
  let pp := swapPoolParams key p amount fee
  let pre := swapPoolAliasFrame f id
  have halias := swapPoolAliasSource (evm := evm) hs
  have hcpre : pre.contract = contract := by dsimp only [pre, swapPoolAliasFrame]; exact hc
  have hkpre : pre.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "key") = false)).trans hk
  have hppre : pre.locals.get? "params" = some (swapParamsValue p) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "params") = false)).trans hp
  have hapre : pre.locals.get? "amountToSwap" = some (.int (EVM.signed amount)) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "amountToSwap") = false)).trans ha
  have hfeepre : pre.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "lpFeeOverride") = false)).trans hfee
  have hipre : pre.locals.get? "id" = some (wordBytes32Value id) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "id") = false)).trans hi
  have hdpre : pre.locals.get? "swapDelta" = some oldDelta :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "swapDelta") = false)).trans hd
  have hbpre : pre.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "hookData") = false)).trans hb
  have hbeforepre : pre.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)) :=
    (store_get_ne _ _ (by decide : (swapPoolAlias == "beforeSwapDelta") = false)).trans hbefore
  have hkey1 : PoolKeyView (swapPoolMemory mem free pp) keyPtr key :=
    ⟨hkey.slice.swapPool free pp hkl
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hkey.fits⟩
  have hparams1 := hparams.swapPool free pp hplo
    (by simpa only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil] using hpb)
  obtain ⟨aw1, k1, C1, hp1, rd1⟩ := swapPoolAllocateTrace v (by omega) hkey hparams
    hcanonical.2.2.2.1 hlimit (by omega) (by omega) hfree hpaid h
  obtain ⟨aw2, k2, C2, hp2, rd2⟩ := swapPoolSelectTrace v (by omega) hkey1 hparams1 (by omega) hclean hp1 rd1
  rcases swapWrapperCallCorrect (f := pre) (p := pp) (state := free+UInt256.ofNat 160) (params := free)
      v hstack hI hσ0 hcpre (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hipre)
      (swapPoolParams_eval hkpre hppre hapre hfeepre) (swapPoolCurrency_eval hkpre hppre)
      (swapPoolMemory_params mem free pp (by omega)) (by omega) (by omega) (by omega)
      (swapPoolMemory_free mem free pp (by omega)) hcanonical.2.2.2.1 hlimit hfeeBound hp2 "__c6" rd2 with
    hog | ⟨result, hcall, ht⟩
  · exact .inl hog
  cases result with
  | returned cf post values =>
    obtain ⟨delta, out, nextFree, aw3, k3, C3, hIp, hσp, hv, hpaid3, rd3, hm⟩ := ht
    subst values
    change ExecStmt config pre evm swapTransition.body[23]! (.ok (swapPoolCallFrame pre delta) post) at hcall
    have hassign := swapPoolDeltaSource (evm := post) (delta := delta) hdpre
    let ff := swapPoolDeltaFrame pre delta
    have hcff : ff.contract = contract := by
      dsimp only [ff, swapPoolDeltaFrame, swapPoolCallFrame]
      exact hcpre
    have hkff : ff.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "key") = false)
        (by decide : ("swapDelta" == "key") = false)).trans hkpre
    have hpff : ff.locals.get? "params" = some (swapParamsValue p) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "params") = false)
        (by decide : ("swapDelta" == "params") = false)).trans hppre
    have hbff : ff.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "hookData") = false)
        (by decide : ("swapDelta" == "hookData") = false)).trans hbpre
    have hbeforeff : ff.locals.get? "beforeSwapDelta" = some (.int (EVM.signed before)) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "beforeSwapDelta") = false)
        (by decide : ("swapDelta" == "beforeSwapDelta") = false)).trans hbeforepre
    have hkey2 : PoolKeyView out keyPtr key := ⟨hm.saved _ _ hkey1.slice hkl
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using
        (show keyPtr.toNat+160 ≤ (free+UInt256.ofNat 160).toNat by omega)), hkey.fits⟩
    have hparams2 := hm.saved _ _ hparams1 hplo
      (by simpa only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil] using
        (show paramsPtr.toNat+96 ≤ (free+UInt256.ofNat 160).toNat by omega))
    have hnlo := hm.lower
    have hnhi := hm.upper
    have hnroom : nextFree.toNat+64 ≤ solcMaxU64 := by omega
    have hnfit : nextFree.toNat+len.toNat+512 < UInt256.size := by
      change _ ≤ 2^64-1 at hnroom
      change _ < 2^256
      omega
    rcases swapAfterCorrect (f := ff) v (by omega) hIp hσp hcff hkff hpff (store_get_self _ _ _)
        hbff hbeforeff hkey2 hparams2 hcanonical hlimit hkl (by omega) (by omega) hplo
        hnfit hnroom hsrc hgas hpaid3 hm.freeLoad rd3 with hog | ⟨final, hafter, htrace⟩
    · exact .inl hog
    · exact .inr ⟨final, ExecBlock.consNormal halias (ExecBlock.consNormal hcall
        (ExecBlock.consNormal hassign hafter)), htrace⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consNormal halias (ExecBlock.consRevert hcall), ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consNormal halias (ExecBlock.consStatic hcall), ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
