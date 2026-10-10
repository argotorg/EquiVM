import Benchmarks.UniswapV4PoolManager.DonateAccountingCorrect
import Benchmarks.UniswapV4PoolManager.DonatePoolSource
import Benchmarks.UniswapV4PoolManager.PoolDonateTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donatePoolCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len id junk j0 j1 : UInt256}
    {key : PoolKeyWords} {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "delta" = some oldDelta)
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hs : f.locals.get? "pool" = some (poolRefValue id))
    (hi : f.locals.get? "poolId" = some (wordBytes32Value id))
    (hkey : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hkl : 96 ≤ keyPtr.toNat)
    (hfit : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10191⟩
      (j0 :: j1 :: (keyPtr+UInt256.ofNat 128) :: keyPtr :: src :: amount1 :: amount0 :: len :: poolSlot id :: id :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 14) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  let pre := donatePoolAliasFrame f id
  have halias := donatePoolAliasSource (evm := evm) hs
  have hfpre : pre.contract = contract := by dsimp only [pre, donatePoolAliasFrame]; exact hf
  have hkpre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "key") = false)).trans hk
  have h0pre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "amount0") = false)).trans h0
  have h1pre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "amount1") = false)).trans h1
  have hdpre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "delta") = false)).trans hd
  have hbpre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "hookData") = false)).trans hb
  have hipre := (store_get_ne _ (poolRefValue id) (by decide : (donatePoolAlias == "poolId") = false)).trans hi
  obtain ⟨cf, hcall⟩ := poolDonateCall (f := pre) (evm := evm) hfpre
    (evalLocalValue (store_get_self _ _ _)) (evalLocalValue h0pre) (evalLocalValue h1pre) "__c6"
  have ht := poolDonateTrace cf v (by omega) hI h
  generalize hx : poolDonateResult cf evm id amount0 amount1 = result at hcall ht
  cases result with
  | returned cf post values =>
    obtain ⟨hIp, hσp, rfl, j0', j1', k1, C1, hp1, rd1⟩ := ht
    let delta := poolDonateDelta amount0 amount1
    change ExecStmt config pre evm donateTransition.body[15]! (.ok (donatePoolCallFrame pre delta) post) at hcall
    have hassign := donatePoolDeltaSource (f := pre) (evm := post) (delta := delta) hdpre
    let ff := donatePoolDeltaFrame pre delta
    have hfff : ff.contract = contract := by dsimp only [ff, donatePoolDeltaFrame, donatePoolCallFrame]; exact hfpre
    have hkff : ff.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "key") = false)
        (by decide : ("delta" == "key") = false)).trans hkpre
    have h0ff : ff.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "amount0") = false)
        (by decide : ("delta" == "amount0") = false)).trans h0pre
    have h1ff : ff.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "amount1") = false)
        (by decide : ("delta" == "amount1") = false)).trans h1pre
    have hbff : ff.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "hookData") = false)
        (by decide : ("delta" == "hookData") = false)).trans hbpre
    have hiff : ff.locals.get? "poolId" = some (wordBytes32Value id) :=
      (store_get_ne2 _ _ _ (by decide : ("__c6" == "poolId") = false)
        (by decide : ("delta" == "poolId") = false)).trans hipre
    rcases donateAccountingCorrect (f := ff) v hstack hIp (hσp.trans hσ0) hfff hkff h0ff h1ff
        (store_get_self _ _ _) hbff hiff hkey hc hkb hkl hfit hsrc hgas (by omega) hfree rd1 with
      hog | ⟨final, hbody, htrace⟩
    · exact .inl hog
    · exact .inr ⟨final, ExecBlock.consNormal halias (ExecBlock.consNormal hcall
        (ExecBlock.consNormal hassign hbody)), htrace⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consNormal halias (ExecBlock.consRevert hcall), ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consNormal halias (ExecBlock.consStatic hcall), ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
