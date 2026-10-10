import Benchmarks.UniswapV4PoolManager.DonatePoolCorrect
import Benchmarks.UniswapV4PoolManager.BeforeDonateHookTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateBeforeCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len id junk : UInt256}
    {key : PoolKeyWords} {oldDelta : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+33 ≤ 1024)
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
    (hroom : free.toNat+4000 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hcd : I.calldata.size < 2^255)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+49)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10153⟩
      (keyPtr :: src :: amount1 :: amount0 :: len :: poolSlot id :: id :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 13) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hw : accountWord hook = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
  have hfit : free.toNat+len.toNat+448 < UInt256.size := by
    change _ ≤ 2^64-1 at hroom
    change _ < 2^256
    omega
  rcases beforeDonateHookTrace (hook := hook) f v hstack hI hσ0 hkey hc hw hkb (by omega)
      hfit hroom hsrc hgas hpaid hfree h with hog | ⟨post, z, out, hcall, ht⟩
  · exact .inl hog
  have he := evalLocalValue (cfg := config) (evm := evm) hk
  have hstmt := donateHookCall false hf (evalStructField he (field := "hooks") rfl) he
    (evalLocalValue h0) (evalLocalValue h1) (evalLocalValue hb) hc
    (by simpa only [hI, donateHookFlag] using hcall) "__c5"
  simp only [hI, donateHookFlag, Bool.false_eq_true, if_false] at hstmt
  generalize hx : hookInvocationResult f evm post (hookEnabled I.source hook ⟨32⟩) z
    (donateHookPayload false I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat))) out = result at hstmt ht
  cases result with
  | returned cf post values =>
    obtain ⟨hIp, hσp, rfl, out, data, nextFree, aw1, k1, C1, j0, j1, hm, hp1, rd1⟩ := ht
    let ff : Frame := {f with locals := f.locals.insert "__c5" .unit}
    change ExecStmt config f evm donateTransition.body[13]! (.ok ff post) at hstmt
    have hfff : ff.contract = contract := hf
    have hkff : ff.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne _ _ (by decide : ("__c5" == "key") = false)).trans hk
    have h0ff : ff.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c5" == "amount0") = false)).trans h0
    have h1ff : ff.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c5" == "amount1") = false)).trans h1
    have hdff : ff.locals.get? "delta" = some (oldDelta) :=
      (store_get_ne _ _ (by decide : ("__c5" == "delta") = false)).trans hd
    have hbff : ff.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) :=
      (store_get_ne _ _ (by decide : ("__c5" == "hookData") = false)).trans hb
    have hsff : ff.locals.get? "pool" = some (poolRefValue id) :=
      (store_get_ne _ _ (by decide : ("__c5" == "pool") = false)).trans hs
    have hiff : ff.locals.get? "poolId" = some (wordBytes32Value id) :=
      (store_get_ne _ _ (by decide : ("__c5" == "poolId") = false)).trans hi
    have hkey1 : PoolKeyView out keyPtr key := ⟨hm.saved _ _ hkey.slice hkl
      (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hkey.fits⟩
    have hnlo := hm.lower
    have hnroom := hm.bound
    have hnfit : nextFree.toNat+len.toNat+448 < UInt256.size := by
      change _ ≤ 2^64-1 at hnroom
      change _ < 2^256
      omega
    rcases donatePoolCorrect (f := ff) v (by omega) hIp hσp hfff hkff h0ff h1ff hdff hbff hsff hiff
        hkey1 hc (by omega) hkl hnfit hsrc hgas hp1 hm.freeLoad rd1 with hog | ⟨final, hbody, htrace⟩
    · exact .inl hog
    · exact .inr ⟨final, ExecBlock.consNormal hstmt hbody, htrace⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consRevert hstmt, ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consStatic hstmt, ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
