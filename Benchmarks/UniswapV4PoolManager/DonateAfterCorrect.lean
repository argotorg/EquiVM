import Benchmarks.UniswapV4PoolManager.AfterDonateHookTrace
import Benchmarks.UniswapV4PoolManager.DonateHookSource
import Benchmarks.UniswapV4PoolManager.SignedResultTrace
import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.ABIResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateAfterCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len delta junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hkey : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ free.toNat)
    (hfit : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0
      (if I.source = AccountAddress.ofNat key.hooks.toNat then ⟨10381⟩ else ⟨10391⟩)
      (key.hooks :: amount1 :: keyPtr :: src :: key.hooks :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 19) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hw : accountWord hook = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
  rcases afterDonateHookTrace (hook := hook) f v hstack hI hσ0 hkey hc hkb hlo hfit hsrc hgas hpaid hfree
      (by rw [hw]; exact h) with hog | ⟨post, z, out, hcall, ht⟩
  · exact .inl hog
  have he := evalLocalValue (cfg := config) (evm := evm) hk
  have hs := donateHookCall true hf (evalStructField he (field := "hooks") rfl) he
    (evalLocalValue h0) (evalLocalValue h1) (evalLocalValue hb) hc
    (by simpa only [hI, donateHookFlag] using hcall) "__c8"
  simp only [hI, donateHookFlag, if_true] at hs
  generalize hx : hookInvocationResult f evm post (hookEnabled I.source hook ⟨16⟩) z
    (donateHookPayload true I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat))) out = result at hs ht
  cases result with
  | returned cf post values =>
    obtain ⟨rfl, hr⟩ := ht
    change ExecStmt config f evm donateTransition.body[19]!
      (.ok {f with locals := f.locals.insert "__c8" .unit} post) at hs
    have hreturn : ExecStmt config {f with locals := f.locals.insert "__c8" .unit} post
        donateTransition.body[20]!
        (.returned {f with locals := f.locals.insert "__c8" .unit} post (some [.int (EVM.signed delta)])) := by
      apply ExecStmt.return
      have hd' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c8" .unit})
        (evm := post) ((store_get_ne _ _ (by decide : ("__c8" == "delta") = false)).trans hd)
      simp only [evalExprs?, hd', bind, EvalResult.bind, pure]
    exact .inr ⟨_, ExecBlock.consNormal hs (ExecBlock.consReturn hreturn), delta.toByteArray, hr,
      returnEquiv_of_encode (signedReturnEncoding ⟨256, by decide⟩ delta (signedWord_fits delta))⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consRevert hs, ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
  | ok | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
