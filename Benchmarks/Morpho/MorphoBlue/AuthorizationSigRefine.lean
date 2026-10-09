import Benchmarks.Morpho.MorphoBlue.AuthorizationSigVerifySource
import Benchmarks.Morpho.MorphoBlue.RawReturnBlockRefines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoAuthorizationSignatureRefine {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 evm : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (locals : Store)
    (hc : a.Canonical) (hcd : 260 ≤ ee.calldata.size)
    (hl : AuthorizationLocals a ee.calldata locals) (hs : SourceState s0 ee σ evm)
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6120)
      (authorizationHashTail R) (authorizationCheckedMem a) aw out σ k C) :
    RawReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := immStore v } evm
      (setAuthorizationWithSigTransition.body.drop 14) := by
  have p0 := morphoAuthorizationHashSource v a ee.calldata locals evm hc hl
  have hl0 := authorizationHashLocals_authorization (v := v) hl
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationStruct (v := v) a hc hstack h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoAuthorizationDigest (v := v) a hstack rd1
  by_cases hv : (signatureRecoveryWord ee.calldata).toNat < 256
  swap
  · exact .reverted (p0.run (morphoAuthorizationSignatureSourceRevert hl0 (immStore v) evm hcd hv))
      (morphoAuthorizationSignatureDecodeRevert (v := v) a hstack hv rd2)
  have p1 := morphoAuthorizationSignatureSource hl0 (immStore v) evm hcd hv
  let l1 := authorizationSignatureLocals (authorizationHashLocals locals v a) ee.calldata
  have hl1 : AuthorizationLocals a ee.calldata l1 :=
    (hl0.insert "signature" _ (by decide)).insert "precompile" _ (by decide)
  have hd : l1.get? "digest" = some (wordBytes32Value (authorizationDigest v a)) := by
    dsimp only [l1, authorizationSignatureLocals, authorizationHashLocals]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hsig : l1.get? "signature" = some (signatureValue ee.calldata) := by
    dsimp only [l1, authorizationSignatureLocals]
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hp : l1.get? "precompile" = some (.address (AccountAddress.ofNat 1)) :=
    store_get_self _ _ _
  obtain ⟨a3, k3, C3, rd3⟩ := morphoAuthorizationSignatureDecode (v := v) a hstack hv rd2
  obtain ⟨gasArg, a4, k4, C4, rd4⟩ := morphoAuthorizationRecoveryInput (v := v) a hstack rd3
  obtain ⟨evm5, z, ret, a5, k5, C5, hcall, hs5, ho, rd5⟩ :=
    morphoAuthorizationRecoveryCall (v := v) a hs hstack rd4
  have p2 := morphoAuthorizationRecoverySource v a ee.calldata l1 (immStore v)
    evm evm5 z ret hd hsig hp hcall
  have p3 : StateBlock config { contract := contract, locals := locals, immutables := immStore v }
      evm (setAuthorizationWithSigTransition.body.drop 14)
      { contract := contract, locals := authorizationRecoveredLocals l1 z ret, immutables := immStore v }
      evm5 (setAuthorizationWithSigTransition.body.drop 19) :=
    ⟨fun tail ↦ p0.run (p1.run (ExecBlock.consNormal p2 tail))⟩
  have hl5 : AuthorizationLocals a ee.calldata (authorizationRecoveredLocals l1 z ret) :=
    (hl1.insert "success" _ (by decide)).insert "recovered" _ (by decide)
  have hz : (authorizationRecoveredLocals l1 z ret).get? "success" = some (.bool z) := by
    dsimp only [authorizationRecoveredLocals]
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hret : (authorizationRecoveredLocals l1 z ret).get? "recovered" = some (.bytes ret) :=
    store_get_self _ _ _
  cases z
  · exact .reverted (p3.run (morphoAuthorizationSourceRecoveryFailed _ _ evm5 hz))
      (morphoAuthorizationRecoveryFailed (v := v) a ho hstack rd5)
  · have ps := morphoAuthorizationSourceVerify hl5 (immStore v) evm5 ret ho hc hz hret
    have pe := morphoAuthorizationSignatureVerify (v := v) a hc ho hstack rd5
    by_cases hv : AuthorizationSignatureValid a ret
    · rw [if_pos hv] at ps pe
      obtain ⟨a6, k6, C6, rd6⟩ := pe
      have hl6 := authorizationSignatoryLocals_authorization hl5 ret
      exact .ok (p3.run (ps.run (morphoAuthorizationSourceFinish hl6 (immStore v) evm5 hc)))
        (authorizationFinalSourceState hs5 a)
        (morphoAuthorizationFinish (v := v) a hc ho hstack hperm rd6)
    · rw [if_neg hv] at ps pe
      exact .reverted (p3.run ps) pe

end Benchmarks.Morpho.MorphoBlue
