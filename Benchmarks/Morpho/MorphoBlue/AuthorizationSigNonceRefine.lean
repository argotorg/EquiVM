import Benchmarks.Morpho.MorphoBlue.AuthorizationSigNonceStore
import Benchmarks.Morpho.MorphoBlue.WordComparisons

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive AuthorizationNonceRefines (v : MorphoImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (a : AuthorizationWords) (cd : ByteArray)
    (locals imms : Store) (evm : State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (setAuthorizationWithSigTransition.body.drop 10) .reverted →
      RDrev (deployedRuntime v) g s0 → AuthorizationNonceRefines v ee g s0 a cd locals imms evm R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (setAuthorizationWithSigTransition.body.drop 10) .staticViolation →
      RDstatic (deployedRuntime v) g s0 → AuthorizationNonceRefines v ee g s0 a cd locals imms evm R
  | ok {locals' evm' σ' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (setAuthorizationWithSigTransition.body.drop 10)
        { contract := contract, locals := locals', immutables := imms } evm'
        (setAuthorizationWithSigTransition.body.drop 14) →
      AuthorizationLocals a cd locals' → SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6120) (authorizationHashTail R)
        (authorizationCheckedMem a) aw' out' σ' k' C' →
      AuthorizationNonceRefines v ee g s0 a cd locals imms evm R

theorem morphoAuthorizationNonceRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (cd : ByteArray)
    (locals imms : Store) (hc : a.Canonical) (hl : AuthorizationLocals a cd locals)
    (hs : SourceState s0 ee σ evm) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5940)
      (authorizationDecodedStack a R) (authorizationDecodedMem a) aw out σ k C) :
    AuthorizationNonceRefines v ee g s0 a cd locals imms evm R := by
  have ht := hl.evalTimestamp imms evm
  rw [hs.env] at ht
  by_cases htime : (UInt256.ofNat ee.header.timestamp).toNat ≤ a.deadline.toNat
  swap
  · exact .reverted (ExecBlock.consRevert (ExecStmt.requireFalse
      (by simpa only [htime, decide_false] using ht)))
      (morphoAuthorizationTimestampRevert (v := v) a (by omega) htime h)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationTimestampOk (v := v) a (by omega) htime h
  have pref : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 10)
      { contract := contract, locals := locals, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 11) :=
    ABlock.start.requireStep (by simpa only [htime, decide_true] using ht)
  let n := authorizationUsedNonce a σ ee
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"nonce", [.mindex (.tupleGet (.var "authorization") 0)]⟩) =
      .ok (.int (Int.ofNat n.toNat)) := by
    simpa only [hs.env, ← hs.accounts] using hl.evalNonce imms evm hc
  have pref1 := pref.letStep he
  by_cases hfit : n.toNat + 1 < UInt256.size
  swap
  · exact .reverted (pref1.run (morphoAuthorizationNonceSourceOverflow _ evm n (by omega)))
      (morphoAuthorizationNonceOverflow (v := v) a hc hstack (by exact Nat.le_of_not_gt hfit) rd1)
  obtain ⟨a2, k2, C2, rd2⟩ := morphoAuthorizationNonceIncrement (v := v) a hc hstack hfit rd1
  have hl1 := hl.insert "usedNonce" (.int (Int.ofNat n.toNat)) (by decide)
  let evm1 := storeAuthorizationNonce evm a (n + UInt256.ofNat 1)
  have hass : ExecStmt config
      (authorizationUsedFrame { contract := contract, locals := locals, immutables := imms } n)
      evm setAuthorizationWithSigTransition.body[12]!
      (.ok (authorizationUsedFrame { contract := contract, locals := locals, immutables := imms } n) evm1) :=
    ExecStmt.assign (morphoAuthorizationNonceSourceExpr _ evm n hfit)
      (hl1.assignNonce imms evm hc _)
  by_cases hperm : ee.perm = true
  swap
  · have hpf : ee.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .static (pref1.run (ExecBlock.consStatic (execStmt_assign_static hass
      (by rw [hs.env]; exact hpf))))
      (morphoAuthorizationNonceStoreStatic (v := v)
        (R := [n, a.nonce, UInt256.ofNat 6120] ++ authorizationHashTail R)
        (by simp [authorizationHashTail]; omega) hpf rd2)
  have pref2 := (StateBlock.ofABlock pref1).step hass
  have haEval : evalExpr? config
      (authorizationUsedFrame { contract := contract, locals := locals, immutables := imms } n)
      evm1 (.tupleGet (.var "authorization") 3) = .ok (.int (Int.ofNat a.nonce.toNat)) :=
    by simpa only [AuthorizationWords.fieldValue] using hl1.evalField imms evm1 ⟨3, by decide⟩
  have hnEval := evalWordEqWord haEval
    (authorizationUsedFrame_eval { contract := contract, locals := locals, immutables := imms } evm1 n)
  by_cases hn : a.nonce = n
  swap
  · exact .reverted (pref2.reverts (ExecStmt.requireFalse
      (by simpa only [hn, decide_false] using hnEval)))
      (morphoAuthorizationNonceStoreRevert (v := v) a hstack hperm hn rd2)
  obtain ⟨a3, k3, C3, rd3⟩ := morphoAuthorizationNonceStoreOk (v := v) a hstack hperm hn rd2
  have hs1 : SourceState s0 ee (authorizationNonceAccounts a n σ ee) evm1 := by
    simpa only [evm1, storeAuthorizationNonce, hs.env] using
      hs.storageWrite (authorizationNonceSlot a) (n + UInt256.ofNat 1)
  exact .ok (pref2.step (ExecStmt.requireTrue (by simpa only [hn, decide_true] using hnEval)))
    hl1 hs1 hperm rd3

end Benchmarks.Morpho.MorphoBlue
