import Benchmarks.Morpho.MorphoBlue.AuthorizationSigFinishSource
import Benchmarks.Morpho.MorphoBlue.WordComparisons
import Benchmarks.Morpho.MorphoBlue.LocalBytesGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationSignatoryLocals (locals : Store) (out : ByteArray) : Store :=
  let base := locals.insert "signatory" (.address (AccountAddress.ofNat 0))
  if out.size = 0 then base
  else base.insert "signatory" (.address (AccountAddress.ofNat (ecrecoverWord out).toNat))

theorem authorizationSignatoryLocals_get (locals : Store) (out : ByteArray) :
    (authorizationSignatoryLocals locals out).get? "signatory" =
      some (.address (AccountAddress.ofNat (ecrecoverWord out).toNat)) := by
  by_cases hz : out.size = 0
  · simp only [authorizationSignatoryLocals, hz, ↓reduceIte, ecrecoverWord, store_get_self]; rfl
  · simp only [authorizationSignatoryLocals, hz, ↓reduceIte, store_get_self]

theorem authorizationSignatoryLocals_authorization {a cd locals}
    (hl : AuthorizationLocals a cd locals) (out : ByteArray) :
    AuthorizationLocals a cd (authorizationSignatoryLocals locals out) := by
  unfold authorizationSignatoryLocals
  split
  · exact hl.insert _ _ (by decide)
  · exact (hl.insert _ _ (by decide)).insert _ _ (by decide)

theorem morphoAuthorizationSourceSignatory {a cd locals}
    (hl : AuthorizationLocals a cd locals) (imms : Store) (evm : EVM.State)
    (out : ByteArray) (ho : EcrecoverOutput out)
    (hz : locals.get? "success" = some (.bool true))
    (hout : locals.get? "recovered" = some (.bytes out)) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 19)
      { contract := contract, locals := authorizationSignatoryLocals locals out, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 22) := by
  have p : ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 19)
      {
        contract := contract, locals := locals.insert "signatory" (.address (AccountAddress.ofNat 0)), immutables := imms }
      (setAuthorizationWithSigTransition.body.drop 21) :=
    (ABlock.start.requireStep (by simp only [evalExpr?, hz, EvalResult.ofOption])).letStep
      (by simp only [evalExpr?, bind, EvalResult.bind, pure]; rfl)
  have hout' : (locals.insert "signatory" (.address (AccountAddress.ofNat 0))).get? "recovered" =
      some (.bytes out) := by rw [store_get_ne _ _ (by decide)]; exact hout
  have he : evalExpr? config {
      contract := contract, locals := locals.insert "signatory" (.address (AccountAddress.ofNat 0)), immutables := imms }
      evm (.binary .ne (.arrayLength .localVar ⟨"recovered", []⟩) (.intLit 0)) =
      .ok (.bool (decide (out.size ≠ 0))) := evalLocalBytesLengthNeZero hout'
  refine ⟨fun hr ↦ p.run (ExecBlock.consNormal ?_ hr)⟩
  rcases ho.size with hs | hs
  · simp only [authorizationSignatoryLocals, hs, ↓reduceIte]
    exact ExecStmt.iteFalse (by simpa only [hs, ne_eq, not_true_eq_false, decide_false] using he) .nil
  · simp only [authorizationSignatoryLocals, hs, show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
    apply ExecStmt.iteTrue (by simpa only [hs] using he)
    apply ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalWord (store_get_self _ _ _))) .nil
    rw [evalExpr?]
    have he' : evalExpr? config {
        contract := contract, locals := locals.insert "signatory" (.address (AccountAddress.ofNat 0)), immutables := imms }
        evm (.var "recovered") = .ok (.bytes out) := by
      simp only [evalExpr?, hout', EvalResult.ofOption]
    rw [he']
    simp only [bind, EvalResult.bind, show config.abiDecodeMode = .modern from rfl,
      decodeAddressWord32 hs (ho.canonical hs), ecrecoverWord, hs,
      show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
    rfl

theorem morphoAuthorizationSourceRecoveryFailed (locals imms : Store) (evm : EVM.State)
    (hz : locals.get? "success" = some (.bool false)) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (setAuthorizationWithSigTransition.body.drop 19) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse
    (by simp only [evalExpr?, hz, EvalResult.ofOption]))

theorem morphoAuthorizationSourceVerify {a cd locals}
    (hl : AuthorizationLocals a cd locals) (imms : Store) (evm : EVM.State)
    (out : ByteArray) (ho : EcrecoverOutput out) (hc : a.Canonical)
    (hz : locals.get? "success" = some (.bool true))
    (hout : locals.get? "recovered" = some (.bytes out)) :
    if AuthorizationSignatureValid a out then
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (setAuthorizationWithSigTransition.body.drop 19)
        { contract := contract, locals := authorizationSignatoryLocals locals out, immutables := imms }
        (setAuthorizationWithSigTransition.body.drop 24)
    else ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (setAuthorizationWithSigTransition.body.drop 19) .reverted := by
  have p := morphoAuthorizationSourceSignatory hl imms evm out ho hz hout
  have he : evalExpr? config
      { contract := contract, locals := authorizationSignatoryLocals locals out, immutables := imms }
      evm (.var "signatory") = .ok (.address (AccountAddress.ofNat (ecrecoverWord out).toNat)) := by
    simp only [evalExpr?, authorizationSignatoryLocals_get, EvalResult.ofOption]
  have hn := evalCanonicalAddressNeZero (word := ecrecoverWord out) ho.wordCanonical he
  change evalExpr? config _ _ _ = .ok (.bool (decide (ecrecoverWord out ≠ UInt256.ofNat 0))) at hn
  have hl' := authorizationSignatoryLocals_authorization hl out
  have ha : evalExpr? config
      { contract := contract, locals := authorizationSignatoryLocals locals out, immutables := imms }
      evm (.tupleGet (.var "authorization") 0) =
      .ok (.address (AccountAddress.ofNat a.authorizer.toNat)) := by
    simpa only [AuthorizationWords.fieldValue] using hl'.evalField imms evm ⟨0, by decide⟩
  have heq : evalExpr? config
      { contract := contract, locals := authorizationSignatoryLocals locals out, immutables := imms }
      evm (.binary .eq (.tupleGet (.var "authorization") 0) (.var "signatory")) =
      .ok (.bool (decide (a.authorizer = ecrecoverWord out))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, he]
    simp only [bind, EvalResult.bind, pure, evalBinaryOp?]
    rw [canonicalAddress_beq _ _ hc.1 ho.wordCanonical]
  by_cases hnonzero : ecrecoverWord out ≠ UInt256.ofNat 0
  · have p1 := p.requireStep (hn.trans (by rw [decide_eq_true hnonzero]))
    by_cases hequal : a.authorizer = ecrecoverWord out
    · rw [if_pos (show AuthorizationSignatureValid a out from ⟨hnonzero, hequal⟩)]
      exact p1.requireStep (by simpa only [hequal, decide_true] using heq)
    · rw [if_neg (show ¬ AuthorizationSignatureValid a out from fun h ↦ hequal h.2)]
      exact p1.requireRevert (by simpa only [hequal, decide_false] using heq)
  · rw [if_neg (show ¬ AuthorizationSignatureValid a out from fun h ↦ hnonzero h.1)]
    exact p.requireRevert (by simpa only [hnonzero, decide_false] using hn)

end Benchmarks.Morpho.MorphoBlue
