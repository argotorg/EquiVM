import Benchmarks.Morpho.MorphoBlue.AuthorizationSigNonceRefine
import Benchmarks.Morpho.MorphoBlue.PackedHashSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationTypeHash : UInt256 :=
  UInt256.ofNat 58716139875033191547423680425660227735028985010655085009261943264615620979857

def AuthorizationWords.structWords (a : AuthorizationWords) : List UInt256 :=
  [authorizationTypeHash, a.authorizer, a.authorized, a.enabled, a.nonce, a.deadline]

def AuthorizationWords.structHash (a : AuthorizationWords) : UInt256 :=
  uInt256OfByteArray (KEC (returnWordBytes a.structWords))

def authorizationStructExpr : Expr := .keccak256 (.abiEncodePacked [
  (abiBytes32, .fixedBytesLit ⟨31, by decide⟩
    [129, 208, 40, 79, 176, 226, 205, 225, 141, 5, 83, 176, 97, 137, 214, 247,
      97, 60, 150, 160, 27, 181, 181, 231, 130, 142, 173, 230, 160, 220, 172, 145]),
  (abiUInt256, .cast (.tupleGet (.var "authorization") 0) (.elem (.int (.uint ⟨256, by decide⟩)))),
  (abiUInt256, .cast (.tupleGet (.var "authorization") 1) (.elem (.int (.uint ⟨256, by decide⟩)))),
  (abiUInt256, .ite (.tupleGet (.var "authorization") 2) (.intLit 1) (.intLit 0)),
  (abiUInt256, .tupleGet (.var "authorization") 3),
  (abiUInt256, .tupleGet (.var "authorization") 4)])

theorem AuthorizationLocals.evalStructHash {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (hc : a.Canonical) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      authorizationStructExpr = .ok (wordBytes32Value a.structHash) := by
  have ht : EVM.Word.toBytesBE authorizationTypeHash =
      [129, 208, 40, 79, 176, 226, 205, 225, 141, 5, 83, 176, 97, 137, 214, 247,
        97, 60, 150, 160, 27, 181, 181, 231, 130, 142, 173, 230, 160, 220, 172, 145] := by native_decide
  have he0 : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.fixedBytesLit ⟨31, by decide⟩
        [129, 208, 40, 79, 176, 226, 205, 225, 141, 5, 83, 176, 97, 137, 214, 247,
          97, 60, 150, 160, 27, 181, 181, 231, 130, 142, 173, 230, 160, 220, 172, 145]) =
      .ok (wordBytes32Value authorizationTypeHash) := by
    simp only [evalExpr?, wordBytes32Value, ht, pure]; rfl
  have ha : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "authorization") 0) = .ok (.address (AccountAddress.ofNat a.authorizer.toNat)) := by
    simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨0, by decide⟩
  have hb : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "authorization") 1) = .ok (.address (AccountAddress.ofNat a.authorized.toNat)) := by
    simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨1, by decide⟩
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.ite (.tupleGet (.var "authorization") 2) (.intLit 1) (.intLit 0)) =
      .ok (.int (Int.ofNat a.enabled.toNat)) := by
    rw [evalExpr?, hl.evalField imms evm ⟨2, by decide⟩]
    rcases hc.2.2 with hz | ho
    · simp only [AuthorizationWords.fieldValue, hz, decide_false, ne_eq, not_true_eq_false,
        bind, EvalResult.bind, ↓reduceIte, evalExpr?, pure]; rfl
    · simp only [AuthorizationWords.fieldValue, ho]
      change evalExpr? config _ evm (.intLit 1) = _
      simp only [evalExpr?, pure]; rfl
  have hn : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "authorization") 3) = .ok (.int (Int.ofNat a.nonce.toNat)) := by
    simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨3, by decide⟩
  have hd : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "authorization") 4) = .ok (.int (Int.ofNat a.deadline.toNat)) := by
    simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨4, by decide⟩
  have hp := evalPackedArgs_cons he0 (encodePacked_bytes32 _)
    (evalPackedArgs_cons (evalCastCanonicalAddress ha hc.1) (encodePacked_uint256 _)
      (evalPackedArgs_cons (evalCastCanonicalAddress hb hc.2.1) (encodePacked_uint256 _)
        (evalPackedArgs_cons he (encodePacked_uint256 _)
          (evalPackedArgs_cons hn (encodePacked_uint256 _)
            (evalPackedArgs_single hd (encodePacked_uint256 _))))))
  apply evalPackedKeccak
  simpa only [returnWordBytes_toList, AuthorizationWords.structWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc] using hp

def authorizationDigestBytes (v : MorphoImmutables) (a : AuthorizationWords) : ByteArray :=
  ⟨#[25, 1]⟩ ++ v.DOMAIN_SEPARATOR.toByteArray ++ a.structHash.toByteArray

def authorizationDigest (v : MorphoImmutables) (a : AuthorizationWords) : UInt256 :=
  uInt256OfByteArray (KEC (authorizationDigestBytes v a))

def authorizationDigestExpr : Expr := .keccak256 (.abiEncodePacked [
  (.elem (.bytes ⟨1, by decide⟩), .fixedBytesLit ⟨1, by decide⟩ [25, 1]),
  (abiBytes32, .immutable "DOMAIN_SEPARATOR"), (abiBytes32, .var "hashStruct")])

theorem evalAuthorizationDigest (v : MorphoImmutables) (a : AuthorizationWords)
    (locals : Store) (evm : EVM.State)
    (hg : locals.get? "hashStruct" = some (wordBytes32Value a.structHash)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      authorizationDigestExpr = .ok (wordBytes32Value (authorizationDigest v a)) := by
  have h0 : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.fixedBytesLit ⟨1, by decide⟩ [25, 1]) = .ok (.fixedBytes ⟨1, by decide⟩ [25, 1]) := by
    simp only [evalExpr?, pure]
  have h2 : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.var "hashStruct") = .ok (wordBytes32Value a.structHash) := by
    simp only [evalExpr?, hg, EvalResult.ofOption]
  have hp := evalPackedArgs_cons h0
    (by decide : encodePackedValue? (.elem (.bytes ⟨1, by decide⟩))
      (.fixedBytes ⟨1, by decide⟩ [25, 1]) = some [25, 1])
    (evalPackedArgs_cons (evalImmutable_DOMAIN_SEPARATOR _ _ _ _ _) (encodePacked_bytes32 _)
      (evalPackedArgs_single h2 (encodePacked_bytes32 _)))
  apply evalPackedKeccak
  simpa [authorizationDigestBytes, byteArray_toList_eq,
    toByteArray_eq_toBytesBE, List.append_assoc] using hp


def authorizationHashLocals (locals : Store) (v : MorphoImmutables)
    (a : AuthorizationWords) : Store :=
  (locals.insert "hashStruct" (wordBytes32Value a.structHash)).insert
    "digest" (wordBytes32Value (authorizationDigest v a))

theorem morphoAuthorizationHashSource (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) (locals : Store) (evm : EVM.State)
    (hc : a.Canonical) (hl : AuthorizationLocals a cd locals) :
    ABlock config evm { contract := contract, locals := locals, immutables := immStore v }
      (setAuthorizationWithSigTransition.body.drop 14)
      { contract := contract, locals := authorizationHashLocals locals v a, immutables := immStore v }
      (setAuthorizationWithSigTransition.body.drop 16) := by
  exact (ABlock.start.letStep (hl.evalStructHash (immStore v) evm hc)).letStep
    (evalAuthorizationDigest v a _ evm (store_get_self _ _ _))

theorem authorizationHashLocals_authorization {locals cd a v}
    (hl : AuthorizationLocals a cd locals) :
    AuthorizationLocals a cd (authorizationHashLocals locals v a) :=
  (hl.insert "hashStruct" _ (by decide)).insert "digest" _ (by decide)

end Benchmarks.Morpho.MorphoBlue
