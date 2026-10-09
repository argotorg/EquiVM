import Benchmarks.Safe.SignatureP256Pieces
import Benchmarks.Safe.ModuleStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureP256Valid (owner : UInt256) (input : P256Input) : Prop :=
  UInt256.land solcAddrMask owner = UInt256.land solcAddrMask (signatureP256Signer input)

instance (owner : UInt256) (input : P256Input) : Decidable (signatureP256Valid owner input) :=
  inferInstanceAs (Decidable (UInt256.land solcAddrMask owner =
    UInt256.land solcAddrMask (signatureP256Signer input)))

theorem evalSignatureP256SignerCondition {f : Frame} {evm : EVM.State} {owner : UInt256}
    {q : P256Input} (ho : f.locals["currentOwner"]? =
      some (.address (AccountAddress.ofUInt256 owner))) :
    evalExpr? config (signatureP256SignerFrame f q) evm
      (eqE (.var "currentOwner") (.var "signerAddress")) =
      .ok (.bool (decide (signatureP256Valid owner q))) := by
  have hm (w : UInt256) : (UInt256.land solcAddrMask w).toNat < EVM.addressModulus := by
    rw [u256_land_comm]; exact solcAddrMask_result_canonical w
  apply evalAddressEq (hm owner) (hm (signatureP256Signer q))
  · have he : evalExpr? config (signatureP256SignerFrame f q) evm (.var "currentOwner") =
        .ok (.address (AccountAddress.ofUInt256 owner)) := evalLocalValue (by
      simp [signatureP256SignerFrame, signatureP256WordsFrame, signatureP256XFrame,
        signatureP256SFrame, signatureP256RFrame, signatureSet, Std.HashMap.getElem?_insert, ho])
    rw [he, accountAddress_ofUInt256_eq_ofNat_toNat, addressOfNat_eq_of_masked_word owner,
      u256_land_comm owner solcAddrMask]
  · have he : evalExpr? config (signatureP256SignerFrame f q) evm (.var "signerAddress") =
        .ok (.address (AccountAddress.ofUInt256 (signatureP256Signer q))) := evalLocalValue (by
      simp [signatureP256SignerFrame, signatureSet, Std.HashMap.getElem?_insert])
    rw [he, accountAddress_ofUInt256_eq_ofNat_toNat,
      addressOfNat_eq_of_masked_word (signatureP256Signer q), u256_land_comm]

theorem safeInternalP256 {p : SignatureInput} {f : Frame} {evm evm' : EVM.State}
    {q : P256Input} {z : Bool} {out : ByteArray} (hc : SignatureCore p f) (hq : q.h = p.hash)
    (hbody : ExecFuncBody config (p256Frame q) evm p256VerifyFunction.body
      (.returned (p256FinalFrame q z out) evm' (some [.bool (p256Result z out)]))) :
    ExecStmt config (signatureP256SignerFrame f q) evm signatureP256Body[11]!
      (.ok (signatureSet (signatureP256SignerFrame f q) "p256Ok" (.bool (p256Result z out)))
        evm') := by
  apply internalCallFunctionReturn (callee := p256VerifyFunction)
    (argVals := [wordBytes32Value q.h, wordBytes32Value q.r, wordBytes32Value q.s,
      uint256Value q.qx, uint256Value q.qy]) (locals := p256Args q)
    (calleeSolm := p256FinalFrame q z out) (value := some [.bool (p256Result z out)])
  · simp [evalExprs?, evalExpr?, signatureP256SignerFrame, signatureP256WordsFrame,
      signatureP256XFrame, signatureP256SFrame, signatureP256RFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hc.hash, hq,
      EvalResult.ofOption, EvalResult.bind, bind, pure]
  · rw [(hc.p256Signer q).contract]; rfl
  · rfl
  · convert hbody using 1
    simp only [signatureP256SignerFrame, signatureP256WordsFrame, signatureP256XFrame,
      signatureP256SFrame, signatureP256RFrame, signatureSet, p256Frame, hc.contract, hc.immutables]

theorem signatureP256SourceSignerFailed {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {off owner : UInt256} (hc : SignatureCore p f)
    (hoff : f.locals["p256Offset"]? = some (uint256Value off))
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)))
    (hb : off.toNat + 128 ≤ p.signatures.size)
    (hv : ¬signatureP256Valid owner (signatureP256Input p off)) :
    ExecBlock config f evm (signatureP256Body.drop 5) .reverted := by
  have hpieces := signatureP256PiecesSource (evm := evm) hc hoff hb
  have htail : ExecBlock config (signatureP256WordsFrame f (signatureP256Input p off)) evm
      (signatureP256Body.drop 9) .reverted :=
    .consNormal (signatureP256SignerSource _ _ _)
      (.consRevert (.requireFalse (by simpa only [hv, decide_false] using
        evalSignatureP256SignerCondition (evm := evm) (q := signatureP256Input p off) ho)))
  exact execBlock_append_ok hpieces htail

theorem signatureP256SourceVerified {p : SignatureInput} {f : Frame} {evm evm' : EVM.State}
    {off owner : UInt256} {z : Bool} {out : ByteArray} (hc : SignatureCore p f)
    (hoff : f.locals["p256Offset"]? = some (uint256Value off))
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)))
    (hb : off.toNat + 128 ≤ p.signatures.size)
    (hv : signatureP256Valid owner (signatureP256Input p off))
    (hcall : callViaEVM evm (AccountAddress.ofNat 256) 0
      (wordBytes (p256Words (signatureP256Input p off))) (z, evm', out) false) :
    ExecBlock config f evm (signatureP256Body.drop 5)
      (if p256Result z out then .ok
        (signatureSet (signatureP256SignerFrame f (signatureP256Input p off)) "p256Ok" (.bool true))
        evm' else .reverted) := by
  have hpieces := signatureP256PiecesSource (evm := evm) hc hoff hb
  have hsigner := signatureP256SignerSource f evm (signatureP256Input p off)
  have hvalid := evalSignatureP256SignerCondition (evm := evm) (q := signatureP256Input p off) ho
  have hverify := safeInternalP256 hc (by rfl) (safeP256Source hcall)
  have htail : ExecBlock config (signatureP256WordsFrame f (signatureP256Input p off)) evm
      (signatureP256Body.drop 9)
      (if p256Result z out then .ok
        (signatureSet (signatureP256SignerFrame f (signatureP256Input p off)) "p256Ok" (.bool true))
        evm' else .reverted) := by
    apply ExecBlock.consNormal hsigner
    apply ExecBlock.consNormal (.requireTrue (by simpa only [hv, decide_true] using hvalid))
    cases he : p256Result z out with
    | false =>
        rw [he] at hverify
        exact .consNormal hverify (.consRevert (.requireFalse (evalLocalValue (by
          simp [signatureSet, Std.HashMap.getElem?_insert]))))
    | true =>
        rw [he] at hverify
        exact .consNormal hverify (.consNormal (.requireTrue (evalLocalValue (by
          simp [signatureSet, Std.HashMap.getElem?_insert]))) .nil)
  exact execBlock_append_ok hpieces htail

end Benchmarks.Safe
