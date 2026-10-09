import Benchmarks.Safe.SignatureOffsetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureP256Body : List Stmt :=
  match signatureLoopBody[4]! with
  | .ite _ _ [.ite _ _ [.ite _ body _]] => body
  | _ => []

def signatureP256OffsetFrame (f : Frame) (r s : UInt256) : Frame :=
  signatureDynamicFrame f r s "p256Offset"

def signatureP256EndFrame (f : Frame) (r s : UInt256) : Frame :=
  signatureSet (signatureP256OffsetFrame f r s) "p256End" (.int (Int.ofNat (s.toNat + 128)))

theorem SignatureCore.p256Offset {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) : SignatureCore p (signatureP256OffsetFrame f r s) :=
  (hc.current r).set _ _ (by decide)

theorem SignatureCore.p256End {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) : SignatureCore p (signatureP256EndFrame f r s) :=
  (hc.p256Offset r s).set _ _ (by decide)

theorem signatureP256EndSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (hc : SignatureCore p f) (hb : s.toNat + 128 < UInt256.size) :
    ExecStmt config (signatureP256OffsetFrame f r s) evm
      (.internalCall "_add" [.var "p256Offset", .intLit 128] "p256End")
      (.ok (signatureP256EndFrame f r s) evm) := by
  have he : (s + (⟨128⟩ : UInt256)).toNat = s.toNat + 128 := addWord_toNat _ _ hb
  have h := safeInternalAdd (evm := evm) (hc.p256Offset r s).contract
    (a := s) (b := ⟨128⟩) (lhs := .var "p256Offset") (rhs := .intLit 128) (retVar := "p256End")
    (evalLocalValue (by simp [signatureP256OffsetFrame, signatureDynamicFrame,
      signatureSet, Std.HashMap.getElem?_insert])) (by simp [evalExpr?]; rfl) hb
  simpa only [uint256Value, he] using h

theorem evalSignatureP256EndBound {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (hc : SignatureCore p f) :
    evalExpr? config (signatureP256EndFrame f r s) evm
      (leE (.var "p256End") (localLength "signatures")) =
      .ok (.bool (decide (s.toNat + 128 ≤ p.signatures.size))) := by
  apply naturalLeSource
  · exact evalLocalValue (by
      simp [signatureP256EndFrame, signatureSet, Std.HashMap.getElem?_insert])
  · exact evalLocalBytesLength (hc.p256End r s).signatures

theorem signatureP256SourcePrefix {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hl : p.requiredBytes ≤ s.toNat) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hn : p.signatures.size < UInt256.size) :
    ExecBlock config f evm (signatureP256Body.take 5) (.ok (signatureP256EndFrame f r s) evm) := by
  have hp := signatureDynamicLocals (evm := evm) "p256Offset" hr hs ho
  have hg := evalSignatureOffsetBound (evm := evm) (r := r) (s := s) "p256Offset" hc (by decide)
  have he := evalSignatureP256EndBound (evm := evm) (r := r) (s := s) hc
  have ht : ExecBlock config (signatureP256OffsetFrame f r s) evm
      ((signatureP256Body.take 5).drop 2) (.ok (signatureP256EndFrame f r s) evm) :=
    .consNormal (.requireTrue (by simpa only [hl, decide_true] using hg))
      (.consNormal (signatureP256EndSource hc (by omega))
        (.consNormal (.requireTrue (by simpa only [hh, decide_true] using he)) .nil))
  exact execBlock_append_ok hp ht

theorem signatureP256SourceBoundsFailed {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hb : ¬(p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size)) :
    ExecBlock config f evm signatureP256Body .reverted := by
  have hp := signatureDynamicLocals (evm := evm) "p256Offset" hr hs ho
  have hg := evalSignatureOffsetBound (evm := evm) (r := r) (s := s) "p256Offset" hc (by decide)
  have ht : ExecBlock config (signatureP256OffsetFrame f r s) evm
      (signatureP256Body.drop 2) .reverted := by
    by_cases hl : p.requiredBytes ≤ s.toNat
    swap
    · exact .consRevert (.requireFalse (by simpa only [hl, decide_false] using hg))
    apply ExecBlock.consNormal (.requireTrue (by simpa only [hl, decide_true] using hg))
    by_cases hfit : s.toNat + 128 < UInt256.size
    · have hh : ¬s.toNat + 128 ≤ p.signatures.size := fun hh ↦ hb ⟨hl, hh⟩
      exact .consNormal (signatureP256EndSource hc hfit)
        (.consRevert (.requireFalse (by
          simpa only [hh, decide_false] using
            evalSignatureP256EndBound (evm := evm) (r := r) (s := s) hc)))
    · exact .consRevert (safeInternalAddOverflow (hc.p256Offset r s).contract
        (a := s) (b := ⟨128⟩) (evalLocalValue (by simp [signatureP256OffsetFrame,
          signatureDynamicFrame, signatureSet, Std.HashMap.getElem?_insert]))
        (by simp [evalExpr?]; rfl) (by change UInt256.size ≤ s.toNat + 128; omega))
  exact execBlock_append_ok hp ht

end Benchmarks.Safe
