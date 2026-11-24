import Benchmarks.Safe.V3_77901a5.SignatureContext
import Benchmarks.Safe.V3_77901a5.P256Source

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

def signatureP256Body : List Stmt :=
  match signatureLoopBody[4]! with
  | .ite _ _ [.ite _ _ [.ite _ body _]] => body
  | _ => []

def signatureP256Input (p : SignatureInput) (s : UInt256) : P256Input :=
  ⟨p.hash, calldataWord p.signatures s.toNat, calldataWord p.signatures (s.toNat + 32),
    calldataWord p.signatures (s.toNat + 64), calldataWord p.signatures (s.toNat + 96)⟩

def p256SignerWord (p : P256Input) : UInt256 := uInt256OfByteArray (KEC (wordBytes [p.qx, p.qy]))

def signatureP256OffsetFrame (f : Frame) (r s : UInt256) : Frame :=
  signatureDynamicFrame f r s "p256Offset"

def signatureP256EndFrame (f : Frame) (r s : UInt256) : Frame :=
  signatureSet (signatureP256OffsetFrame f r s) "p256End" (.int (Int.ofNat (s.toNat + 128)))

theorem SignatureCore.p256Offset {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) :
    SignatureCore p (signatureP256OffsetFrame f r s) := (hc.current r).set _ _ (by decide)

theorem SignatureCore.p256End {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) :
    SignatureCore p (signatureP256EndFrame f r s) := (hc.p256Offset r s).set _ _ (by decide)

theorem signatureP256Locals {f : Frame} {evm : EVM.State} {r s : UInt256} {old : Value}
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old) :
    ExecBlock fork config f evm (signatureP256Body.take 2)
      (.ok (signatureP256OffsetFrame f r s) evm) := signatureDynamicLocals "p256Offset" hr hs ho

theorem signatureP256EndSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (hc : SignatureCore p f) (hb : s.toNat + 128 < UInt256.size) :
    ExecStmt fork config (signatureP256OffsetFrame f r s) evm signatureP256Body[3]!
      (.ok (signatureP256EndFrame f r s) evm) := by
  have he : (s + (⟨128⟩ : UInt256)).toNat = s.toNat + 128 := addWord_toNat _ _ hb
  have ha := safeInternalAdd (fork := fork) (caller := signatureP256OffsetFrame f r s) (evm := evm)
    (lhs := .var "p256Offset") (rhs := .intLit 128) (retVar := "p256End")
    (a := s) (b := ⟨128⟩) (hc.p256Offset r s).contract
    (evalLocalValue (by simp [signatureP256OffsetFrame, signatureDynamicFrame, signatureSet,
      Std.HashMap.getElem_insert])) (by simp [evalExpr?]; rfl) hb
  simpa only [uint256Value, he] using ha

theorem signatureP256EndBound {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (hc : SignatureCore p f) :
    evalExpr? config (signatureP256EndFrame f r s) evm
      (leE (.var "p256End") (localLength "signatures")) =
      .ok (.bool (decide (s.toNat + 128 ≤ p.signatures.size))) := by
  apply naturalLeSource
  · exact evalLocalValue (by simp [signatureP256EndFrame, signatureSet,
      Std.HashMap.getElem_insert])
  · exact evalLocalBytesLength (hc.p256End r s).signatures

theorem signatureP256Prefix {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hl : p.requiredBytes ≤ s.toNat) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : p.signatures.size < UInt256.size) :
    ExecBlock fork config f evm (signatureP256Body.take 5)
      (.ok (signatureP256EndFrame f r s) evm) := by
  have htail : ExecBlock fork config (signatureP256OffsetFrame f r s) evm
      ((signatureP256Body.drop 2).take 3) (.ok (signatureP256EndFrame f r s) evm) :=
    .consNormal (.requireTrue (by
      simpa only [hl, decide_true] using
        evalSignatureOffsetBound (evm := evm) (r := r) (s := s) "p256Offset" hc (by decide)))
      (.consNormal (signatureP256EndSource hc (by omega))
        (.consNormal (.requireTrue (by
          simpa only [hh, decide_true] using
            signatureP256EndBound (evm := evm) (r := r) (s := s) hc)) .nil))
  exact execBlock_append_ok (signatureP256Locals hr hs ho) htail

theorem signatureP256BoundsFailed {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hbad : ¬(p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size)) :
    ExecBlock fork config f evm signatureP256Body .reverted := by
  have hprefix := signatureP256Locals (fork := fork) (evm := evm) hr hs ho
  have htail : ExecBlock fork config (signatureP256OffsetFrame f r s) evm
      (signatureP256Body.drop 2) .reverted := by
    by_cases hl : p.requiredBytes ≤ s.toNat
    swap
    · exact .consRevert (.requireFalse (by
        simpa only [hl, decide_false] using
          evalSignatureOffsetBound (evm := evm) (r := r) (s := s) "p256Offset" hc (by decide)))
    apply ExecBlock.consNormal (.requireTrue (by
      simpa only [hl, decide_true] using
        evalSignatureOffsetBound (evm := evm) (r := r) (s := s) "p256Offset" hc (by decide)))
    by_cases hb : s.toNat + 128 < UInt256.size
    · exact .consNormal (signatureP256EndSource hc hb) (.consRevert (.requireFalse (by
        simpa only [show ¬s.toNat + 128 ≤ p.signatures.size from fun h ↦ hbad ⟨hl, h⟩,
          decide_false] using signatureP256EndBound (evm := evm) (r := r) (s := s) hc)))
    · apply ExecBlock.consRevert
      apply safeInternalAddOverflow (a := s) (b := ⟨128⟩) (hc.p256Offset r s).contract
      · exact evalLocalValue (by simp [signatureP256OffsetFrame, signatureDynamicFrame,
          signatureSet, Std.HashMap.getElem_insert])
      · simp [evalExpr?]; rfl
      · exact Nat.le_of_not_gt hb
  simpa only [List.take_append_drop] using execBlock_append_ok hprefix htail

end Benchmarks.Safe.V3_77901a5
