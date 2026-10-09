import Benchmarks.Safe.SignatureP256Trace
import Benchmarks.Safe.SignatureContractSource
import Benchmarks.Safe.EthSignSource
import Benchmarks.Safe.SignatureOwnerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SignatureContext (p : SignatureInput) (f : Frame) (i : Nat) (last : UInt256)
    extends SignatureCore p f : Prop where
  index : f.locals["i"]? = some (.int (Int.ofNat i))
  lastOwner : f.locals["lastOwner"]? = some (.address (AccountAddress.ofUInt256 last))

theorem SignatureContext.set {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (name : Ident) (value : Value)
    (hn : name ∉ ["executor", "dataHash", "signatures", "requiredSignatures", "requiredBytes",
      "owners", "approvedHashes", "i", "lastOwner"]) :
    SignatureContext p (signatureSet f name value) i last := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  refine ⟨h.toSignatureCore.set name value (by simp [hn]), ?_, ?_⟩ <;>
    simp [signatureSet, Std.HashMap.getElem?_insert, hn, h.index, h.lastOwner]

theorem SignatureContext.initial (p : SignatureInput) :
    SignatureContext p p.loopFrame 0 ⟨0⟩ := by
  refine ⟨SignatureCore.initial p, ?_, ?_⟩ <;>
    simp [SignatureInput.loopFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  rfl

theorem SignatureContext.current {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (r : UInt256) :
    SignatureContext p (signatureCurrentFrame f r) i last := h.set _ _ (by decide)

theorem SignatureContext.split {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) :
    SignatureContext p (signatureVFrame f p.signatures i) i last :=
  (((h.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem SignatureContext.contractBranch {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (r s : UInt256) :
    SignatureContext p (signatureSet (signatureContractFrame f r s) "_contractSigOk" .unit)
      i last := ((h.current r).set _ _ (by decide)).set _ _ (by decide)

theorem SignatureContext.recovered {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (owner : UInt256) :
    SignatureContext p (signatureRecoveredFrame f owner) i last :=
  (h.set _ _ (by decide)).set _ _ (by decide)

theorem SignatureContext.eth {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (owner : UInt256) :
    SignatureContext p (signatureRecoveredFrame (signatureEthFrame f p.hash) owner) i last :=
  (h.set _ _ (by decide)).recovered owner

theorem SignatureContext.p256 {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (h : SignatureContext p f i last) (r s : UInt256) :
    SignatureContext p (signatureP256FinalFrame f p r s) i last :=
  ((((((((h.current r).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _
    (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem SignatureContext.next {p : SignatureInput} {f : Frame} {i : Nat}
    {last current : UInt256} (h : SignatureContext p f i last) :
    SignatureContext p (signatureNextFrame f current i) (i + 1) current := by
  refine ⟨(h.toSignatureCore.set _ _ (by decide)).set _ _ (by decide), ?_, ?_⟩ <;>
    simp [signatureNextFrame, signatureSet, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

end Benchmarks.Safe
