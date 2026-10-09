import Benchmarks.Safe.SignatureP256BoundsTrace
import Benchmarks.Safe.SignatureP256Check

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def signatureP256FinalFrame (f : Frame) (p : SignatureInput) (r s : UInt256) : Frame :=
  signatureSet (signatureP256SignerFrame (signatureP256EndFrame f r s)
    (signatureP256Input p s)) "p256Ok" (.bool true)

theorem safeSignatureP256Trace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i s r v current last : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2218⟩
      (i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
      mem aw rdata σ k C)
    (hc : SignatureCore p f) (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hov : R.length + 26 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config f evm signatureP256Body .reverted) ∨
    ∃ evm' σ' mem' aw' out k' C',
      ExecBlock config f evm signatureP256Body (.ok (signatureP256FinalFrame f p r s) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩
        (i :: (signatureP256Input p s).s :: (signatureP256Input p s).r :: v :: r :: last ::
          p.required :: UInt256.ofNat src :: p.hash :: R) mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧
      MemoryPreserves mem mem' 96 ptr := by
  have hn' : p.signatures.size < UInt256.size := lt_trans hn (by decide)
  obtain ⟨hrev, hbad⟩ | ⟨aw₁, k₁, C₁, hl, hh, h₁⟩ :=
    safeSignatureP256Bounds p h hm hn' hreq (by simp; omega)
  · exact .inl ⟨hrev, signatureP256SourceBoundsFailed hc hr hs ho hbad⟩
  have hprefix := signatureP256SourcePrefix (evm := evm) hc hr hs ho hl hh hn'
  have hoff : (signatureP256EndFrame f r s).locals["p256Offset"]? =
      some (uint256Value s) := by
    simp [signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have howner : (signatureP256EndFrame f r s).locals["currentOwner"]? =
      some (.address (AccountAddress.ofUInt256 r)) := by
    simp [signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', aw', out, k', C', hbody, he, hac, hw,
      h₂, hm', hf', hz', hms, hpres⟩ :=
    safeSignatureP256Check p evm h₁ (hc.p256End r s) hoff howner hee hacc hworld
      hm hf hz hsrc ha hp hh hov
  · exact .inl ⟨hrev, by simpa only [List.take_append_drop] using
      execBlock_append_ok hprefix hbody⟩
  exact .inr ⟨evm', σ', mem', aw', out, k', C', by
    simpa only [List.take_append_drop] using execBlock_append_ok hprefix hbody,
    he, hac, hw, h₂, hm', hf', hz', hms, hpres⟩

end Benchmarks.Safe
