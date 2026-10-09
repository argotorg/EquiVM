import Benchmarks.Safe.SignatureBranchResult
import Benchmarks.Safe.SignatureApprovalTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem signatureApprovalMemoryFacts {mem : ByteArray} {src ptr : Nat} {p : SignatureInput}
    (hm : BytesMemory mem src p.signatures) (hsrc : 128 ≤ src) (hb : src < UInt256.size)
    (r : UInt256) :
    BytesMemory (signatureApprovalMemory mem r p.hash) src p.signatures ∧
    memLoad ⟨64⟩ (signatureApprovalMemory mem r p.hash) = memLoad ⟨64⟩ mem ∧
    memLoad ⟨96⟩ (signatureApprovalMemory mem r p.hash) = memLoad ⟨96⟩ mem ∧
    (signatureApprovalMemory mem r p.hash).size = mem.size ∧
    MemoryPreserves mem (signatureApprovalMemory mem r p.hash) 96 ptr := by
  have hmem : 128 ≤ mem.size := by have := hm.available; omega
  have hs : (twoWordHashMem (UInt256.land solcAddrMask r) ⟨8⟩ mem).size = mem.size :=
    twoWordHashMem_size_of_ge64 _ _ (by omega)
  refine ⟨(hm.scratch hb (by omega) _ _).scratch hb (by omega) _ _, ?_, ?_, ?_, ?_⟩
  · rw [signatureApprovalMemory, twoWordHashMem_load_preserved _ _ ⟨64⟩ (by decide)
      (by rw [hs]; exact Nat.le_trans (by decide) hmem),
      twoWordHashMem_load_preserved _ _ ⟨64⟩ (by decide)
        (by exact Nat.le_trans (by decide) hmem)]
  · rw [signatureApprovalMemory, twoWordHashMem_load_preserved _ _ ⟨96⟩ (by decide)
      (by rw [hs]; exact hmem), twoWordHashMem_load_preserved _ _ ⟨96⟩ (by decide) hmem]
  · rw [signatureApprovalMemory, twoWordHashMem_size_of_ge64 _ _ (by rw [hs]; omega), hs]
  · exact (MemoryPreserves.scratch mem _ _ ptr).trans (MemoryPreserves.scratch _ _ _ ptr)
      (Nat.le_refl _)

theorem safeSignatureApprovalBranch (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r current last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2108⟩
      (UInt256.ofNat i :: s :: r :: ⟨1⟩ :: current :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: R) mem aw rdata σ k C)
    (hc : SignatureContext p f i last) (he : p.executor = AccountAddress.ofUInt256 executor)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src) (hb : src < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    SignatureBranchResult p I g s0 f evm i last executor src ptr mem R signatureApprovalBody := by
  have hsource := signatureApprovalSource (evm := evm) hc.toSignatureCore he hr ho
  rw [hee, hacc] at hsource
  obtain ⟨hrev, hbad⟩ | ⟨mem', aw', k', C', hv, h₁, hform⟩ :=
    safeSignatureApprovalTrace h (by have := hm.available; omega) hov
  · exact .inl ⟨hrev, by simpa only [hbad, if_false] using hsource⟩
  refine .inr ⟨signatureCurrentFrame f r, evm, σ, mem', ptr, aw', rdata, s, r, ⟨1⟩, r, k', C',
    ?_, hc.current r, ?_, hee, hacc, hworld, h₁, ?_⟩
  · simpa only [hv, if_true] using hsource
  · simp [signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert]
  rcases hform with rfl | rfl
  · exact ⟨hm, hf, hz, Nat.le_refl _, by omega, by omega, MemoryPreserves.refl _ _ _⟩
  · obtain ⟨hm', hf', hz', hsize, hpres⟩ := signatureApprovalMemoryFacts (ptr := ptr) hm hsrc hb r
    exact ⟨hm', hf'.trans hf, hz'.trans hz, Nat.le_refl _, by omega, by rw [hsize]; omega, hpres⟩

end Benchmarks.Safe
