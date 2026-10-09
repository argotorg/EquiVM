import Benchmarks.Safe.SignatureBranchTrace
import Benchmarks.Safe.SignatureSplitTrace
import Benchmarks.Safe.SignatureOwnerTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSignatureIteration (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r v current last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2011⟩
      (UInt256.ofNat i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: R) mem aw rdata σ k C)
    (hc : SignatureContext p f i last) (he : p.executor = AccountAddress.ofUInt256 executor)
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hi : i < p.required.toNat) (hov : R.length + 43 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config f evm signatureLoopBody .reverted) ∨
    ∃ f' evm' σ' mem' ptr' aw' out s' r' v' owner k' C',
      ExecBlock config f evm signatureLoopBody (.ok f' evm') ∧
      SignatureContext p f' (i + 1) owner ∧
      f'.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2002⟩
        (UInt256.ofNat (i + 1) :: s' :: r' :: v' :: owner :: owner :: p.required ::
          UInt256.ofNat src :: p.hash :: executor :: R) mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hin : 65 * i + 65 ≤ p.signatures.size := by
    dsimp [SignatureInput.requiredBytes] at hreq
    omega
  have hi' : i + 1 < UInt256.size := by
    change i + 1 < 2 ^ 256
    omega
  have hb : src + 64 + p.signatures.size < UInt256.size := by
    change _ < 2 ^ 256
    omega
  have hsplit := signatureSplitSource (evm := evm) hc.toSignatureCore hc.index hin
  have hfinish {result} (ht : ExecBlock config (signatureVFrame f p.signatures i) evm
      (signatureLoopBody.drop 4) result) : ExecBlock config f evm signatureLoopBody result := by
    simpa only [List.take_append_drop] using execBlock_append_ok hsplit ht
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeSignatureSplit h hm hin hb (by simp; omega)
  have hr : (signatureVFrame f p.signatures i).locals["r"]? =
      some (wordBytes32Value (signatureR p.signatures i)) := by
    simp [signatureVFrame, signatureSFrame, signatureRFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hs : (signatureVFrame f p.signatures i).locals["s"]? =
      some (wordBytes32Value (signatureS p.signatures i)) := by
    simp [signatureVFrame, signatureSFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hv : (signatureVFrame f p.signatures i).locals["v"]? =
      some (uint256Value (signatureV p.signatures i)) := by
    simp [signatureVFrame, signatureSet, Std.HashMap.getElem?_insert]
  have ho' : (signatureVFrame f p.signatures i).locals["currentOwner"]? = some old := by
    simp [signatureVFrame, signatureSFrame, signatureRFrame, signatureOffsetFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ho]
  obtain ⟨hrev, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw', out, s', r', v', owner, k', C',
      hbody, hc', ho'', hee', hacc', hw', h₂, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
    safeSignatureBranchTrace p evm h₁ hc.split he hr hs hv ho' hee hacc hworld hm hf hz hsrc
      ha hp hn hreq (by rw [signatureV_toNat]; exact signatureVNat_bound _ _) hov
  · exact .inl ⟨hrev, hfinish (.consRevert (signatureSwitchSource hv hbody))⟩
  have hmem : 128 ≤ mem'.size := by have := hm'.available; omega
  have hswitch := signatureSwitchSource hv hbody
  obtain ⟨hrev, hbad⟩ | ⟨aw'', k'', C'', hvalid, h₃⟩ :=
    safeSignatureOwnerTrace h₂ (by omega) hi' (by simp; omega)
  · exact .inl ⟨hrev, hfinish (.consNormal hswitch
      (signatureOwnerSourceRejected hc'.toSignatureCore ho'' hc'.lastOwner
        (by rwa [hee', hacc'])))⟩
  refine .inr ⟨signatureNextFrame f' owner i, evm', σ', _, ptr', aw'', out, s', r', v', owner,
    k'', C'', hfinish (.consNormal hswitch (signatureOwnerSourceAccepted hc'.toSignatureCore
      ho'' hc'.lastOwner hc'.index hi' (by rwa [hee', hacc']))), hc'.next, ?_, hee', hacc', hw',
    h₃, hm'.scratch (by omega) (by omega) _ _, ?_, ?_, hpl, hph, ?_, ?_⟩
  · simp [signatureNextFrame, signatureSet, Std.HashMap.getElem?_insert, ho'']
  · exact (twoWordHashMem_load_preserved _ _ ⟨64⟩ (by decide)
      (by change 96 ≤ mem'.size; omega)).trans hf'
  · exact (twoWordHashMem_load_preserved _ _ ⟨96⟩ (by decide) hmem).trans hz'
  · rwa [twoWordHashMem_size_of_ge64 _ _ (by omega)]
  · exact hpres.trans (MemoryPreserves.scratch _ _ _ ptr') hpl

end Benchmarks.Safe
