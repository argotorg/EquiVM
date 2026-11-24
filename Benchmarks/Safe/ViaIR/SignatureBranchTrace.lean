import Benchmarks.Safe.ViaIR.SignatureApprovalBranch
import Benchmarks.Safe.ViaIR.SignatureContractTrace
import Benchmarks.Safe.ViaIR.SignaturePlainTrace
import Benchmarks.Safe.ViaIR.SignatureEthTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSignatureBranchTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r v last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD fork safeBytecode I g s0 (if v = ⟨0⟩ then ⟨7607⟩ else ⟨8128⟩)
      (v :: r :: s :: r :: last :: s :: UInt256.ofNat src :: p.hash ::
        UInt256.ofNat i :: executor :: p.required :: R) mem aw rdata σ k C)
    (hc : SignatureContext p f i last) (he : p.executor = AccountAddress.ofUInt256 executor)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (hv : f.locals["v"]? = some (uint256Value v)) (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hv8 : v.toNat < 256) (hov : R.length + 43 ≤ 1024) :
    SignatureBranchResult fork p I g s0 f evm i last executor src ptr mem R
      (signatureSelectedBody v) := by
  have haddr : AccountAddress.ofUInt256 (UInt256.land solcAddrMask r) =
      AccountAddress.ofUInt256 r := by
    rw [u256_land_comm]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (addressOfNat_eq_of_masked_word r).symm
  by_cases h₀ : v.toNat = 0
  · have heq : v = ⟨0⟩ := u256_inj h₀
    subst v
    simp only [if_true] at h
    change SignatureBranchResult fork p I g s0 f evm i last executor src ptr mem R signatureContractBody
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, k', C', hbody, hee', hacc', hw',
        h₁, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩ :=
      safeSignatureContractTrace p evm h hc.toSignatureCore hr hs ho hee hacc hworld hm hf hz
        hsrc ha hp hn hreq (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, UInt256.land solcAddrMask r, k', C', hbody,
      hc.contractBranch r s, ?_, hee', hacc', hw', h₁, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩
    simp [haddr, signatureContractFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hn₀ : v ≠ ⟨0⟩ := fun hh ↦ h₀ (congrArg UInt256.toNat hh)
  rw [if_neg hn₀] at h
  simp only [signatureSelectedBody, if_neg h₀]
  by_cases h₁ : v.toNat = 1
  · have heq : v = ⟨1⟩ := u256_inj h₁
    subst v
    exact safeSignatureApprovalBranch p evm h hc he hr ho hee hacc hworld hm hf hz hsrc
      (by change src < 2 ^ 256; omega) (by omega)
  simp only [if_neg h₁]
  have hn₁ : UInt256.ofNat 1 ≠ v := fun hh ↦ h₁ (congrArg UInt256.toNat hh.symm)
  have hneq : UInt256.eq v (UInt256.ofNat 1) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun hh ↦ hn₁ (uInt256_eq_one_eq hh).symm)
  have h₂ := safeRuntime_block_8128_taken (by simp; omega)
    (by rw [hneq]; decide) (by jump_dest) h
  by_cases htwo : v.toNat = 2
  · have heq : v = ⟨2⟩ := u256_inj htwo
    subst v
    have h₃ := safeRuntime_block_8251_fallthrough (by simp; omega) (by decide) h₂
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', aw', out, k', C', hbody, hee', hacc', hw',
        h₄, hm', hf', hz', hms, hpres⟩ :=
      safeSignatureP256Trace p evm h₃ hc.toSignatureCore hr hs ho hee hacc hworld hm hf hz
        hsrc ha hp hn hreq (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr, aw', out, UInt256.land solcAddrMask r, k', C', hbody,
      hc.p256 r s, ?_, hee', hacc', hw', h₄, hm', hf', hz', Nat.le_refl _, by omega, hms, hpres, id⟩
    simp [haddr, signatureP256FinalFrame, signatureP256SignerFrame, signatureP256WordsFrame,
      signatureP256XFrame, signatureP256SFrame, signatureP256RFrame, signatureP256EndFrame,
      signatureP256OffsetFrame, signatureDynamicFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  simp only [if_neg htwo]
  have hn₂ : UInt256.ofNat 2 ≠ v := fun hh ↦ htwo (congrArg UInt256.toNat hh.symm)
  have h₃ := safeRuntime_block_8251_taken (by simp; omega)
    (u256_sub_ne_zero_of_ne hn₂.symm) (by jump_dest) h₂
  by_cases hh : 30 < v.toNat
  · simp only [if_pos hh]
    have hgt : UInt256.gt v (UInt256.ofNat 30) = ⟨1⟩ := ugt_one hh
    have h₄ := safeRuntime_block_8526_fallthrough (by simp; omega) (by rw [hgt]; decide) h₃
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
        hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩ :=
      safeSignatureEthTrace p evm h₄ hc.toSignatureCore hr hs hv ho hee hacc hworld hm hf hz
        hsrc ha hp (by omega) hv8 (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
      hc.eth owner, ?_, hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩
    simp [signatureRecoveredFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert]
  · simp only [if_neg hh]
    have hgt : UInt256.gt v (UInt256.ofNat 30) = ⟨0⟩ :=
      ugt_zero (by change v.toNat ≤ 30; omega)
    have h₄ := safeRuntime_block_8526_taken (by simp; omega) (by rw [hgt]; decide)
      (by jump_dest) h₃
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
        hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩ :=
      safeSignaturePlainTrace p evm h₄ hc.toSignatureCore hr hs hv ho hee hacc hworld hm hf hz
        hsrc ha hp hv8 (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
      hc.recovered owner, ?_, hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩
    simp [signatureRecoveredFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert]

end Benchmarks.Safe.ViaIR
