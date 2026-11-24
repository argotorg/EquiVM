import Benchmarks.Safe.V0_cdb2eb5.SignatureApprovalBranch
import Benchmarks.Safe.V0_cdb2eb5.SignatureContractTrace
import Benchmarks.Safe.V0_cdb2eb5.SignaturePlainTrace
import Benchmarks.Safe.V0_cdb2eb5.SignatureEthTrace
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_015

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeSignatureBranchTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r v current last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD fork safeBytecode I g s0 (if v = ⟨0⟩ then ⟨2144⟩ else ⟨2200⟩)
      (UInt256.ofNat i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: R) mem aw rdata σ k C)
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
  by_cases h₀ : v.toNat = 0
  · have heq : v = ⟨0⟩ := u256_inj h₀
    subst v
    simp only [if_true] at h
    change SignatureBranchResult fork p I g s0 f evm i last executor src ptr mem R signatureContractBody
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, k', C', hbody, hee', hacc', hw',
        h₁, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
      safeSignatureContractTrace p evm h hc.toSignatureCore hr hs ho hee hacc hworld hm hf hz
        hsrc ha hp hn hreq (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, s, r, ⟨0⟩, r, k', C', hbody,
      hc.contractBranch r s, ?_, hee', hacc', hw', h₁, hm', hf', hz', hpl, hph, hms, hpres⟩
    simp [signatureContractFrame, signatureCurrentFrame, signatureSet,
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
  have h₂ := safeRuntime_block_2200_taken (by simp; omega)
    (u256_sub_ne_zero_of_ne hn₁) (by jump_dest) h
  by_cases hh : 30 < v.toNat
  · simp only [if_pos hh]
    have hgt : UInt256.gt v (UInt256.ofNat 30) = ⟨1⟩ := ugt_one hh
    have h₄ := safeRuntime_block_2301_fallthrough (by simp; omega) (by rw [hgt]; decide) h₂
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
        hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
      safeSignatureEthTrace p evm h₄ hc.toSignatureCore hr hs hv ho hee hacc hworld hm hf hz
        hsrc ha hp (by omega) hv8 (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, s, r, v, owner, k', C', hbody,
      hc.eth owner, ?_, hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres⟩
    simp [signatureRecoveredFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert]
  · simp only [if_neg hh]
    have hgt : UInt256.gt v (UInt256.ofNat 30) = ⟨0⟩ :=
      ugt_zero (by change v.toNat ≤ 30; omega)
    have h₄ := safeRuntime_block_2301_taken (by simp; omega) (by rw [hgt]; decide)
      (by jump_dest) h₂
    obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, owner, k', C', hbody,
        hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
      safeSignaturePlainTrace p evm h₄ hc.toSignatureCore hr hs hv ho hee hacc hworld hm hf hz
        hsrc ha hp hv8 (by simp; omega)
    · exact .inl ⟨hrev, hbody⟩
    refine .inr ⟨_, evm', σ', mem', ptr', aw', out, s, r, v, owner, k', C', hbody,
      hc.recovered owner, ?_, hee', hacc', hw', h₅, hm', hf', hz', hpl, hph, hms, hpres⟩
    simp [signatureRecoveredFrame, signatureCurrentFrame, signatureSet,
      Std.HashMap.getElem?_insert]

end Benchmarks.Safe.V0_cdb2eb5
