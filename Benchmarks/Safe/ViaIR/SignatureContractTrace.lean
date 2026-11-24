import Benchmarks.Safe.ViaIR.SignatureContractSource
import Benchmarks.Safe.ViaIR.ContractSignatureCheckTrace
import Benchmarks.Safe.ViaIR.SafeMulTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_036
import Benchmarks.Safe.ViaIR.Blocks.Runtime_038
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSignatureContractTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i s r last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD fork safeBytecode I g s0 ⟨7607⟩
      (⟨0⟩ :: r :: s :: r :: last :: s :: UInt256.ofNat src :: p.hash ::
        i :: executor :: p.required :: R)
      mem aw rdata σ k C)
    (hc : SignatureCore p f) (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hov : R.length + 42 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config f evm signatureContractBody .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out k' C',
      ExecBlock fork config f evm signatureContractBody
        (.ok (signatureSet (signatureContractFrame f r s) "_contractSigOk" .unit) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨7803⟩
        (last :: UInt256.land solcAddrMask r :: UInt256.ofNat src :: p.hash ::
          i :: executor :: p.required :: R)
        mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr ∧ (ptr < 2 ^ 64 → ptr' < 2 ^ 64) := by
  have hfit : p.requiredBytes < UInt256.size := lt_of_le_of_lt hreq (lt_trans hn (by decide))
  have hmul : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  have h₁ := safeRuntime_block_7607 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeMul65Trace h₁ hfit (by simp; omega) (by jump_dest)
  by_cases hb : p.requiredBytes ≤ s.toNat
  swap
  · have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨1⟩ :=
      ult_one (by rw [hmul]; omega)
    have h₃ := safeRuntime_block_7628_taken (by simp; omega)
      (by rw [hlt]; decide) (by jump_dest) h₂
    have h₄ := safeRuntime_block_8123 (by
      simp only [safeRuntime_block_7628_taken_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_9682 (by
      simp only [safeRuntime_block_7628_taken_stack, List.length_cons]; omega) h₄,
      signatureContractSourceRejected hc hr hs ho hb⟩
  have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ :=
    ult_zero (by rw [hmul]; exact hb)
  have h₃ := safeRuntime_block_7628_fallthrough (by simp; omega) hlt h₂
  simp only [safeRuntime_block_7628_fallthrough_stack, safeAddressMask] at h₃
  have haddr : AccountAddress.ofUInt256 (UInt256.land solcAddrMask r) =
      AccountAddress.ofUInt256 r := by
    rw [u256_land_comm]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (addressOfNat_eq_of_masked_word r).symm
  obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, k', C', hbody, he, hac, hw,
      h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩ :=
    safeCheckContractTrace (signatureContractInput p r s) evm h₃ hee hacc hworld haddr.symm
      hm hf hz hsrc ha hp hn (by simp; omega)
  · exact .inl ⟨hrev, signatureContractSource hc hr hs ho hb hbody⟩
  exact .inr ⟨evm', σ', mem', ptr', aw', out, _, _,
    signatureContractSource hc hr hs ho hb hbody, he, hac, hw,
    h₅, hm', hf', hz', hpl, hph, hms, hpres, hcap⟩

end Benchmarks.Safe.ViaIR
