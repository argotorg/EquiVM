import Benchmarks.Safe.SignatureContractSource
import Benchmarks.Safe.ContractSignatureCheckTrace
import Benchmarks.Safe.SafeMulTrace
import Benchmarks.Safe.Blocks.Runtime_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSignatureContractTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i s r current last : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2052⟩
      (i :: s :: r :: ⟨0⟩ :: current :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
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
    (RDrev safeBytecode g s0 ∧ ExecBlock config f evm signatureContractBody .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out k' C',
      ExecBlock config f evm signatureContractBody
        (.ok (signatureSet (signatureContractFrame f r s) "_contractSigOk" .unit) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩
        (i :: s :: r :: ⟨0⟩ :: r :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
        mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hfit : p.requiredBytes < UInt256.size := lt_of_le_of_lt hreq (lt_trans hn (by decide))
  have hmul : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  have h₁ := safeRuntime_block_2052 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeMulTrace h₁ hfit (by simp; omega) (by jump_dest)
  by_cases hb : p.requiredBytes ≤ s.toNat
  swap
  · have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨1⟩ :=
      ult_one (by rw [hmul]; omega)
    have h₃ := safeRuntime_block_2067_fallthrough (by simp; omega)
      (by rw [hlt]; decide) h₂
    have h₄ := safeRuntime_block_2075 (by
      simp only [safeRuntime_block_2067_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_2075_stack, safeRuntime_block_2067_fallthrough_stack,
        List.length_cons]; omega) h₄, signatureContractSourceRejected hc hr hs ho hb⟩
  have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ :=
    ult_zero (by rw [hmul]; exact hb)
  have h₃ := safeRuntime_block_2067_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_2091 (by simp; omega) (by jump_dest) h₃
  obtain ⟨hrev, hbody⟩ | ⟨evm', σ', mem', ptr', aw', out, k', C', hbody, he, hac, hw,
      h₅, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
    safeCheckContractTrace (signatureContractInput p r s) evm h₄ hee hacc hworld rfl
      hm hf hz hsrc ha hp hn (by simp; omega) (by jump_dest)
  · exact .inl ⟨hrev, signatureContractSource hc hr hs ho hb hbody⟩
  have h₆ := safeRuntime_block_2103 (by simp; omega) (by jump_dest) h₅
  exact .inr ⟨evm', σ', mem', ptr', aw', out, _, _,
    signatureContractSource hc hr hs ho hb hbody, he, hac, hw,
    h₆, hm', hf', hz', hpl, hph, hms, hpres⟩

end Benchmarks.Safe
