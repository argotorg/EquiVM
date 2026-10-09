import Benchmarks.Safe.SignatureRecoverySource
import Benchmarks.Safe.EcrecoverTrace
import Benchmarks.Safe.SignatureRecoveryMemory
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSignaturePlainTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i s r v current last : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2586⟩
      (i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
      mem aw rdata σ k C)
    (hc : SignatureCore p f) (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (hv : f.locals["v"]? = some (uint256Value v)) (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hv8 : v.toNat < 256) (hov : R.length + 17 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecBlock config f evm (signatureRecoverBody (.var "dataHash") (.var "v")) .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out owner k' C',
      ExecBlock config f evm (signatureRecoverBody (.var "dataHash") (.var "v"))
        (.ok (signatureRecoveredFrame f owner) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩
        (i :: s :: r :: v :: owner :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
        mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hptr : 128 ≤ ptr := by omega
  have hb : ptr + 160 < UInt256.size := by change _ < 2 ^ 256; omega
  obtain ⟨gasArg, aw₁, k₁, C₁, h₁⟩ := safeEcrecoverPlainPrepare
    (p := ⟨p.hash, v, r, s⟩) h hf (by omega) hb hv8 hov
  obtain ⟨hrev, hbody⟩ | ⟨evm', σ', out, aw', k', C', hbody, he, hac, hw, h₂, _⟩ :=
    safeEcrecoverCall true evm h₁ hee hacc hworld (by omega) hb (by simp; omega)
  · exact .inl ⟨hrev, signatureRecoverSourceRejected hc (evalLocalValue hc.hash)
      (evalLocalValue hv) hr hs hbody⟩
  refine .inr ⟨evm', σ', _, ptr + 32, aw', out, calldataWord out 0, k', C',
    signatureRecoverSource hc (evalLocalValue hc.hash) (evalLocalValue hv) hr hs ho hbody,
    he, hac, hw, h₂, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · exact ecrecoverOutputMemory_bytes hm (by omega) ha (by omega)
  · exact ecrecoverOutputMemory_free _ _ _ _ (by omega)
  · exact ecrecoverOutputMemory_zeroSlot (by have := hm.available; omega) hptr hz
  · rw [ecrecoverOutputMemory_size _ _ _ _ (by omega)]
    omega
  · refine ⟨?_, fun off count hl hh hin ↦
      ecrecoverOutputMemory_preserved _ _ _ _ _ _ hin hl hh⟩
    rw [ecrecoverOutputMemory_size _ _ _ _ (by omega)]
    omega

end Benchmarks.Safe
