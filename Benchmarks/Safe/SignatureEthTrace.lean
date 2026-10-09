import Benchmarks.Safe.EthSignPrepare
import Benchmarks.Safe.EthSignSource
import Benchmarks.Safe.EcrecoverTrace
import Benchmarks.Safe.SignatureRecoveryMemory
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSignatureEthTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i s r v current last : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2405⟩
      (i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
      mem aw rdata σ k C)
    (hc : SignatureCore p f) (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (hv : f.locals["v"]? = some (uint256Value v)) (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hvl : 4 ≤ v.toNat) (hv8 : v.toNat < 256) (hov : R.length + 17 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config f evm signatureEthBody .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out owner k' C',
      ExecBlock config f evm signatureEthBody
        (.ok (signatureRecoveredFrame (signatureEthFrame f p.hash) owner) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩
        (i :: s :: r :: v :: owner :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
        mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hptr : 128 ≤ ptr := by omega
  have hmem : 128 ≤ mem.size := by have := hm.available; omega
  have hb : ptr + 252 < UInt256.size := by change _ < 2 ^ 256; omega
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeEthSignPrepare h hf (by omega) (by omega)
    (by omega) hvl hov
  have hve : (UInt256.sub v ⟨4⟩).toNat < 256 := by
    rw [usub_toNat (a := v) (b := ⟨4⟩) hvl]
    omega
  obtain ⟨gasArg, aw₂, k₂, C₂, h₂⟩ := safeEcrecoverEthSignPrepare
    (p := ⟨ethSignWord p.hash, UInt256.sub v ⟨4⟩, r, s⟩) h₁
    (ethSignMemory_free mem ptr p.hash) (by omega) (by omega) hve (by simp; omega)
  obtain ⟨hrev, hbody⟩ | ⟨evm', σ', out, aw', k', C', hbody, he, hac, hw, h₃, _⟩ :=
    safeEcrecoverCall false evm h₂ hee hacc hworld (by omega) (by omega) (by simp; omega)
  · exact .inl ⟨hrev, signatureEthSourceRejected hc hr hs hv hvl hv8 hbody⟩
  have hmeth := ethSignMemory_bytes (hash := p.hash) hm (by omega) ha (by omega)
  have hethsize := ethSignMemory_size mem ptr p.hash (by omega)
  have hzeth : memLoad ⟨96⟩ (ethSignMemory mem ptr p.hash) = ⟨0⟩ := by
    rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
      ethSignMemory_preserved _ _ _ _ _ hmem (by decide) hptr,
      ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
  refine .inr ⟨evm', σ', _, ptr + 92 + 32, aw', out, calldataWord out 0, k', C',
    signatureEthSource hc hr hs hv ho hvl hv8 hbody, he, hac, hw, h₃,
    ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · exact ecrecoverOutputMemory_bytes hmeth (by omega) (by omega) (by omega)
  · exact ecrecoverOutputMemory_free _ _ _ _ (by omega)
  · exact ecrecoverOutputMemory_zeroSlot (by rw [hethsize]; omega) (by omega) hzeth
  · rw [ecrecoverOutputMemory_size _ _ _ _ (by omega), hethsize]
    omega
  · refine ⟨?_, ?_⟩
    · rw [ecrecoverOutputMemory_size _ _ _ _ (by omega), hethsize]
      omega
    · intro off count hl hh hin
      rw [ecrecoverOutputMemory_preserved _ _ _ _ _ _ (by rw [hethsize]; omega)
        hl (by omega), ethSignMemory_preserved _ _ _ _ _ hin hl hh]

end Benchmarks.Safe
