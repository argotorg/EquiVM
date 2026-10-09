import Benchmarks.Safe.ContractSignatureBounds
import Benchmarks.Safe.ContractSignatureState
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

open ContractSignatureInput

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeCheckContractTrace (p : ContractSignatureInput)
    {I g s0 σ k C aw mem rdata ptr src} {owner ret : UInt256} {R : List UInt256}
    (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨6935⟩
      (p.offset :: UInt256.ofNat src :: p.hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (howner : p.owner = AccountAddress.ofUInt256 owner)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hs : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hov : R.length + 33 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm checkContractSignatureFunction.body .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out k' C',
      ExecFuncBody config p.frame evm checkContractSignatureFunction.body
        (.returned (p.finalFrame true) evm' none) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret R mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hmargin : ptr + 2 ^ 141 < UInt256.size := by change _ < 2 ^ 256; omega
  have hbytes := hm.available
  obtain ⟨hr, hbad⟩ | ⟨_, _, _, hstart, hend, h₁⟩ :=
    safeCheckContractBounds p h hm (by omega) (by omega)
  · exact Or.inl ⟨hr, safeCheckContractBoundsFailed p evm hbad⟩
  have hoff : p.offset.toNat + 32 ≤ p.signatures.size := hstart
  have hfinish : p.offset.toNat + 32 + p.len.toNat ≤ p.signatures.size := hend
  have hsig : p.signature.size = p.len.toNat := by
    simp only [signature, ByteArray.size_extract]
    dsimp [finish, start] at *
    omega
  have hsig64 : p.signature.size < 2 ^ 64 := by rw [hsig]; omega
  let subptr := src + 32 + p.offset.toNat
  let words := memoryWords mem (subptr + 32) ((p.signature.size + 31) / 32)
  have hwords : words.length = (p.signature.size + 31) / 32 := memoryWords_length _ _ _
  have hbegin : subptr + 32 = src + 32 + p.start := by dsimp [subptr, start]; omega
  have hview : WordArrayMemory mem (subptr + 32) words := memoryWords_view _ _ _
  have hsview : (wordBytes words).extract 0 p.signature.size = p.signature := by
    have hr := hm.sliceWords (show p.start ≤ p.finish by dsimp [finish]; omega) hend
    have hd : p.finish - p.start = p.signature.size := by rw [hsig]; dsimp [finish]; omega
    simpa only [hd, ← hbegin] using hr
  have hlen : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat p.signature.size := by
    rw [hm.word hoff (by omega), hsig]
    apply u256_inj
    exact (ulit_toNat' p.len.toNat p.len.val.isLt).symm
  have hadd : UInt256.ofNat 32 + (p.offset + UInt256.ofNat src) = UInt256.ofNat subptr := by
    apply u256_inj
    change (32 + (p.offset.toNat + src % UInt256.size) % UInt256.size) % UInt256.size =
      subptr % UInt256.size
    rw [Nat.mod_eq_of_lt (by omega : src < UInt256.size),
      Nat.mod_eq_of_lt (by omega : p.offset.toNat + src < UInt256.size)]
    congr 1
    dsimp [subptr]
    omega
  have h₂ := safeRuntime_block_7036 (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_7036_stack, hadd] at h₂
  have hcl : contractSignatureCallLength p.signature.size < 2 ^ 65 := by
    dsimp [contractSignatureCallLength, ABI.paddedSize]
    omega
  have hce : contractSignatureCallEnd ptr p.signature.size < ptr + 2 ^ 66 := by
    dsimp [contractSignatureCallEnd]
    omega
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, hac, hw, h₃, hout⟩ :=
    safeContractSignatureTrace words evm h₂ hee hacc hworld hf hz hlen hview hwords hsview
      (by omega) (by omega)
      (by rw [hwords, hsig]; dsimp [subptr]; omega)
      (by rw [hwords, hsig]; dsimp [subptr]; omega)
      (by omega) (by omega)
      (by
        have hg : 2 ^ 65 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega)
      (by simp; omega) (by jump_dest)
  have hc' : callViaEVM evm (EVM.address p.owner) 0
      (contractSignatureCallBytes p.hash p.signature) (z, evm', out) false := by
    simpa only [howner] using hc
  have hsource := safeCheckContractSource p hstart hend (by omega) hc'
  cases hv : contractSignatureResult z out
  · have h₄ := safeRuntime_block_7053_fallthrough (by simp; omega)
      (by rw [hv]; rfl) h₃
    have h₅ := safeRuntime_block_7058 (by
      simp only [safeRuntime_block_7053_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₄
    exact Or.inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_7058_stack, safeRuntime_block_7053_fallthrough_stack,
        List.length_cons]; omega) h₅, by simpa only [hv, Bool.false_eq_true, if_false] using
          hsource⟩
  · have h₄ := safeRuntime_block_7053_taken (by simp; omega)
      (by rw [hv]; decide) (by jump_dest) h₃
    have h₅ := safeRuntime_block_7074 (by omega) hret h₄
    have hbmem := contractSignatureFinalMemory_size_le mem out ptr p.signature.size p.hash words
      hwords (by omega) hsig64 hout
    have hbnext := contractSignatureNext_bounds ptr p.signature.size out hsig64 hout
    refine Or.inr ⟨evm', σ', _, contractSignatureNext ptr p.signature.size out, _, out, _, _,
      ?_, he, hac, hw, h₅, ?_, ?_, ?_, hbnext.1, hbnext.2, hbmem.2, ?_⟩
    · simpa only [hv, if_true] using hsource
    · exact contractSignatureFinalMemory_bytes hwords hm (by omega) ha (by omega)
    · exact contractSignatureFinalMemory_free _ _ _ _ _ _ hwords (by omega)
    · change memLoad ⟨96⟩
        (contractSignatureFinalMemory mem ptr p.signature.size p.hash words out) = ⟨0⟩
      rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
        contractSignatureFinalMemory_preserved mem out ptr p.signature.size 96 32 p.hash words
          hwords (by omega)
          (by decide) (by omega),
        ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
    · exact ⟨hbmem.1, fun off count hl hh hin ↦
        contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hwords hin hl hh⟩

end Benchmarks.Safe
