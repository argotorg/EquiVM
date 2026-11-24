import Benchmarks.Safe.V0_cdb2eb5.ContractSignatureBounds
import Benchmarks.Safe.V0_cdb2eb5.ContractSignatureState
import Benchmarks.Safe.V0_cdb2eb5.MemoryPreserves
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

open ContractSignatureInput

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeCheckContractTrace (p : ContractSignatureInput)
    {I g s0 σ k C aw mem rdata ptr src} {owner ret : UInt256} {R : List UInt256}
    (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨7082⟩
      (p.offset :: UInt256.ofNat src :: p.hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (howner : p.owner = AccountAddress.ofUInt256 owner)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hs : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hov : R.length + 33 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config p.frame evm checkContractSignatureFunction.body .reverted) ∨
    ∃ evm' σ' mem' ptr' aw' out k' C',
      ExecFuncBody fork config p.frame evm checkContractSignatureFunction.body
        (.returned (p.finalFrame true) evm' none) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ret R mem' aw' out σ' k' C' ∧
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
  let head := contractSignatureHeaderMemory mem ptr p.hash
  let words := memoryWords head (subptr + 32) ((p.signature.size + 31) / 32)
  have hwords : words.length = (p.signature.size + 31) / 32 := memoryWords_length _ _ _
  have hbegin : subptr + 32 = src + 32 + p.start := by dsimp [subptr, start]; omega
  have hview : WordArrayMemory head (subptr + 32) words := memoryWords_view _ _ _
  have hsview : (wordBytes words).extract 0 p.signature.size = p.signature := by
    rw [memoryWords_prefix _ _ _ _ (by
      rw [contractSignatureHeaderMemory_size]
      rw [hsig]
      dsimp [subptr]
      omega) (by omega)]
    rw [contractSignatureHeaderMemory_preserved _ _ _ _ _ (by
      rw [hsig]; dsimp [subptr]; omega) (by rw [hsig]; dsimp [subptr]; omega), hbegin]
    have hr := hm.slice (show p.start ≤ p.finish by dsimp [finish]; omega) hend
    have hd : p.finish - p.start = p.signature.size := by rw [hsig]; dsimp [finish]; omega
    simpa only [hd] using hr
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
  have hlenWord : p.len = UInt256.ofNat p.signature.size := by
    rw [hsig]
    apply u256_inj
    exact (ulit_toNat' p.len.toNat p.len.val.isLt).symm
  rw [hlenWord] at h₁
  have hcl : contractSignatureCallLength p.signature.size < 2 ^ 65 := by
    dsimp [contractSignatureCallLength, ABI.paddedSize]
    omega
  obtain ⟨evm', σ', z, out, hc, he, hac, hw, hout, htrace⟩ :=
    safeContractSignatureTrace words evm h₁ hee hacc hworld hf hadd hlen hview hwords hsview
      (by omega) (by omega)
      (by dsimp [subptr]; omega) (by dsimp [subptr]; omega)
      (by rw [hwords, hsig]; dsimp [subptr]; omega)
      (by rw [hwords, hsig]; omega)
      (by
        have hg : 2 ^ 65 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega) hov hret
  have hc' : callViaEVM fork evm (EVM.address p.owner) 0
      (contractSignatureCallBytes p.hash p.signature) (z, evm', out) false := by
    simpa only [howner] using hc
  have hsource := safeCheckContractSource p hstart hend (by omega) (by omega) hc'
  rcases htrace with ⟨hr, hv⟩ | ⟨aw', k', C', hr, hv⟩
  · exact Or.inl ⟨hr, by simpa only [hv, Bool.false_eq_true, if_false] using hsource⟩
  · have hbmem := contractSignatureFinalMemory_size_le mem out ptr p.signature.size p.hash words
      hwords (by omega) hsig64 hout
    have hbnext := contractSignatureNext_bounds ptr p.signature.size out hsig64 hout
    refine Or.inr ⟨evm', σ', _, contractSignatureNext ptr p.signature.size out, _, out, _, _,
      ?_, he, hac, hw, hr, ?_, ?_, ?_, hbnext.1, hbnext.2, hbmem.2, ?_⟩
    · simpa only [hv, if_true] using hsource
    · exact contractSignatureFinalMemory_bytes hwords hm (by omega) ha (by omega) (by omega)
    · exact contractSignatureFinalMemory_free _ _ _ _ _ _ hwords (by omega) (by omega)
    · change memLoad ⟨96⟩
        (contractSignatureFinalMemory mem ptr p.signature.size p.hash words out) = ⟨0⟩
      rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
        contractSignatureFinalMemory_preserved mem out ptr p.signature.size 96 32 p.hash words
          hwords (by omega) (by decide) (by omega) (by omega),
        ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
    · exact ⟨hbmem.1, fun off count hl hh hin ↦
        contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hwords hin hl hh (by omega)⟩

end Benchmarks.Safe.V0_cdb2eb5
