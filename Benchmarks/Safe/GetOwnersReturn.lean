import Benchmarks.Safe.AddressArrayMemory
import Benchmarks.Safe.AddressArrayCopy
import Benchmarks.Safe.AddressArrayEncoding
import Benchmarks.Safe.Blocks.Runtime_009
import Benchmarks.Safe.Blocks.Runtime_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

set_option maxHeartbeats 800000 in
theorem safeGetOwnersReturnTrace {I g s0 σ k C aw mem rdata n words} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨1174⟩ (⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus) :
    RDret safeBytecode g s0 σ (addressArrayReturnBytes words) := by
  let fp := 160 + 32 * n
  have hfp : (addressArrayFreePtr n).toNat = fp :=
    ulit_toNat' _ (by change 160 + 32 * n < 2 ^ 256; omega)
  have hfp32 : (addressArrayFreePtr n + UInt256.ofNat 32).toNat = fp + 32 := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hfp]; change fp + 32 < 2 ^ 256; dsimp [fp]; omega),
      hfp]
  have hfpadd : addressArrayFreePtr n + UInt256.ofNat 32 = UInt256.ofNat (fp + 32) := by
    apply u256_inj
    rw [hfp32, ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)]
  have hfree : memLoad (UInt256.ofNat 64) mem = addressArrayFreePtr n :=
    mloadWordValue_of_readWithPadding (by change 64 < mem.size; have := hm.lower; omega)
      hm.freePtr
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_1174_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_1174_stack, hfree] at h₁
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_10305_packed (by simp; omega)
    (by jump_dest) h₁
  simp only [safeRuntime_block_10305_stack, safeRuntime_block_10305_memory, hfp, hfpadd] at h₂
  have hcount : memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) = UInt256.ofNat n := by
    apply mloadWordValue_of_readWithPadding
      (by change 128 < (writeWord mem fp ⟨32⟩).size
          rw [writeWord_sparse_size]; have := hm.lower; omega)
    change (writeWord mem fp ⟨32⟩).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by dsimp [fp]; omega, hm.lower⟩)]
    exact hm.count
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_10238_packed (by simp; omega) h₂
  change RD safeBytecode I g s0 ⟨10256⟩
    (⟨0⟩ :: (⟨128⟩ + UInt256.ofNat 32) :: memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) ::
      ⟨0⟩ :: ⟨128⟩ :: (UInt256.ofNat (fp + 32) + UInt256.ofNat 32) ::
      ⟨6891⟩ :: ⟨0⟩ :: addressArrayFreePtr n :: ⟨128⟩ :: ⟨771⟩ :: R)
    (writeWord (writeWord mem fp ⟨32⟩) (UInt256.ofNat (fp + 32)).toNat
      (memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩))) aw₃ rdata σ k₃ C₃ at h₃
  have ha : UInt256.ofNat (fp + 32) + UInt256.ofNat 32 = UInt256.ofNat (fp + 64) := by
    rw [u256_add_comm]
    simpa only [Nat.add_assoc] using u256_32_add_ofNat (fp + 32)
  rw [hcount, ha, ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)] at h₃
  have hwords := addressArrayHeaderWords mem fp words 160 hm.words hm.aligned
    (by decide) (by dsimp [fp]; omega) (by rw [hm.length])
  rw [hm.length] at hwords
  have hmsize := addressArrayHeaderSize mem fp n hm.upper
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeAddressArrayCopyLoop words (i := 0) (src := 160) h₃
    (by simp; omega) hwords hmsize (by rw [hm.length]; dsimp [fp]; omega)
    (by simpa using hm.length) (by change n < 2 ^ 256; omega)
    (by rw [hm.length]; change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
    hc (by jump_dest)
  have h₅ := safeRuntime_block_6891 (by omega) (by jump_dest) h₄
  have hret := safeRuntime_block_771 (by omega) h₅
  let encoded := addressArrayHeaderMemory mem fp n ++ wordBytes words
  have he64 : encoded.readWithPadding 64 32 = (addressArrayFreePtr n).toByteArray := by
    rw [readAppendPrefix _ _ _ (by rw [hmsize]; dsimp [fp]; omega),
      addressArrayHeaderRead _ _ _ _ (by have := hm.lower; omega)
        (by dsimp [fp]; omega)]
    exact hm.freePtr
  have hefree : memLoad (UInt256.ofNat 64) encoded = addressArrayFreePtr n :=
    mloadWordValue_of_readWithPadding
      (by change 64 < encoded.size
          dsimp [encoded]; rw [ByteArray.size_append, hmsize]; dsimp [fp]; omega) he64
  change RDret safeBytecode g s0 σ (encoded.readWithPadding
    (memLoad (UInt256.ofNat 64) encoded).toNat
    (UInt256.sub (UInt256.ofNat (fp + 64 + 32 * words.length))
      (memLoad (UInt256.ofNat 64) encoded)).toNat) at hret
  have hend : (UInt256.ofNat (fp + 64 + 32 * words.length)).toNat =
      fp + 64 + 32 * words.length :=
    ulit_toNat' _ (by rw [hm.length]; change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  rw [hefree, usub_toNat (by rw [hfp, hend]; omega), hfp, hend] at hret
  have hlen : fp + 64 + 32 * words.length - fp = 64 + 32 * words.length := by omega
  rw [hlen] at hret
  have hread := addressArrayEncodedRead mem fp words hm.upper
  rw [hm.length] at hread
  rw [hm.length] at hret
  rw [hread] at hret
  exact hret

end Benchmarks.Safe
