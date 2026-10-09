import Benchmarks.Safe.AddressArrayMemory
import Benchmarks.Safe.WordBufferEncoding
import Benchmarks.Safe.WordBufferCopy
import Benchmarks.Safe.Blocks.Runtime_008
import Benchmarks.Safe.Blocks.Runtime_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 2000

set_option maxHeartbeats 800000 in
theorem safeStorageAtReturnTrace {I g s0 σ k C aw mem rdata n words} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨918⟩ (⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024)
    (hm : AddressArrayMemory mem n words (UInt256.ofNat (32 * n)))
    (hn : n ≤ 2 ^ 64 - 1) :
    RDret safeBytecode g s0 σ (wordBufferReturnBytes words) := by
  let fp := 160 + 32 * n
  have hfp : (addressArrayFreePtr n).toNat = fp :=
    ulit_toNat' _ (by change 160 + 32 * n < 2 ^ 256; omega)
  have hfpadd : addressArrayFreePtr n + UInt256.ofNat 32 = UInt256.ofNat (fp + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat fp
  have ha : UInt256.ofNat (fp + 32) + UInt256.ofNat 32 = UInt256.ofNat (fp + 64) := by
    rw [u256_add_comm]
    simpa only [Nat.add_assoc] using u256_32_add_ofNat (fp + 32)
  have hfree : memLoad (UInt256.ofNat 64) mem = addressArrayFreePtr n :=
    memLoad_of_wordRead _ _ _ hm.freePtr
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_918_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_918_stack, hfree] at h₁
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_9876_packed (by simp; omega)
    (by jump_dest) h₁
  simp only [safeRuntime_block_9876_stack, safeRuntime_block_9876_memory, hfp, hfpadd] at h₂
  have hcount : memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) = UInt256.ofNat (32 * n) := by
    apply memLoad_of_wordRead
    change (writeWord mem fp ⟨32⟩).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by dsimp [fp]; omega, hm.lower⟩)]
    exact hm.count
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_9767_packed (by simp; omega)
    (by jump_dest) h₂
  change RD safeBytecode I g s0 ⟨9733⟩
    (⟨160⟩ :: (UInt256.ofNat (fp + 32) + UInt256.ofNat 32) ::
      memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) :: ⟨9790⟩ ::
      memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) :: ⟨0⟩ :: ⟨128⟩ ::
      UInt256.ofNat (fp + 32) :: ⟨6891⟩ :: ⟨0⟩ :: addressArrayFreePtr n :: ⟨128⟩ :: ⟨771⟩ :: R)
    (writeWord (writeWord mem fp ⟨32⟩) (UInt256.ofNat (fp + 32)).toNat
      (memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩))) aw₃ rdata σ k₃ C₃ at h₃
  rw [hcount, ha, ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)] at h₃
  have hwords := addressArrayHeaderWords mem fp words 160 hm.words hm.aligned
    (by decide) (by dsimp [fp]; omega) (by rw [hm.length]) (32 * n)
  have hmsize := addressArrayHeaderSize mem fp (32 * n) hm.upper
  have h₄ := safeRuntime_block_9733 (by simp; omega) h₃
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeWordBufferCopyLoop words (i := 0) (src := 160) h₄
    (by simp; omega) (by simpa using hwords) (by simpa using hmsize)
    (by dsimp [fp]; omega) (by rw [hm.length]; omega)
    (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  let encoded := addressArrayHeaderMemory mem fp (32 * n) ++ wordBytes words
  have hesize : encoded.size = fp + 64 + 32 * n := by
    dsimp [encoded]
    rw [ByteArray.size_append, hmsize, wordBytes_size, hm.length]
  have he : (UInt256.ofNat (32 * n) + UInt256.ofNat (fp + 64)).toNat = encoded.size := by
    rw [hesize]
    simpa only [Nat.add_comm] using
      (uadd_ofNat_toNat (a := 32 * n) (b := fp + 64)
        (by change 32 * n < 2 ^ 256; omega)
        (by change fp + 64 < 2 ^ 256; dsimp [fp]; omega)
        (by change 32 * n + (fp + 64) < 2 ^ 256; dsimp [fp]; omega))
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_9759_packed (by simp; omega)
    (by jump_dest) h₅
  simp only [safeRuntime_block_9759_stack, safeRuntime_block_9759_memory, he] at h₆
  change RD safeBytecode I g s0 ⟨9790⟩ _
    ((⟨0⟩ : UInt256).toByteArray.write 0 encoded encoded.size 32) aw₆ rdata σ k₆ C₆ at h₆
  rw [writeWordAtEnd encoded (⟨0⟩ : UInt256) rfl] at h₆
  have h₇ := safeRuntime_block_9790 (by simp; omega) (by jump_dest) h₆
  have hround := wordAlignedRoundUp (32 * n)
    (by change 32 * n + 31 < 2 ^ 256; omega) (by omega)
  simp only [safeRuntime_block_9790_stack, hround] at h₇
  have hendword : UInt256.ofNat 32 + (UInt256.ofNat (32 * n) + UInt256.ofNat (fp + 32)) =
      UInt256.ofNat (fp + 64 + 32 * n) := by
    apply u256_inj
    rw [← uadd_assoc]
    rw [uadd3_ofNat_toNat]
    · rw [ulit_toNat' _ (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)]
      omega
    all_goals change _ < 2 ^ 256; dsimp [fp]; omega
  rw [hendword] at h₇
  have h₈ := safeRuntime_block_6891 (by omega) (by jump_dest) h₇
  have hret := safeRuntime_block_771 (by omega) h₈
  have he64 : (encoded ++ (⟨0⟩ : UInt256).toByteArray).readWithPadding 64 32 =
      (addressArrayFreePtr n).toByteArray := by
    rw [readAppendPrefix _ _ _ (by rw [hesize]; dsimp [fp]; omega),
      readAppendPrefix _ _ _ (by rw [hmsize]; dsimp [fp]; omega),
      addressArrayHeaderRead _ _ _ _ (by have := hm.lower; omega) (by dsimp [fp]; omega)]
    exact hm.freePtr
  have hefree : memLoad (UInt256.ofNat 64) (encoded ++ (⟨0⟩ : UInt256).toByteArray) =
      addressArrayFreePtr n := memLoad_of_wordRead _ _ _ he64
  change RDret safeBytecode g s0 σ ((encoded ++ (⟨0⟩ : UInt256).toByteArray).readWithPadding
    (memLoad (UInt256.ofNat 64) (encoded ++ (⟨0⟩ : UInt256).toByteArray)).toNat
    (UInt256.sub (UInt256.ofNat (fp + 64 + 32 * n))
      (memLoad (UInt256.ofNat 64) (encoded ++ (⟨0⟩ : UInt256).toByteArray))).toNat) at hret
  have hend : (UInt256.ofNat (fp + 64 + 32 * n)).toNat = fp + 64 + 32 * n :=
    ulit_toNat' _ (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  rw [hefree, usub_toNat (by rw [hfp, hend]; omega), hfp, hend,
    show fp + 64 + 32 * n - fp = 64 + 32 * n by omega,
    readAppendPrefixLen _ _ _ _ (by rw [hesize]; omega)] at hret
  have hread := wordBufferEncodedRead mem fp (32 * n) words hm.upper
  rw [hm.length] at hread
  change encoded.readWithPadding fp (64 + 32 * n) = _ at hread
  rw [hread] at hret
  simpa only [wordBufferReturnBytes, hm.length] using hret

end Benchmarks.Safe
