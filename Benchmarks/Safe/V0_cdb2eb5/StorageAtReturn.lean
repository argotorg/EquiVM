import Benchmarks.Safe.V0_cdb2eb5.AddressArrayMemory
import Benchmarks.Safe.V0_cdb2eb5.WordBufferEncoding
import Benchmarks.Safe.V0_cdb2eb5.WordBufferCopy
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_007
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_008
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 2000

set_option maxHeartbeats 800000 in
theorem safeStorageAtReturnTrace {I g s0 σ k C aw mem rdata n words} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨918⟩ (⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024)
    (hm : AddressArrayMemory mem n words (UInt256.ofNat (32 * n)))
    (hn : n ≤ 2 ^ 64 - 1) :
    RDret fork safeBytecode g s0 σ (wordBufferReturnBytes words) := by
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
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_9745_packed (by simp; omega)
    (by jump_dest) h₁
  simp only [safeRuntime_block_9745_stack, safeRuntime_block_9745_memory, hfp, hfpadd] at h₂
  have hcount : memLoad ⟨128⟩ (writeWord mem fp ⟨32⟩) = UInt256.ofNat (32 * n) := by
    apply memLoad_of_wordRead
    change (writeWord mem fp ⟨32⟩).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by dsimp [fp]; omega, hm.lower⟩)]
    exact hm.count
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_9612_packed (by simp; omega) h₂
  simp only [safeRuntime_block_9612_stack, safeRuntime_block_9612_memory, hcount,
    ulit_toNat' (fp + 32) (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)] at h₃
  change memLoad ⟨128⟩ ((UInt256.ofNat 32).toByteArray.write 0 mem fp 32) = _ at hcount
  rw [hcount] at h₃
  have hwords := addressArrayHeaderWords mem fp words 160 hm.words hm.aligned
    (by decide) (by dsimp [fp]; omega) (by rw [hm.length]) (32 * n)
  have hmsize := addressArrayHeaderSize mem fp (32 * n) hm.upper
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeWordBufferCopyLoop words (i := 0) (src := 128) (dst := fp + 32) h₃
    (by simp; omega) (by simpa using hwords) (by simpa using hmsize)
    (by dsimp [fp]; omega) (by rw [hm.length]; omega)
    (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  let encoded := addressArrayHeaderMemory mem fp (32 * n) ++ wordBytes words
  have hesize : encoded.size = fp + 64 + 32 * n := by
    dsimp [encoded]
    rw [ByteArray.size_append, hmsize, wordBytes_size, hm.length]
  have he : ((UInt256.ofNat (fp + 32) + UInt256.ofNat (32 * n)) +
      UInt256.ofNat 32).toNat = encoded.size := by
    rw [hesize, uadd3_ofNat_toNat]
    · omega
    all_goals change _ < 2 ^ 256; dsimp [fp]; omega
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_9648_packed (by simp; omega)
    (by jump_dest) h₅
  simp only [safeRuntime_block_9648_stack, safeRuntime_block_9648_memory, he] at h₆
  change RD fork safeBytecode I g s0 ⟨7075⟩ _
    ((⟨0⟩ : UInt256).toByteArray.write 0 encoded encoded.size 32) aw₆ rdata σ k₆ C₆ at h₆
  rw [writeWordAtEnd encoded (⟨0⟩ : UInt256) rfl] at h₆
  have hround := wordAlignedRoundUp (32 * n)
    (by change 32 * n + 31 < 2 ^ 256; omega) (by omega)
  rw [u256_land_comm, u256_add_comm (UInt256.ofNat (32 * n)), hround] at h₆
  have hendword : (UInt256.ofNat (fp + 32) + UInt256.ofNat (32 * n)) + UInt256.ofNat 32 =
      UInt256.ofNat (fp + 64 + 32 * n) := by
    apply u256_inj
    rw [uadd3_ofNat_toNat]
    · rw [ulit_toNat' _ (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)]
      omega
    all_goals change _ < 2 ^ 256; dsimp [fp]; omega
  rw [hendword] at h₆
  have h₈ := safeRuntime_block_7075 (by omega) (by jump_dest) h₆
  have hret := safeRuntime_block_771 (by omega) h₈
  have he64 : (encoded ++ (⟨0⟩ : UInt256).toByteArray).readWithPadding 64 32 =
      (addressArrayFreePtr n).toByteArray := by
    rw [readAppendPrefix _ _ _ (by rw [hesize]; dsimp [fp]; omega),
      readAppendPrefix _ _ _ (by rw [hmsize]; dsimp [fp]; omega),
      addressArrayHeaderRead _ _ _ _ (by have := hm.lower; omega) (by dsimp [fp]; omega)]
    exact hm.freePtr
  have hefree : memLoad (UInt256.ofNat 64) (encoded ++ (⟨0⟩ : UInt256).toByteArray) =
      addressArrayFreePtr n := memLoad_of_wordRead _ _ _ he64
  change RDret fork safeBytecode g s0 σ ((encoded ++ (⟨0⟩ : UInt256).toByteArray).readWithPadding
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

end Benchmarks.Safe.V0_cdb2eb5
