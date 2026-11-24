import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.WordBufferEncoding
import Benchmarks.Safe.ViaIR.WordBufferCopy
import Benchmarks.Safe.ViaIR.Blocks.Runtime_029
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

set_option maxHeartbeats 800000 in
theorem safeStorageAtReturnTrace {I g s0 σ k C aw mem rdata n words offset} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6173⟩
      (UInt256.ofNat n :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R) mem aw rdata σ k C)
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
  have hfree : memLoad (UInt256.ofNat 64) mem = addressArrayFreePtr n :=
    memLoad_of_wordRead _ _ _ hm.freePtr
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_6173_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_6173_stack, safeRuntime_block_6173_memory,
    hfree, hfp, hfpadd] at h₁
  have hcount : memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)) =
      UInt256.ofNat (32 * n) := by
    apply memLoad_of_wordRead
    change (writeWord mem fp (UInt256.ofNat 32)).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by dsimp [fp]; omega, hm.lower⟩)]
    exact hm.count
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_7374_packed (by simp; omega) h₁
  simp only [safeRuntime_block_7374_stack, safeRuntime_block_7374_memory] at h₂
  change RD fork safeBytecode I g s0 ⟨7384⟩
    (⟨0⟩ :: ⟨128⟩ :: UInt256.ofNat (fp + 32) :: UInt256.ofNat 585 ::
      memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)) ::
      addressArrayFreePtr n :: addressArrayFreePtr n :: UInt256.ofNat n ::
      offset :: UInt256.ofNat n :: ⟨128⟩ :: R)
    (writeWord (writeWord mem fp (UInt256.ofNat 32)) (UInt256.ofNat (fp + 32)).toNat
      (memLoad ⟨128⟩ (writeWord mem fp (UInt256.ofNat 32)))) aw₂ rdata σ k₂ C₂ at h₂
  rw [hcount, ulit_toNat' _ (by change fp + 32 < 2 ^ 256; dsimp [fp]; omega)] at h₂
  have hwords := addressArrayHeaderWords mem fp words 160 hm.words hm.aligned
    (by decide) (by dsimp [fp]; omega) (by rw [hm.length]) (32 * n)
  have hmsize := addressArrayHeaderSize mem fp (32 * n) hm.upper
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeWordBufferCopyLoop words (i := 0) (src := 128) h₂
    (by simp; omega) (by simpa using hwords)
    (by simpa only [Nat.add_zero, Nat.add_assoc] using hmsize)
    (by dsimp [fp]; omega) (by rw [hm.length]; omega)
    (by change fp + 32 + 32 * n + 32 < 2 ^ 256; dsimp [fp]; omega)
  let encoded := addressArrayHeaderMemory mem fp (32 * n) ++ wordBytes words
  have hesize : encoded.size = fp + 64 + 32 * n := by
    dsimp [encoded]
    rw [ByteArray.size_append, hmsize, wordBytes_size, hm.length]
  have he : ((UInt256.ofNat (fp + 32) + UInt256.ofNat (32 * n)) +
      UInt256.ofNat 32).toNat = encoded.size := by
    rw [hesize, uadd3_ofNat_toNat]
    · omega
    all_goals change _ < 2 ^ 256; dsimp [fp]; omega
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_7392_packed (by simp; omega)
    (by jump_dest) h₅
  simp only [safeRuntime_block_7392_stack, safeRuntime_block_7392_memory, he] at h₆
  change RD fork safeBytecode I g s0 ⟨585⟩ _
    ((⟨0⟩ : UInt256).toByteArray.write 0 encoded encoded.size 32) aw₆ rdata σ k₆ C₆ at h₆
  rw [writeWordAtEnd encoded (⟨0⟩ : UInt256) rfl] at h₆
  have hround : UInt256.land (UInt256.ofNat (32 * n) + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (32 * n) := by
    rw [u256_land_comm, u256_add_comm (UInt256.ofNat (32 * n))]
    exact wordAlignedRoundUp (32 * n) (by change 32 * n + 31 < 2 ^ 256; omega) (by omega)
  rw [hround] at h₆
  have hendword : (UInt256.ofNat (32 * n) + UInt256.ofNat (fp + 32)) + UInt256.ofNat 32 =
      UInt256.ofNat (fp + 64 + 32 * n) := by
    apply u256_inj
    rw [uadd3_ofNat_toNat]
    · rw [ulit_toNat' _ (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)]
      omega
    all_goals change _ < 2 ^ 256; dsimp [fp]; omega
  rw [hendword] at h₆
  have hret := safeRuntime_block_585 (by simp; omega) h₆
  change RDret fork safeBytecode g s0 σ ((encoded ++ (⟨0⟩ : UInt256).toByteArray).readWithPadding
    (addressArrayFreePtr n).toNat
    (UInt256.sub (UInt256.ofNat (fp + 64 + 32 * n)) (addressArrayFreePtr n)).toNat) at hret
  have hend : (UInt256.ofNat (fp + 64 + 32 * n)).toNat = fp + 64 + 32 * n :=
    ulit_toNat' _ (by change fp + 64 + 32 * n < 2 ^ 256; dsimp [fp]; omega)
  rw [usub_toNat (by rw [hfp, hend]; omega), hfp, hend,
    show fp + 64 + 32 * n - fp = 64 + 32 * n by omega,
    readAppendPrefixLen _ _ _ _ (by rw [hesize]; omega)] at hret
  have hread := wordBufferEncodedRead mem fp (32 * n) words hm.upper
  rw [hm.length] at hread
  change encoded.readWithPadding fp (64 + 32 * n) = _ at hread
  rw [hread] at hret
  simpa only [wordBufferReturnBytes, hm.length] using hret

end Benchmarks.Safe.ViaIR
