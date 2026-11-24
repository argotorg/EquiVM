import Benchmarks.Safe.V3_77901a5.WordBufferCopy
import Benchmarks.Safe.V3_77901a5.RawBytesCopyMemory
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_051

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeRawBytesEncode {I g s0 σ k C aw mem rdata src dst n}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11834⟩
      (UInt256.ofNat dst :: UInt256.ofNat src :: ret :: R) mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat (32 * n + 4))
    (hd : dst ≤ mem.size) (ha : src + 32 + 32 * n + 4 ≤ dst)
    (hb : dst + 32 * n + 64 < UInt256.size)
    (hov : R.length + 13 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      (UInt256.ofNat (dst + 32 * n + 4) :: R)
      (rawBytesCopyMemory mem src dst n) aw' rdata σ k' C' := by
  have hs32 : UInt256.ofNat src + UInt256.ofNat 32 = UInt256.ofNat (src + 32) := by
    rw [u256_add_comm]; exact u256_32_add_ofNat src
  have h₁ := safeRuntime_block_11834 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11834_stack, hl, hs32] at h₁
  have h₂ := safeRuntime_block_9733 (by simp; omega) h₁
  simp only [safeRuntime_block_9733_stack] at h₂
  obtain ⟨_, _, _, h₃⟩ := safeByteBufferCopyPrefix
    (memoryWords mem (src + 32) n) (i := 0) h₂ (by simp; omega) (by omega)
    (by simpa using memoryWords_view mem (src + 32) n) (by omega)
    (by rw [memoryWords_length]; omega)
    (by rw [memoryWords_length]; omega) (by rw [memoryWords_length]; omega)
  simp only [Nat.zero_add, Nat.add_zero, memoryWords_length] at h₃
  have hlt : UInt256.lt (UInt256.ofNat (32 * n)) (UInt256.ofNat (32 * n + 4)) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ (by omega)]; omega)
  have h₄ := safeRuntime_block_9735_fallthrough (by simp; omega)
    (by rw [hlt]; decide) h₃
  have h₅ := safeRuntime_block_9744 (by simp; omega) (by jump_dest) h₄
  have hs : UInt256.ofNat (32 * n) + UInt256.ofNat (src + 32) =
      UInt256.ofNat (src + 32 + 32 * n) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact (uadd_ofNat_toNat (a := 32 * n) (b := src + 32)
      (by omega) (by omega) (by omega)).trans (by omega)
  have hd' : (UInt256.ofNat (32 * n) + UInt256.ofNat dst).toNat = dst + 32 * n :=
    (uadd_ofNat_toNat (a := 32 * n) (b := dst)
      (by omega) (by omega) (by omega)).trans (by omega)
  have hw : memLoad (UInt256.ofNat (src + 32 + 32 * n))
      (rawBytesCopyPrefix mem src dst n) = rawBytesCopyLast mem src dst n := by
    rw [memLoadReadWord, ulit_toNat' _ (by omega)]
    rfl
  have hinc : UInt256.ofNat 32 + UInt256.ofNat (32 * n) =
      UInt256.ofNat (32 * n + 32) := u256_32_add_ofNat (32 * n)
  change memLoad (UInt256.ofNat (src + 32 + 32 * n))
      (writeWords mem dst (memoryWords mem (src + 32) n)) = _ at hw
  simp only [safeRuntime_block_9744_stack, safeRuntime_block_9744_memory, hs, hd',
    hinc, hw] at h₅
  have hge : UInt256.lt (UInt256.ofNat (32 * n + 32)) (UInt256.ofNat (32 * n + 4)) = ⟨0⟩ :=
    ult_zero (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ (by omega)]; omega)
  have h₆ := safeRuntime_block_9735_taken (by simp; omega)
    (by rw [hge]; decide) (by jump_dest) h₅
  have h₇ := safeRuntime_block_9759 (by simp; omega) (by jump_dest) h₆
  have he : (UInt256.ofNat (32 * n + 4) + UInt256.ofNat dst).toNat = dst + 32 * n + 4 :=
    (uadd_ofNat_toNat (a := 32 * n + 4) (b := dst)
      (by omega) (by omega) (by omega)).trans (by omega)
  simp only [safeRuntime_block_9759_stack, safeRuntime_block_9759_memory, he] at h₇
  have h₈ := safeRuntime_block_11851 (by simp; omega) hret h₇
  have heword : UInt256.ofNat (32 * n + 4) + UInt256.ofNat dst =
      UInt256.ofNat (dst + 32 * n + 4) := by
    apply u256_inj
    rw [he, ulit_toNat' _ (by omega)]
  simp only [safeRuntime_block_11851_stack, heword] at h₈
  exact ⟨_, _, _, h₈⟩

end Benchmarks.Safe.V3_77901a5
