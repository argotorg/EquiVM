import Benchmarks.Safe.PreModuleEncodingMemory
import Benchmarks.Safe.Blocks.Runtime_049
import Benchmarks.Safe.Blocks.Runtime_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safePreModuleEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata base src len} {target value operation sender ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11707⟩
      (UInt256.ofNat base :: sender :: operation :: UInt256.ofNat src :: value ::
        target :: ret :: R) mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : mem.size ≤ base + 160) (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ base)
    (hb : base + 224 + 32 * words.length < UInt256.size)
    (ho : operation.toNat < 2) (hov : R.length + 21 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat (base + 192 + 32 * words.length) :: R)
      (preModuleArgsMemory mem base len target value operation sender words)
      aw' rdata σ k' C' := by
  have hadd (n : Nat) (hh : base + n < UInt256.size) :
      UInt256.ofNat base + UInt256.ofNat n = UInt256.ofNat (base + n) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  have ht (n : Nat) (hh : base + n < UInt256.size) :
      (UInt256.ofNat (base + n)).toNat = base + n := ulit_toNat' _ hh
  have hs : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
  have hhead : safeRuntime_block_11707_memory (mem := mem) (x0 := UInt256.ofNat base)
      (x4 := value) (x5 := target) = preModuleHeadMemory mem base target value := by
    simp only [safeRuntime_block_11707_memory, safeAddressMask, hadd 32 (by omega),
      hadd 64 (by omega), ht 32 (by omega), ht 64 (by omega), ulit_toNat' base (by omega)]
    rfl
  have hload : memLoad (UInt256.ofNat src) (preModuleHeadMemory mem base target value) =
      UInt256.ofNat len := by
    have hsize := preModuleHeadMemory_size mem base target value
    have hr := preModuleHeadMemory_preserved mem base src 32 target value (by omega) (by omega)
    simpa only [memLoad, hs, if_neg (show ¬ src ≥ mem.size by omega),
      if_neg (show ¬ src ≥ (preModuleHeadMemory mem base target value).size by omega), hr]
      using hl
  have h₁ := safeRuntime_block_11707 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11707_stack, hhead, hadd 160 (by omega)] at h₁
  obtain ⟨aw', k', C', h₂⟩ := safeMemoryBytesEncode words h₁ hload
    (preModuleHeadMemory_words _ _ _ _ _ _ hw hin ha) hn
    (by rw [preModuleHeadMemory_size]; omega)
    (by rw [preModuleHeadMemory_size]; omega) (by omega) (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_11745 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_11745_stack, hadd 96 (by omega)] at h₃
  have hcond : UInt256.lt operation (UInt256.ofNat 2) ≠ UInt256.ofNat 0 := by
    simp [UInt256.lt, UInt256.fromBool, show operation < UInt256.ofNat 2 from ho]
    decide
  have h₄ := safeRuntime_block_11224_taken (by simp; omega) hcond (by jump_dest) h₃
  have h₅ := safeRuntime_block_11252 (by simp; omega) (by jump_dest) h₄
  simp only [safeRuntime_block_11252_stack, safeRuntime_block_11252_memory,
    ht 96 (by omega)] at h₅
  have h₆ := safeRuntime_block_11760 (by simp; omega) hret h₅
  simp only [safeRuntime_block_11760_stack, safeRuntime_block_11760_memory,
    safeAddressMask] at h₆
  rw [show UInt256.ofNat 128 + UInt256.ofNat base = UInt256.ofNat (base + 128) by
    rw [u256_add_comm]; exact hadd 128 (by omega)] at h₆
  simp only [ht 128 (by omega)] at h₆
  have he : base + 160 + 32 + 32 * words.length = base + 192 + 32 * words.length := by omega
  rw [he] at h₆
  exact ⟨_, _, _, h₆⟩

end Benchmarks.Safe
