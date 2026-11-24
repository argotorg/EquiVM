import Benchmarks.Safe.ViaIR.PreModuleCallMemory
import Benchmarks.Safe.ViaIR.CalldataDecodeArithmetic
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044
import Benchmarks.Safe.ViaIR.Blocks.Runtime_045

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safePreModuleEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {target value operation guard oldHash ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9899⟩
      (operation :: value :: guard :: UInt256.ofNat src :: ret :: oldHash :: target :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : mem.size ≤ ptr + 164) (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr)
    (hb : ptr + 228 + 32 * words.length < UInt256.size)
    (ho : operation.toNat < 2) (hov : R.length + 24 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9979⟩
      (UInt256.ofNat (ptr + 196 + 32 * words.length) :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat ptr :: guard :: UInt256.ofNat ptr :: ⟨32⟩ :: UInt256.ofNat ptr :: ret :: R)
      (writeWord (memoryBytesEncodedMemory
        (preModuleHeadMemory (writeWord mem ptr preModuleSelectorWord) (ptr + 4) target value)
        (ptr + 164) len words) (ptr + 100) operation) aw' rdata σ k' C' := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have hadd (n : Nat) (hh : ptr + n < UInt256.size) :
      UInt256.ofNat ptr + UInt256.ofNat n = UInt256.ofNat (ptr + n) :=
    wordOfNatAdd _ _ hh
  have ht (n : Nat) (hh : ptr + n < UInt256.size) :
      (UInt256.ofNat (ptr + n)).toNat = ptr + n := ulit_toNat' _ hh
  have hs : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
  let m := writeWord mem ptr preModuleSelectorWord
  have hsz : m.size = max mem.size (ptr + 32) := writeWord_sparse_size _ _ _
  have hhead : safeRuntime_block_9899_memory (mem := mem) (x1 := value) (x6 := target) =
      preModuleHeadMemory m (ptr + 4) target value := by
    simp only [safeRuntime_block_9899_memory, safeAddressMask, hf, hadd 4 (by omega),
      hadd 36 (by omega), hadd 68 (by omega), ht 4 (by omega), ht 36 (by omega),
      ht 68 (by omega), ulit_toNat' ptr (by omega), u256_land_comm solcAddrMask target]
    rfl
  have hload₀ : memLoad (UInt256.ofNat src) m = UInt256.ofNat len := by
    have hr := writeWordReadBelow mem ptr src 32 preModuleSelectorWord (by omega) (by omega)
    change m.readWithPadding src 32 = mem.readWithPadding src 32 at hr
    simpa only [memLoad, hs, if_neg (show ¬ src ≥ mem.size by omega),
      if_neg (show ¬ src ≥ m.size by omega), hr] using hl
  have hload : memLoad (UInt256.ofNat src) (preModuleHeadMemory m (ptr + 4) target value) =
      UInt256.ofNat len := by
    have hsize := preModuleHeadMemory_size m (ptr + 4) target value
    have hr := preModuleHeadMemory_preserved m (ptr + 4) src 32 target value
      (by omega) (by omega)
    simpa only [memLoad, hs, if_neg (show ¬ src ≥ m.size by omega),
      if_neg (show ¬ src ≥ (preModuleHeadMemory m (ptr + 4) target value).size by omega), hr]
      using hload₀
  have hwords : WordArrayMemory (preModuleHeadMemory m (ptr + 4) target value)
      (src + 32) words :=
    preModuleHeadMemory_words _ _ _ _ _ _
      (hw.writeAfter mem (src + 32) words hin ptr preModuleSelectorWord ha)
      (by omega) (by omega)
  have h₁ := safeRuntime_block_9899 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_9899_stack, hhead, hf, hadd 164 (by omega)] at h₁
  obtain ⟨aw', k', C', h₂⟩ := safeMemoryBytesEncode words h₁ hload hwords hn
    (by rw [preModuleHeadMemory_size]; omega)
    (by rw [preModuleHeadMemory_size]; omega) (by omega) (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_9968 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_9968_stack, hadd 100 (by omega)] at h₃
  have h₄ := safeRuntime_block_8837_fallthrough (by simp; omega) (by
    rw [ult_one (by exact ho)]; decide) h₃
  obtain ⟨aw'', k'', C'', h₅⟩ := safeRuntime_block_8848_packed (by simp; omega)
    (by jump_dest) h₄
  simp only [safeRuntime_block_8848_stack, safeRuntime_block_8848_memory,
    safeRuntime_block_8837_fallthrough_stack, ht 100 (by omega)] at h₅
  have he : ptr + 164 + 32 + 32 * words.length = ptr + 196 + 32 * words.length := by omega
  rw [he] at h₅
  exact ⟨_, _, _, h₅⟩

end Benchmarks.Safe.ViaIR
