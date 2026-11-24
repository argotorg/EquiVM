import Benchmarks.Safe.ViaIR.PreModuleEncode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safePreModuleCallPrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {oldHash guard target value operation ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9899⟩
      (operation :: value :: UInt256.land guard solcAddrMask :: UInt256.ofNat src ::
        ret :: oldHash :: target :: guard :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : 96 ≤ mem.size) (hu : mem.size ≤ ptr + 164) (hp : 96 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr)
    (hb : ptr + 228 + 32 * words.length < UInt256.size)
    (ho : operation.toNat < 2) (hov : R.length + 29 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨9989⟩
      (gasArg :: UInt256.land guard solcAddrMask :: ⟨0⟩ :: UInt256.ofNat ptr ::
        UInt256.ofNat (196 + 32 * words.length) :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat ptr :: ret :: guard :: R)
      (preModuleCallMemory mem ptr len target value operation (UInt256.ofNat I.source.val) words)
      aw' rdata σ k' C' := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safePreModuleEncode words h hf hl hw hn hu hin ha hb ho
    (by simp; omega)
  have hadd (n : Nat) (hh : ptr + n < UInt256.size) :
      UInt256.ofNat ptr + UInt256.ofNat n = UInt256.ofNat (ptr + n) :=
    wordOfNatAdd _ _ hh
  have hsender : UInt256.land solcAddrMask (UInt256.ofNat I.source.val) =
      UInt256.ofNat I.source.val := by
    rw [u256_land_comm]
    apply solcAddrMask_clean
    rw [ulit_toNat' _ (lt_trans I.source.isLt (by decide))]
    exact I.source.isLt
  let m := writeWord (memoryBytesEncodedMemory
    (preModuleHeadMemory (writeWord mem ptr preModuleSelectorWord) (ptr + 4) target value)
    (ptr + 164) len words) (ptr + 100) operation
  have hmem : safeRuntime_block_9979_memory (ee := I) (mem := m)
      (x1 := UInt256.ofNat ptr) =
      preModuleCallMemory mem ptr len target value operation (UInt256.ofNat I.source.val)
        words := by
    simp only [safeRuntime_block_9979_memory, hadd 132 (by omega),
      ulit_toNat' (ptr + 132) (by omega), preModuleCallMemory, preModuleArgsMemory, hsender]
    rfl
  have h₂ := safeRuntime_block_9979 (by simp; omega) h₁
  rw [hmem] at h₂
  simp only [safeRuntime_block_9979_stack] at h₂
  have hsub : UInt256.sub (UInt256.ofNat (ptr + 196 + 32 * words.length))
      (UInt256.ofNat ptr) = UInt256.ofNat (196 + 32 * words.length) := by
    rw [show ptr + 196 + 32 * words.length = ptr + (196 + 32 * words.length) by omega,
      ← hadd _ (by omega), word_add_sub_left]
  rw [hsub] at h₂
  exact ⟨_, _, _, _, h₂⟩

end Benchmarks.Safe.ViaIR
