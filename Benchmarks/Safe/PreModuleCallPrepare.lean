import Benchmarks.Safe.PreModuleEncode
import Benchmarks.Safe.PreModuleCallMemory
import Benchmarks.Safe.Blocks.Runtime_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safePreModuleCallPrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {oldHash guard target value operation : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7281⟩
      (oldHash :: guard :: operation :: UInt256.ofNat src :: value :: target :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : 96 ≤ mem.size) (hu : mem.size ≤ ptr + 164) (hp : 96 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr)
    (hb : ptr + 228 + 32 * words.length < UInt256.size)
    (ho : operation.toNat < 2) (hov : R.length + 29 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨7345⟩
      (gasArg :: UInt256.land guard solcAddrMask :: ⟨0⟩ :: UInt256.ofNat ptr ::
        UInt256.ofNat (196 + 32 * words.length) :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat (ptr + 196 + 32 * words.length) :: ⟨1921788274⟩ ::
        UInt256.land guard solcAddrMask :: oldHash :: guard :: operation ::
        UInt256.ofNat src :: value :: target :: R)
      (preModuleCallMemory mem ptr len target value operation (UInt256.ofNat I.source.val) words)
      aw' rdata σ k' C' := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have hpt : (UInt256.ofNat ptr).toNat = ptr := ulit_toNat' _ (by omega)
  have hst : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
  have hadd (n : Nat) (hh : ptr + n < UInt256.size) :
      UInt256.ofNat ptr + UInt256.ofNat n = UInt256.ofNat (ptr + n) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  let m := writeWord mem ptr preModuleSelectorWord
  have hsz : m.size = max mem.size (ptr + 32) := writeWord_sparse_size _ _ _
  have hload : memLoad (UInt256.ofNat src) m = UInt256.ofNat len := by
    have hr := writeWordReadBelow mem ptr src 32 preModuleSelectorWord (by omega) (by omega)
    change m.readWithPadding src 32 = mem.readWithPadding src 32 at hr
    simpa only [memLoad, hst, if_neg (show ¬ src ≥ mem.size by omega),
      if_neg (show ¬ src ≥ m.size by omega), hr] using hl
  have h₁ := safeRuntime_block_7281 (by simp; omega) (by jump_dest) h
  have h4 : UInt256.ofNat 4 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 4) := by
    rw [u256_add_comm]; exact hadd 4 (by omega)
  simp only [safeRuntime_block_7281_stack, safeRuntime_block_7281_memory,
    safeAddressMask, hf, hpt, h4] at h₁
  change RD safeBytecode I g s0 _ _ m _ _ _ _ _ at h₁
  obtain ⟨aw', k', C', h₂⟩ := safePreModuleEncode words h₁ hload
    (hw.writeAfter mem (src + 32) words hin ptr preModuleSelectorWord ha) hn
    (by omega) (by omega)
    (by omega) (by omega) ho (by simp; omega) (by jump_dest)
  change RD safeBytecode I g s0 _ _
    (preModuleCallMemory mem ptr len target value operation (UInt256.ofNat I.source.val) words)
    _ _ _ _ _ at h₂
  have he : ptr + 4 + 192 + 32 * words.length = ptr + 196 + 32 * words.length := by omega
  rw [he] at h₂
  have hfree : memLoad (UInt256.ofNat 64)
      (preModuleCallMemory mem ptr len target value operation (UInt256.ofNat I.source.val) words) =
      UInt256.ofNat ptr :=
    (preModuleCallMemory_free mem ptr len target value operation
      (UInt256.ofNat I.source.val) words hm hp).trans hf
  have h₃ := safeRuntime_block_7332 (by simp; omega) h₂
  simp only [safeRuntime_block_7332_stack, hfree] at h₃
  have hsub : UInt256.sub (UInt256.ofNat (ptr + 196 + 32 * words.length))
      (UInt256.ofNat ptr) = UInt256.ofNat (196 + 32 * words.length) := by
    rw [show ptr + 196 + 32 * words.length = ptr + (196 + 32 * words.length) by omega,
      ← hadd _ (by omega), word_add_sub_left]
  rw [hsub] at h₃
  exact ⟨_, _, _, _, h₃⟩

end Benchmarks.Safe
