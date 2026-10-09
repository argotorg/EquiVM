import Benchmarks.Safe.Memory
import Benchmarks.Safe.Blocks.Runtime_050
import Benchmarks.Safe.Blocks.Runtime_051
import Benchmarks.Safe.Blocks.Runtime_030
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

-- GENERALIZES the shared solc bool decoder to arbitrary input-buffer and return pointers.
theorem safeBoolDecoderHead {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11632⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255) :
    ∃ k' C', RD safeBytecode I g s0 ⟨11648⟩
      (⟨0⟩ :: start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k' C' := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨0⟩ := by
    apply slt_lit_zero (by decide)
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]
      exact hl
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]
      exact hb
  exact ⟨_, _, safeRuntime_block_11632_taken (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) (by jump_dest) h⟩

theorem safeBoolDecoderShort {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11632⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : len < 32) : RDrev safeBytecode g s0 := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨1⟩ := by
    apply slt_lit_one_low (by decide)
    rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]
    exact hl
  have hr := safeRuntime_block_11632_fallthrough (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) h
  exact safeRuntime_block_11645 (by simp [safeRuntime_block_11632_fallthrough_stack]; omega) hr

theorem safeBoolDecoderValid {I g s0 σ k C aw mem rdata} {start ret word : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11632⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255)
    (hm : memLoad start mem = word) (hw : word = ⟨0⟩ ∨ word = ⟨1⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret (word :: R) mem aw' rdata σ k' C' := by
  obtain ⟨_, _, hd⟩ := safeBoolDecoderHead h hov hl hb
  have hr := safeRuntime_block_11648_taken (by simp; omega)
    (by rw [hm]; rcases hw with rfl | rfl <;> decide) (by jump_dest) hd
  have he := safeRuntime_block_6891 (by omega) hret hr
  exact ⟨_, _, _, by simpa only [safeRuntime_block_6891_stack,
    safeRuntime_block_11648_taken_stack, hm] using he⟩

theorem safeBoolDecoderNoncanon {I g s0 σ k C aw mem rdata} {start ret word : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11632⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255)
    (hm : memLoad start mem = word) (hz : word ≠ ⟨0⟩) (ho : word ≠ ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, hd⟩ := safeBoolDecoderHead h (by omega) hl hb
  have hr := safeRuntime_block_11648_fallthrough (by simp; omega)
    (by rw [hm, isZero_eq_zero_of_ne hz]
        change UInt256.eq word ⟨1⟩ = ⟨0⟩
        exact uInt256_eq_zero_of_ne (fun he ↦ ho (uInt256_eq_one_eq he))) hd
  exact safeRuntime_block_11660 (by simp [safeRuntime_block_11648_fallthrough_stack]; omega) hr

end Benchmarks.Safe
