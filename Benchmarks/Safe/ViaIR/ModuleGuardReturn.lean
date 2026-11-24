import Benchmarks.Safe.ViaIR.GuardReturn
import Benchmarks.Safe.ViaIR.Blocks.Runtime_010
import Benchmarks.Safe.ViaIR.Blocks.Runtime_011

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeModuleGuardCallFailureTrace {I g s0 σ k C aw mem rdata ptr guard} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1929⟩
      (⟨0⟩ :: ptr :: guard :: guard :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_1929_taken (by simp; omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_1705 (by omega)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
        show (Fin.ofNat _ rdata.size).val ≤ rdata.size
        simp only [Fin.ofNat]
        exact Nat.mod_le _ _) hr

theorem safeModuleGuardReturnStart {I g s0 σ k C aw out guard} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1929⟩
      (⟨1⟩ :: ⟨128⟩ :: guard :: guard :: ⟨0⟩ :: R)
      (guardOutputMemory .moduleGuard out) aw out σ k C)
    (hov : R.length + 14 ≤ 1024) (hb : out.size < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1974⟩ ::
        guard :: guard :: ⟨0⟩ :: R)
      (guardDecodedMemory .moduleGuard out) aw' out σ k' C' := by
  have h1936 := safeRuntime_block_1929_fallthrough (by simp; omega) (by decide) h
  simp only [safeRuntime_block_1929_fallthrough_stack] at h1936
  have h1949 := safeRuntime_block_1936_taken (by simp; omega) (by decide)
    (by jump_dest) h1936
  simp only [safeRuntime_block_1936_taken_stack] at h1949
  have h7128 : ∃ k' C', RD fork safeBytecode I g s0 ⟨7128⟩
      (⟨128⟩ :: UInt256.ofNat (min 32 out.size) :: ⟨1684⟩ ::
        UInt256.ofNat (min 32 out.size) :: ⟨128⟩ :: ⟨1974⟩ :: guard :: guard :: ⟨0⟩ :: R)
      (guardOutputMemory .moduleGuard out) aw out σ k' C' := by
    by_cases hl : 32 ≤ out.size
    · have ht := safeRuntime_block_1949_fallthrough (by simp; omega)
        (ugt_zero (by rw [ulit_toNat' _ hb]; exact hl)) h1949
      have hf := safeRuntime_block_1965 (by simp; omega) (by jump_dest) ht
      rw [Nat.min_eq_left hl]
      exact ⟨_, _, hf⟩
    · have ht := safeRuntime_block_1949_taken (by simp; omega)
        (by rw [ugt_one (by rw [ulit_toNat' _ hb]; change out.size < 32; omega)]; decide)
        (by jump_dest) h1949
      have hf := safeRuntime_block_1698 (by simp; omega) (by jump_dest) ht
      have he := safeRuntime_block_1674 (by simp; omega) (by jump_dest) hf
      rw [Nat.min_eq_right (by omega)]
      exact ⟨_, _, he⟩
  obtain ⟨_, _, h7128⟩ := h7128
  exact safeGuardReturnAllocate h7128 (by simp; omega) (Nat.min_le_left _ _)

theorem safeModuleGuardSupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1770⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨1775⟩ R mem aw rdata σ k' C' :=
  ⟨_, _, safeRuntime_block_1770_fallthrough hov (by decide) h⟩

theorem safeModuleGuardUnsupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1770⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_1770_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_1847
    (by simp only [safeRuntime_block_1770_taken_stack]; omega) hr

theorem safeModuleGuardReturnTrue {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1974⟩ :: R)
      (guardDecodedMemory .moduleGuard out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨1775⟩ R
      (guardDecodedMemory .moduleGuard out) aw' out σ k' C' := by
  obtain ⟨aw', k', C', hd⟩ := safeBoolDecoderValid h hov (by omega) (by omega)
    (guardDecodedMemory_word (kind := .moduleGuard) out hl) (.inr hw) (by jump_dest)
  rw [hw] at hd
  have h1942 := safeRuntime_block_1974 (by simp; omega) (by jump_dest) hd
  have h1770 := safeRuntime_block_1942 (by simp; omega) (by jump_dest) h1942
  obtain ⟨k'', C'', he⟩ := safeModuleGuardSupported h1770 (by omega)
  exact ⟨aw', k'', C'', he⟩

theorem safeModuleGuardReturnFalse {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1974⟩ :: R)
      (guardDecodedMemory .moduleGuard out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, hd⟩ := safeBoolDecoderValid h hov (by omega) (by omega)
    (guardDecodedMemory_word (kind := .moduleGuard) out hl) (.inl hw) (by jump_dest)
  rw [hw] at hd
  have h1942 := safeRuntime_block_1974 (by simp; omega) (by jump_dest) hd
  have h1770 := safeRuntime_block_1942 (by simp; omega) (by jump_dest) h1942
  exact safeModuleGuardUnsupported h1770 (by omega)

end Benchmarks.Safe.ViaIR
