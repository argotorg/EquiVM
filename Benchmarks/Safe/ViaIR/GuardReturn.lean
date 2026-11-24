import Benchmarks.Safe.ViaIR.GuardCallMemory
import Benchmarks.Safe.ViaIR.BoolReturnDecoder
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008
import Benchmarks.Safe.ViaIR.Blocks.Runtime_009
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeGuardCallFailureTrace {I g s0 σ k C aw mem rdata ptr guard} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1638⟩
      (⟨0⟩ :: ptr :: guard :: guard :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_1638_taken (by simp; omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_1705 (by omega)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
        show (Fin.ofNat _ rdata.size).val ≤ rdata.size
        simp only [Fin.ofNat]
        exact Nat.mod_le _ _) hr

-- The fixed one-word output buffer bounds the IR allocation independently of return-data size.
theorem safeGuardReturnAllocate {I g s0 σ k C aw mem rdata len ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7128⟩
      (⟨128⟩ :: UInt256.ofNat len :: ⟨1684⟩ :: UInt256.ofNat len :: ⟨128⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hlen : len ≤ 32) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat len) :: ret :: R)
      (writeWord mem 64 (⟨128⟩ + UInt256.land (UInt256.ofNat len + UInt256.ofNat 31)
        (UInt256.lnot (UInt256.ofNat 31)))) aw' rdata σ k' C' := by
  have h7157 := safeRuntime_block_7128_fallthrough (by simp; omega)
    (by interval_cases len <;> decide) h
  obtain ⟨aw', k', C', h1684⟩ := safeRuntime_block_7157_packed (by simp; omega)
    (by jump_dest) h7157
  simp only [safeRuntime_block_7157_stack, safeRuntime_block_7157_memory] at h1684
  have hout := safeRuntime_block_1684 (by simp; omega) (by jump_dest) h1684
  exact ⟨_, _, _, hout⟩

theorem safeGuardReturnStart {I g s0 σ k C aw out guard} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1638⟩
      (⟨1⟩ :: ⟨128⟩ :: guard :: guard :: ⟨0⟩ :: R)
      (guardOutputMemory .transaction out) aw out σ k C)
    (hov : R.length + 14 ≤ 1024) (hb : out.size < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1692⟩ ::
        guard :: guard :: ⟨0⟩ :: R)
      (guardDecodedMemory .transaction out) aw' out σ k' C' := by
  have h1645 := safeRuntime_block_1638_fallthrough (by simp; omega) (by decide) h
  simp only [safeRuntime_block_1638_fallthrough_stack] at h1645
  have h1658 := safeRuntime_block_1645_taken (by simp; omega) (by decide)
    (by jump_dest) h1645
  simp only [safeRuntime_block_1645_taken_stack] at h1658
  have h1674 : ∃ k' C', RD fork safeBytecode I g s0 ⟨1674⟩
      (UInt256.ofNat (min 32 out.size) :: ⟨128⟩ :: ⟨1692⟩ :: guard :: guard :: ⟨0⟩ :: R)
      (guardOutputMemory .transaction out) aw out σ k' C' := by
    by_cases hl : 32 ≤ out.size
    · have ht := safeRuntime_block_1658_fallthrough (by simp; omega)
        (ugt_zero (by rw [ulit_toNat' _ hb]; exact hl)) h1658
      rw [Nat.min_eq_left hl]
      exact ⟨_, _, ht⟩
    · have ht := safeRuntime_block_1658_taken (by simp; omega)
        (by rw [ugt_one (by rw [ulit_toNat' _ hb]; change out.size < 32; omega)]; decide)
        (by jump_dest) h1658
      have hf := safeRuntime_block_1698 (by simp; omega) (by jump_dest) ht
      rw [Nat.min_eq_right (by omega)]
      exact ⟨_, _, hf⟩
  obtain ⟨_, _, h1674⟩ := h1674
  have h7128 := safeRuntime_block_1674 (by simp; omega) (by jump_dest) h1674
  exact safeGuardReturnAllocate h7128 (by simp; omega) (Nat.min_le_left _ _)

theorem safeGuardSupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1479⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨1484⟩ R mem aw rdata σ k' C' :=
  ⟨_, _, safeRuntime_block_1479_fallthrough hov (by decide) h⟩

theorem safeGuardUnsupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1479⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_1479_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_1556
    (by simp only [safeRuntime_block_1479_taken_stack]; omega) hr

theorem safeGuardReturnTrue {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1692⟩ :: R)
      (guardDecodedMemory .transaction out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨1484⟩ R
      (guardDecodedMemory .transaction out) aw' out σ k' C' := by
  obtain ⟨aw', k', C', hd⟩ := safeBoolDecoderValid h hov (by omega) (by omega)
    (guardDecodedMemory_word (kind := .transaction) out hl) (.inr hw) (by jump_dest)
  rw [hw] at hd
  have h1651 := safeRuntime_block_1692 (by simp; omega) (by jump_dest) hd
  have h1479 := safeRuntime_block_1651 (by simp; omega) (by jump_dest) h1651
  obtain ⟨k'', C'', he⟩ := safeGuardSupported h1479 (by omega)
  exact ⟨aw', k'', C'', he⟩

theorem safeGuardReturnFalse {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9234⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat (min 32 out.size)) :: ⟨1692⟩ :: R)
      (guardDecodedMemory .transaction out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, hd⟩ := safeBoolDecoderValid h hov (by omega) (by omega)
    (guardDecodedMemory_word (kind := .transaction) out hl) (.inl hw) (by jump_dest)
  rw [hw] at hd
  have h1651 := safeRuntime_block_1692 (by simp; omega) (by jump_dest) hd
  have h1479 := safeRuntime_block_1651 (by simp; omega) (by jump_dest) h1651
  exact safeGuardUnsupported h1479 (by omega)

end Benchmarks.Safe.ViaIR
