import Benchmarks.Safe.Runs1e6.GuardCallMemory
import Benchmarks.Safe.Runs1e6.BoolReturnDecoder
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_027
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_028
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

theorem safeGuardCallFailureTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7361⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_7361_fallthrough (by omega) (by decide) h
  exact safeRuntime_block_7368 (by simp [safeRuntime_block_7361_fallthrough_stack]; omega) hr

theorem safeGuardReturnStart {I g s0 σ k C aw out} {x0 x1 x2 : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7361⟩ (⟨1⟩ :: x0 :: x1 :: x2 :: R)
      ((guardOutputMemory .transaction) out) aw out σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨14540⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨7411⟩ :: R)
      ((guardDecodedMemory .transaction) out) aw' out σ k' C' := by
  have hr := safeRuntime_block_7361_taken (by simp; omega) (by decide) (by jump_dest) h
  obtain ⟨aw', k', C', hd⟩ := safeRuntime_block_7375_packed (by omega) (by jump_dest) hr
  have hf : memLoad (UInt256.ofNat 64) ((guardOutputMemory .transaction) out) = ⟨128⟩ :=
    guardOutputMemory_freePtr (kind := .transaction) out
  exact ⟨aw', k', C', by simpa only [safeRuntime_block_7375_stack,
    safeRuntime_block_7375_memory, hf, guardDecodedMemory, Reasoning.Theory.writeWord] using hd⟩

theorem safeGuardSupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7413⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7459⟩ R mem aw rdata σ k' C' :=
  ⟨_, _, safeRuntime_block_7413_taken hov (by decide) (by jump_dest) h⟩

theorem safeGuardUnsupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7413⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hf := safeRuntime_block_7413_fallthrough (by omega) (by decide) h
  have hr := safeRuntime_block_7419
    (by simpa only [safeRuntime_block_7413_fallthrough_stack] using
      (show R.length + 3 ≤ 1024 by omega))
    (by jump_dest) hf
  exact safeRuntime_block_8421
    (by simp [safeRuntime_block_7419_stack, safeRuntime_block_7413_fallthrough_stack]; omega) hr

theorem safeGuardReturnTrue {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨14540⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨7411⟩ :: R)
      ((guardDecodedMemory .transaction) out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7459⟩ R
      ((guardDecodedMemory .transaction) out) aw' out σ k' C' := by
  obtain ⟨aw', k', C', hd⟩ := safeBoolDecoderValid h hov hl hb
    (guardDecodedMemory_word (kind := .transaction) out hl) (.inr hw) (by jump_dest)
  rw [hw] at hd
  have hr := safeRuntime_block_7411 (by omega) hd
  obtain ⟨k'', C'', he⟩ := safeGuardSupported hr (by omega)
  exact ⟨aw', k'', C'', he⟩

theorem safeGuardReturnFalse {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨14540⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨7411⟩ :: R)
      ((guardDecodedMemory .transaction) out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, hd⟩ := safeBoolDecoderValid h hov hl hb
    (guardDecodedMemory_word (kind := .transaction) out hl) (.inl hw) (by jump_dest)
  rw [hw] at hd
  exact safeGuardUnsupported (safeRuntime_block_7411 (by omega) hd) (by omega)

end Benchmarks.Safe.Runs1e6
