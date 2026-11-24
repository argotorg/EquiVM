import Benchmarks.Safe.V1_0227664.GuardCallMemory
import Benchmarks.Safe.V1_0227664.BoolReturnDecoder
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_026
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_029

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 100000

theorem safeModuleGuardCallFailureTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5648⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hr := safeRuntime_block_5648_fallthrough (by omega) (by decide) h
  exact safeRuntime_block_5655 (by simp [safeRuntime_block_5648_fallthrough_stack]; omega) hr

theorem safeModuleGuardReturnStart {I g s0 σ k C aw out} {x0 x1 x2 : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5648⟩ (⟨1⟩ :: x0 :: x1 :: x2 :: R)
      ((guardOutputMemory .moduleGuard) out) aw out σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨11245⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨5698⟩ :: R)
      ((guardDecodedMemory .moduleGuard) out) aw' out σ k' C' := by
  have hr := safeRuntime_block_5648_taken (by simp; omega) (by decide) (by jump_dest) h
  obtain ⟨aw', k', C', hd⟩ := safeRuntime_block_5662_packed (by omega) (by jump_dest) hr
  have hf : memLoad (UInt256.ofNat 64) ((guardOutputMemory .moduleGuard) out) = ⟨128⟩ :=
    guardOutputMemory_freePtr (kind := .moduleGuard) out
  exact ⟨aw', k', C', by simpa only [safeRuntime_block_5662_stack,
    safeRuntime_block_5662_memory, hf, guardDecodedMemory, Reasoning.Theory.writeWord] using hd⟩

theorem safeModuleGuardSupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5700⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5722⟩ R mem aw rdata σ k' C' :=
  ⟨_, _, safeRuntime_block_5700_taken hov (by decide) (by jump_dest) h⟩

theorem safeModuleGuardUnsupported {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5700⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hf := safeRuntime_block_5700_fallthrough (by omega) (by decide) h
  have hr := safeRuntime_block_5706
    (by simpa only [safeRuntime_block_5700_fallthrough_stack] using
      (show R.length + 3 ≤ 1024 by omega))
    (by jump_dest) hf
  exact safeRuntime_block_6712
    (by simp [safeRuntime_block_5706_stack, safeRuntime_block_5700_fallthrough_stack]; omega) hr

theorem safeModuleGuardReturnTrue {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11245⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨5698⟩ :: R)
      ((guardDecodedMemory .moduleGuard) out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨5722⟩ R
      ((guardDecodedMemory .moduleGuard) out) aw' out σ k' C' := by
  obtain ⟨aw', k', C', hd⟩ := safeBoolDecoderValid h hov hl hb
    (guardDecodedMemory_word (kind := .moduleGuard) out hl) (.inr hw) (by jump_dest)
  rw [hw] at hd
  have hr := safeRuntime_block_5698 (by omega) hd
  obtain ⟨k'', C'', he⟩ := safeModuleGuardSupported hr (by omega)
  exact ⟨aw', k'', C'', he⟩

theorem safeModuleGuardReturnFalse {I g s0 σ k C aw out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11245⟩
      (⟨128⟩ :: (⟨128⟩ + UInt256.ofNat out.size) :: ⟨5698⟩ :: R)
      ((guardDecodedMemory .moduleGuard) out) aw out σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255)
    (hw : calldataWord out 0 = ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, _, hd⟩ := safeBoolDecoderValid h hov hl hb
    (guardDecodedMemory_word (kind := .moduleGuard) out hl) (.inl hw) (by jump_dest)
  rw [hw] at hd
  exact safeModuleGuardUnsupported (safeRuntime_block_5698 (by omega) hd) (by omega)

end Benchmarks.Safe.V1_0227664
