import Examples.Ripemd160Old.DecodeEntry

open Ethereum Ethereum.EVM

namespace Ripemd160Old

private def entryJumpTargets : Array UInt256 :=
  #[⟨21⟩, ⟨121⟩, ⟨167⟩, ⟨221⟩, ⟨235⟩]

private theorem entryJumpTargets_valid : ∀ i : Fin entryJumpTargets.size,
    (D_J runtimeBytecode 0).contains entryJumpTargets[i] = true := by
  rw [runtimeValidJumps]
  native_decide

@[simp] theorem jump_21 : (D_J runtimeBytecode 0).contains ⟨21⟩ = true := by
  simpa [entryJumpTargets] using entryJumpTargets_valid ⟨0, by decide⟩

@[simp] theorem jump_121 : (D_J runtimeBytecode 0).contains ⟨121⟩ = true := by
  simpa [entryJumpTargets] using entryJumpTargets_valid ⟨1, by decide⟩

@[simp] theorem jump_167 : (D_J runtimeBytecode 0).contains ⟨167⟩ = true := by
  simpa [entryJumpTargets] using entryJumpTargets_valid ⟨2, by decide⟩

@[simp] theorem jump_221 : (D_J runtimeBytecode 0).contains ⟨221⟩ = true := by
  simpa [entryJumpTargets] using entryJumpTargets_valid ⟨3, by decide⟩

@[simp] theorem jump_235 : (D_J runtimeBytecode 0).contains ⟨235⟩ = true := by
  simpa [entryJumpTargets] using entryJumpTargets_valid ⟨4, by decide⟩

theorem jumpMem_21 : ⟨21⟩ ∈ D_J runtimeBytecode 0 := by
  simpa [Array.contains_iff_mem] using jump_21

theorem jumpMem_121 : ⟨121⟩ ∈ D_J runtimeBytecode 0 := by
  simpa [Array.contains_iff_mem] using jump_121

theorem jumpMem_167 : ⟨167⟩ ∈ D_J runtimeBytecode 0 := by
  simpa [Array.contains_iff_mem] using jump_167

theorem jumpMem_221 : ⟨221⟩ ∈ D_J runtimeBytecode 0 := by
  simpa [Array.contains_iff_mem] using jump_221

theorem jumpMem_235 : ⟨235⟩ ∈ D_J runtimeBytecode 0 := by
  simpa [Array.contains_iff_mem] using jump_235

end Ripemd160Old
