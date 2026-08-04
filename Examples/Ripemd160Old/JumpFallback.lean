import Examples.Ripemd160Old.DecodeFallback

open Ethereum Ethereum.EVM

namespace Ripemd160Old

private def fallbackJumpTargets : Array UInt256 := #[⟨214⟩, ⟨232⟩, ⟨249⟩, ⟨8306⟩]

private theorem fallbackJumpTargets_valid : ∀ i : Fin fallbackJumpTargets.size,
    (D_J runtimeBytecode 0).contains fallbackJumpTargets[i] = true := by
  rw [runtimeValidJumps]
  native_decide

theorem jump_214 : (D_J runtimeBytecode 0).contains ⟨214⟩ = true := by
  simpa [fallbackJumpTargets] using fallbackJumpTargets_valid ⟨0, by decide⟩

theorem jump_232 : (D_J runtimeBytecode 0).contains ⟨232⟩ = true := by
  simpa [fallbackJumpTargets] using fallbackJumpTargets_valid ⟨1, by decide⟩

theorem jump_249 : (D_J runtimeBytecode 0).contains ⟨249⟩ = true := by
  simpa [fallbackJumpTargets] using fallbackJumpTargets_valid ⟨2, by decide⟩

theorem jump_8306 : (D_J runtimeBytecode 0).contains ⟨8306⟩ = true := by
  simpa [fallbackJumpTargets] using fallbackJumpTargets_valid ⟨3, by decide⟩

end Ripemd160Old
