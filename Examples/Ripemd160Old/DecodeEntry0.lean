import Examples.Ripemd160Old.Bytecode

open Ethereum Ethereum.EVM
set_option maxRecDepth 50000000
set_option maxHeartbeats 0



namespace Ripemd160Old

private def entryDecodes0 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨0⟩, some (.PUSH1, some (⟨128⟩, 1))),
  (⟨2⟩, some (.PUSH1, some (⟨64⟩, 1))),
  (⟨4⟩, some (.MSTORE, none)),
  (⟨5⟩, some (.CALLVALUE, none)),
  (⟨6⟩, some (.ISZERO, none)),
  (⟨7⟩, some (.PUSH2, some (⟨235⟩, 2))),
  (⟨10⟩, some (.JUMPI, none)),
  (⟨11⟩, some (.PUSH2, some (⟨21⟩, 2))),
  (⟨14⟩, some (.JUMP, none)),
  (⟨21⟩, some (.JUMPDEST, none))
]

private theorem entryDecodes0_correct : ∀ i : Fin entryDecodes0.size,
    decode runtimeBytecode entryDecodes0[i].1 = entryDecodes0[i].2 := by
  native_decide

@[simp] theorem decode_0 : decode runtimeBytecode ⟨0⟩ = some (.PUSH1, some (⟨128⟩, 1)) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨0, by decide⟩
@[simp] theorem decode_2 : decode runtimeBytecode ⟨2⟩ = some (.PUSH1, some (⟨64⟩, 1)) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨1, by decide⟩
@[simp] theorem decode_4 : decode runtimeBytecode ⟨4⟩ = some (.MSTORE, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨2, by decide⟩
@[simp] theorem decode_5 : decode runtimeBytecode ⟨5⟩ = some (.CALLVALUE, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨3, by decide⟩
@[simp] theorem decode_6 : decode runtimeBytecode ⟨6⟩ = some (.ISZERO, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨4, by decide⟩
@[simp] theorem decode_7 : decode runtimeBytecode ⟨7⟩ = some (.PUSH2, some (⟨235⟩, 2)) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨5, by decide⟩
@[simp] theorem decode_10 : decode runtimeBytecode ⟨10⟩ = some (.JUMPI, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨6, by decide⟩
@[simp] theorem decode_11 : decode runtimeBytecode ⟨11⟩ = some (.PUSH2, some (⟨21⟩, 2)) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨7, by decide⟩
@[simp] theorem decode_14 : decode runtimeBytecode ⟨14⟩ = some (.JUMP, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨8, by decide⟩
@[simp] theorem decode_21 : decode runtimeBytecode ⟨21⟩ = some (.JUMPDEST, none) := by
  simpa [entryDecodes0] using entryDecodes0_correct ⟨9, by decide⟩

end Ripemd160Old
