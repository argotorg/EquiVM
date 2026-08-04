import Examples.Ripemd160Old.DecodeEntry0

open Ethereum Ethereum.EVM
set_option maxRecDepth 50000000
set_option maxHeartbeats 0
namespace Ripemd160Old

private def entryDecodes1 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨22⟩, some (.PUSH0, none)), (⟨23⟩, some (.DUP1, none)),
  (⟨24⟩, some (.REVERT, none)), (⟨121⟩, some (.JUMPDEST, none)),
  (⟨167⟩, some (.JUMPDEST, none)), (⟨168⟩, some (.SWAP1, none)),
  (⟨169⟩, some (.SWAP3, none)), (⟨170⟩, some (.SWAP2, none)),
  (⟨171⟩, some (.SWAP3, none)), (⟨172⟩, some (.PUSH2, some (⟨188⟩, 2)))
]

private theorem entryDecodes1_correct : ∀ i : Fin entryDecodes1.size,
    decode runtimeBytecode entryDecodes1[i].1 = entryDecodes1[i].2 := by native_decide

@[simp] theorem decode_22 : decode runtimeBytecode ⟨22⟩ = some (.PUSH0, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨0, by decide⟩
@[simp] theorem decode_23 : decode runtimeBytecode ⟨23⟩ = some (.DUP1, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨1, by decide⟩
@[simp] theorem decode_24 : decode runtimeBytecode ⟨24⟩ = some (.REVERT, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨2, by decide⟩
@[simp] theorem decode_121 : decode runtimeBytecode ⟨121⟩ = some (.JUMPDEST, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨3, by decide⟩
@[simp] theorem decode_167 : decode runtimeBytecode ⟨167⟩ = some (.JUMPDEST, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨4, by decide⟩
@[simp] theorem decode_168 : decode runtimeBytecode ⟨168⟩ = some (.SWAP1, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨5, by decide⟩
@[simp] theorem decode_169 : decode runtimeBytecode ⟨169⟩ = some (.SWAP3, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨6, by decide⟩
@[simp] theorem decode_170 : decode runtimeBytecode ⟨170⟩ = some (.SWAP2, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨7, by decide⟩
@[simp] theorem decode_171 : decode runtimeBytecode ⟨171⟩ = some (.SWAP3, none) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨8, by decide⟩
@[simp] theorem decode_172 : decode runtimeBytecode ⟨172⟩ = some (.PUSH2, some (⟨188⟩, 2)) := by simpa [entryDecodes1] using entryDecodes1_correct ⟨9, by decide⟩

end Ripemd160Old
