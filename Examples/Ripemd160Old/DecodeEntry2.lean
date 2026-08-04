import Examples.Ripemd160Old.DecodeEntry1

open Ethereum Ethereum.EVM
set_option maxRecDepth 50000000
set_option maxHeartbeats 0
namespace Ripemd160Old

private def entryDecodes2 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨175⟩, some (.PUSH2, some (⟨183⟩, 2))), (⟨178⟩, some (.DUP3, none)),
  (⟨179⟩, some (.PUSH2, some (⟨121⟩, 2))), (⟨182⟩, some (.JUMP, none)),
  (⟨221⟩, some (.JUMPDEST, none)), (⟨222⟩, some (.PUSH2, some (⟨232⟩, 2))),
  (⟨225⟩, some (.SWAP2, none)), (⟨226⟩, some (.CALLDATASIZE, none)),
  (⟨227⟩, some (.SWAP2, none)), (⟨228⟩, some (.PUSH2, some (⟨167⟩, 2)))
]

private theorem entryDecodes2_correct : ∀ i : Fin entryDecodes2.size,
    decode runtimeBytecode entryDecodes2[i].1 = entryDecodes2[i].2 := by native_decide

@[simp] theorem decode_175 : decode runtimeBytecode ⟨175⟩ = some (.PUSH2, some (⟨183⟩, 2)) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨0, by decide⟩
@[simp] theorem decode_178 : decode runtimeBytecode ⟨178⟩ = some (.DUP3, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨1, by decide⟩
@[simp] theorem decode_179 : decode runtimeBytecode ⟨179⟩ = some (.PUSH2, some (⟨121⟩, 2)) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨2, by decide⟩
@[simp] theorem decode_182 : decode runtimeBytecode ⟨182⟩ = some (.JUMP, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨3, by decide⟩
@[simp] theorem decode_221 : decode runtimeBytecode ⟨221⟩ = some (.JUMPDEST, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨4, by decide⟩
@[simp] theorem decode_222 : decode runtimeBytecode ⟨222⟩ = some (.PUSH2, some (⟨232⟩, 2)) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨5, by decide⟩
@[simp] theorem decode_225 : decode runtimeBytecode ⟨225⟩ = some (.SWAP2, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨6, by decide⟩
@[simp] theorem decode_226 : decode runtimeBytecode ⟨226⟩ = some (.CALLDATASIZE, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨7, by decide⟩
@[simp] theorem decode_227 : decode runtimeBytecode ⟨227⟩ = some (.SWAP2, none) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨8, by decide⟩
@[simp] theorem decode_228 : decode runtimeBytecode ⟨228⟩ = some (.PUSH2, some (⟨167⟩, 2)) := by simpa [entryDecodes2] using entryDecodes2_correct ⟨9, by decide⟩

end Ripemd160Old
