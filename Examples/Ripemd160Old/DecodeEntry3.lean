import Examples.Ripemd160Old.DecodeEntry2

open Ethereum Ethereum.EVM
set_option maxRecDepth 50000000
set_option maxHeartbeats 0
namespace Ripemd160Old

private def entryDecodes3 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨231⟩, some (.JUMP, none)), (⟨235⟩, some (.JUMPDEST, none)),
  (⟨236⟩, some (.PUSH2, some (⟨254⟩, 2))), (⟨239⟩, some (.PUSH2, some (⟨249⟩, 2))),
  (⟨242⟩, some (.PUSH0, none)), (⟨243⟩, some (.CALLDATASIZE, none)),
  (⟨244⟩, some (.SWAP1, none)), (⟨245⟩, some (.PUSH2, some (⟨221⟩, 2))),
  (⟨248⟩, some (.JUMP, none))
]

private theorem entryDecodes3_correct : ∀ i : Fin entryDecodes3.size,
    decode runtimeBytecode entryDecodes3[i].1 = entryDecodes3[i].2 := by native_decide

@[simp] theorem decode_231 : decode runtimeBytecode ⟨231⟩ = some (.JUMP, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨0, by decide⟩
@[simp] theorem decode_235 : decode runtimeBytecode ⟨235⟩ = some (.JUMPDEST, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨1, by decide⟩
@[simp] theorem decode_236 : decode runtimeBytecode ⟨236⟩ = some (.PUSH2, some (⟨254⟩, 2)) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨2, by decide⟩
@[simp] theorem decode_239 : decode runtimeBytecode ⟨239⟩ = some (.PUSH2, some (⟨249⟩, 2)) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨3, by decide⟩
@[simp] theorem decode_242 : decode runtimeBytecode ⟨242⟩ = some (.PUSH0, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨4, by decide⟩
@[simp] theorem decode_243 : decode runtimeBytecode ⟨243⟩ = some (.CALLDATASIZE, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨5, by decide⟩
@[simp] theorem decode_244 : decode runtimeBytecode ⟨244⟩ = some (.SWAP1, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨6, by decide⟩
@[simp] theorem decode_245 : decode runtimeBytecode ⟨245⟩ = some (.PUSH2, some (⟨221⟩, 2)) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨7, by decide⟩
@[simp] theorem decode_248 : decode runtimeBytecode ⟨248⟩ = some (.JUMP, none) := by simpa [entryDecodes3] using entryDecodes3_correct ⟨8, by decide⟩

end Ripemd160Old
