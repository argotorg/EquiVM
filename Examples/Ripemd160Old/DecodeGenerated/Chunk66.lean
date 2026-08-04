import Examples.Ripemd160Old.DecodeGenerated.Chunk65

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes66 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨9128⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9129⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9130⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9131⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9132⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH5), some (⟨495790613315⟩, 5))),
  (⟨9138⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.STOP), none)),
  (⟨9139⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADDMOD), none)),
  (⟨9140⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9141⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.STOP), none)),
  (⟨9142⟩, some (Ethereum.Operation.Env (Ethereum.Operation.EOp.CALLER), none))
]

private theorem generatedDecodes66_correct : ∀ i : Fin generatedDecodes66.size,
    decode runtimeBytecode generatedDecodes66[i].1 = generatedDecodes66[i].2 := by
  native_decide

theorem decode_9128 : decode runtimeBytecode ⟨9128⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨0, by decide⟩
theorem decode_9129 : decode runtimeBytecode ⟨9129⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨1, by decide⟩
theorem decode_9130 : decode runtimeBytecode ⟨9130⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨2, by decide⟩
theorem decode_9131 : decode runtimeBytecode ⟨9131⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨3, by decide⟩
theorem decode_9132 : decode runtimeBytecode ⟨9132⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH5), some (⟨495790613315⟩, 5)) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨4, by decide⟩
theorem decode_9138 : decode runtimeBytecode ⟨9138⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.STOP), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨5, by decide⟩
theorem decode_9139 : decode runtimeBytecode ⟨9139⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADDMOD), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨6, by decide⟩
theorem decode_9140 : decode runtimeBytecode ⟨9140⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨7, by decide⟩
theorem decode_9141 : decode runtimeBytecode ⟨9141⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.STOP), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨8, by decide⟩
theorem decode_9142 : decode runtimeBytecode ⟨9142⟩ = some (Ethereum.Operation.Env (Ethereum.Operation.EOp.CALLER), none) := by
  simpa [generatedDecodes66] using generatedDecodes66_correct ⟨9, by decide⟩

end Ripemd160Old
