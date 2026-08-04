import Examples.Ripemd160Old.DecodeGenerated.Chunk53

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes54 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7435⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7436⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7437⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7438⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7439⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7441⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7442⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7445⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7446⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7447⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7448⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7449⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7450⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7452⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7453⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7456⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7457⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7458⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7459⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7460⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7461⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7463⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7464⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7467⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7468⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7469⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7470⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7471⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7472⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7474⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7475⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7478⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7479⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7480⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7481⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7482⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7483⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7485⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7486⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7489⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7490⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7491⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7492⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7493⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7494⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7496⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7497⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7500⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7501⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7502⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7503⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7504⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7505⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7507⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7508⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7511⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7512⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7513⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7514⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨7516⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7517⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨7518⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7519⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7520⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7521⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7810⟩, 2))),
  (⟨7524⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7525⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7526⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7528⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7529⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7799⟩, 2))),
  (⟨7532⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7533⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7534⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7536⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7537⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7788⟩, 2))),
  (⟨7540⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7541⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7542⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7544⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7545⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7777⟩, 2))),
  (⟨7548⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7549⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7550⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7552⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7553⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7767⟩, 2))),
  (⟨7556⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7557⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7558⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7560⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7561⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7756⟩, 2))),
  (⟨7564⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7565⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7566⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7568⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7569⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7745⟩, 2))),
  (⟨7572⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7573⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7574⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7576⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7577⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7735⟩, 2)))
]

private theorem generatedDecodes54_correct : ∀ i : Fin generatedDecodes54.size,
    decode runtimeBytecode generatedDecodes54[i].1 = generatedDecodes54[i].2 := by
  native_decide

theorem decode_7435 : decode runtimeBytecode ⟨7435⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨0, by decide⟩
theorem decode_7436 : decode runtimeBytecode ⟨7436⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨1, by decide⟩
theorem decode_7437 : decode runtimeBytecode ⟨7437⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨2, by decide⟩
theorem decode_7438 : decode runtimeBytecode ⟨7438⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨3, by decide⟩
theorem decode_7439 : decode runtimeBytecode ⟨7439⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨4, by decide⟩
theorem decode_7441 : decode runtimeBytecode ⟨7441⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨5, by decide⟩
theorem decode_7442 : decode runtimeBytecode ⟨7442⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨6, by decide⟩
theorem decode_7445 : decode runtimeBytecode ⟨7445⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨7, by decide⟩
theorem decode_7446 : decode runtimeBytecode ⟨7446⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨8, by decide⟩
theorem decode_7447 : decode runtimeBytecode ⟨7447⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨9, by decide⟩
theorem decode_7448 : decode runtimeBytecode ⟨7448⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨10, by decide⟩
theorem decode_7449 : decode runtimeBytecode ⟨7449⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨11, by decide⟩
theorem decode_7450 : decode runtimeBytecode ⟨7450⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨12, by decide⟩
theorem decode_7452 : decode runtimeBytecode ⟨7452⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨13, by decide⟩
theorem decode_7453 : decode runtimeBytecode ⟨7453⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨14, by decide⟩
theorem decode_7456 : decode runtimeBytecode ⟨7456⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨15, by decide⟩
theorem decode_7457 : decode runtimeBytecode ⟨7457⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨16, by decide⟩
theorem decode_7458 : decode runtimeBytecode ⟨7458⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨17, by decide⟩
theorem decode_7459 : decode runtimeBytecode ⟨7459⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨18, by decide⟩
theorem decode_7460 : decode runtimeBytecode ⟨7460⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨19, by decide⟩
theorem decode_7461 : decode runtimeBytecode ⟨7461⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨20, by decide⟩
theorem decode_7463 : decode runtimeBytecode ⟨7463⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨21, by decide⟩
theorem decode_7464 : decode runtimeBytecode ⟨7464⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨22, by decide⟩
theorem decode_7467 : decode runtimeBytecode ⟨7467⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨23, by decide⟩
theorem decode_7468 : decode runtimeBytecode ⟨7468⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨24, by decide⟩
theorem decode_7469 : decode runtimeBytecode ⟨7469⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨25, by decide⟩
theorem decode_7470 : decode runtimeBytecode ⟨7470⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨26, by decide⟩
theorem decode_7471 : decode runtimeBytecode ⟨7471⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨27, by decide⟩
theorem decode_7472 : decode runtimeBytecode ⟨7472⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨28, by decide⟩
theorem decode_7474 : decode runtimeBytecode ⟨7474⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨29, by decide⟩
theorem decode_7475 : decode runtimeBytecode ⟨7475⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨30, by decide⟩
theorem decode_7478 : decode runtimeBytecode ⟨7478⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨31, by decide⟩
theorem decode_7479 : decode runtimeBytecode ⟨7479⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨32, by decide⟩
theorem decode_7480 : decode runtimeBytecode ⟨7480⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨33, by decide⟩
theorem decode_7481 : decode runtimeBytecode ⟨7481⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨34, by decide⟩
theorem decode_7482 : decode runtimeBytecode ⟨7482⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨35, by decide⟩
theorem decode_7483 : decode runtimeBytecode ⟨7483⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨36, by decide⟩
theorem decode_7485 : decode runtimeBytecode ⟨7485⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨37, by decide⟩
theorem decode_7486 : decode runtimeBytecode ⟨7486⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨38, by decide⟩
theorem decode_7489 : decode runtimeBytecode ⟨7489⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨39, by decide⟩
theorem decode_7490 : decode runtimeBytecode ⟨7490⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨40, by decide⟩
theorem decode_7491 : decode runtimeBytecode ⟨7491⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨41, by decide⟩
theorem decode_7492 : decode runtimeBytecode ⟨7492⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨42, by decide⟩
theorem decode_7493 : decode runtimeBytecode ⟨7493⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨43, by decide⟩
theorem decode_7494 : decode runtimeBytecode ⟨7494⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨44, by decide⟩
theorem decode_7496 : decode runtimeBytecode ⟨7496⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨45, by decide⟩
theorem decode_7497 : decode runtimeBytecode ⟨7497⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨46, by decide⟩
theorem decode_7500 : decode runtimeBytecode ⟨7500⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨47, by decide⟩
theorem decode_7501 : decode runtimeBytecode ⟨7501⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨48, by decide⟩
theorem decode_7502 : decode runtimeBytecode ⟨7502⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨49, by decide⟩
theorem decode_7503 : decode runtimeBytecode ⟨7503⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨50, by decide⟩
theorem decode_7504 : decode runtimeBytecode ⟨7504⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨51, by decide⟩
theorem decode_7505 : decode runtimeBytecode ⟨7505⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨52, by decide⟩
theorem decode_7507 : decode runtimeBytecode ⟨7507⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨53, by decide⟩
theorem decode_7508 : decode runtimeBytecode ⟨7508⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨54, by decide⟩
theorem decode_7511 : decode runtimeBytecode ⟨7511⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨55, by decide⟩
theorem decode_7512 : decode runtimeBytecode ⟨7512⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨56, by decide⟩
theorem decode_7513 : decode runtimeBytecode ⟨7513⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨57, by decide⟩
theorem decode_7514 : decode runtimeBytecode ⟨7514⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨58, by decide⟩
theorem decode_7516 : decode runtimeBytecode ⟨7516⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨59, by decide⟩
theorem decode_7517 : decode runtimeBytecode ⟨7517⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨60, by decide⟩
theorem decode_7518 : decode runtimeBytecode ⟨7518⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨61, by decide⟩
theorem decode_7519 : decode runtimeBytecode ⟨7519⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨62, by decide⟩
theorem decode_7520 : decode runtimeBytecode ⟨7520⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨63, by decide⟩
theorem decode_7521 : decode runtimeBytecode ⟨7521⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7810⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨64, by decide⟩
theorem decode_7524 : decode runtimeBytecode ⟨7524⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨65, by decide⟩
theorem decode_7525 : decode runtimeBytecode ⟨7525⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨66, by decide⟩
theorem decode_7526 : decode runtimeBytecode ⟨7526⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨67, by decide⟩
theorem decode_7528 : decode runtimeBytecode ⟨7528⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨68, by decide⟩
theorem decode_7529 : decode runtimeBytecode ⟨7529⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7799⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨69, by decide⟩
theorem decode_7532 : decode runtimeBytecode ⟨7532⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨70, by decide⟩
theorem decode_7533 : decode runtimeBytecode ⟨7533⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨71, by decide⟩
theorem decode_7534 : decode runtimeBytecode ⟨7534⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨72, by decide⟩
theorem decode_7536 : decode runtimeBytecode ⟨7536⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨73, by decide⟩
theorem decode_7537 : decode runtimeBytecode ⟨7537⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7788⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨74, by decide⟩
theorem decode_7540 : decode runtimeBytecode ⟨7540⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨75, by decide⟩
theorem decode_7541 : decode runtimeBytecode ⟨7541⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨76, by decide⟩
theorem decode_7542 : decode runtimeBytecode ⟨7542⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨77, by decide⟩
theorem decode_7544 : decode runtimeBytecode ⟨7544⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨78, by decide⟩
theorem decode_7545 : decode runtimeBytecode ⟨7545⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7777⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨79, by decide⟩
theorem decode_7548 : decode runtimeBytecode ⟨7548⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨80, by decide⟩
theorem decode_7549 : decode runtimeBytecode ⟨7549⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨81, by decide⟩
theorem decode_7550 : decode runtimeBytecode ⟨7550⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨82, by decide⟩
theorem decode_7552 : decode runtimeBytecode ⟨7552⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨83, by decide⟩
theorem decode_7553 : decode runtimeBytecode ⟨7553⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7767⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨84, by decide⟩
theorem decode_7556 : decode runtimeBytecode ⟨7556⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨85, by decide⟩
theorem decode_7557 : decode runtimeBytecode ⟨7557⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨86, by decide⟩
theorem decode_7558 : decode runtimeBytecode ⟨7558⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨87, by decide⟩
theorem decode_7560 : decode runtimeBytecode ⟨7560⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨88, by decide⟩
theorem decode_7561 : decode runtimeBytecode ⟨7561⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7756⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨89, by decide⟩
theorem decode_7564 : decode runtimeBytecode ⟨7564⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨90, by decide⟩
theorem decode_7565 : decode runtimeBytecode ⟨7565⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨91, by decide⟩
theorem decode_7566 : decode runtimeBytecode ⟨7566⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨92, by decide⟩
theorem decode_7568 : decode runtimeBytecode ⟨7568⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨93, by decide⟩
theorem decode_7569 : decode runtimeBytecode ⟨7569⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7745⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨94, by decide⟩
theorem decode_7572 : decode runtimeBytecode ⟨7572⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨95, by decide⟩
theorem decode_7573 : decode runtimeBytecode ⟨7573⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨96, by decide⟩
theorem decode_7574 : decode runtimeBytecode ⟨7574⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨97, by decide⟩
theorem decode_7576 : decode runtimeBytecode ⟨7576⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨98, by decide⟩
theorem decode_7577 : decode runtimeBytecode ⟨7577⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7735⟩, 2)) := by
  simpa [generatedDecodes54] using generatedDecodes54_correct ⟨99, by decide⟩

end Ripemd160Old
