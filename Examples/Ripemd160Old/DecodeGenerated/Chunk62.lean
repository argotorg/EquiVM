import Examples.Ripemd160Old.DecodeGenerated.Chunk61

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes62 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8546⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8547⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8548⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8586⟩, 2))),
  (⟨8551⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8580⟩, 2))),
  (⟨8554⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8574⟩, 2))),
  (⟨8557⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8568⟩, 2))),
  (⟨8560⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8592⟩, 2))),
  (⟨8563⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨8564⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2))),
  (⟨8567⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8568⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8569⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨8570⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2))),
  (⟨8573⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8575⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨8576⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2))),
  (⟨8579⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8580⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8581⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8582⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2))),
  (⟨8585⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8586⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8587⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8588⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2))),
  (⟨8591⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8592⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8593⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8594⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8596⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8597⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8598⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8599⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8601⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8602⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8603⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8604⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8606⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8607⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8608⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8609⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8611⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8612⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨8613⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8615⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨8616⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8617⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8618⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8619⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8620⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8621⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8622⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8623⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨8624⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨8625⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8627⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8628⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none)),
  (⟨8629⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨8630⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none)),
  (⟨8631⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨8632⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8633⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8634⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8635⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8636⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨8638⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8639⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8640⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8997⟩, 2))),
  (⟨8643⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8644⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8645⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8646⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8647⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8650⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8651⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8652⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8653⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8654⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8656⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8659⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8660⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8661⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8662⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8663⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8664⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8666⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8669⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8670⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8671⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8672⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8673⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none)),
  (⟨8674⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8676⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8679⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8680⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8681⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8682⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8683⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8684⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8686⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)))
]

private theorem generatedDecodes62_correct : ∀ i : Fin generatedDecodes62.size,
    decode runtimeBytecode generatedDecodes62[i].1 = generatedDecodes62[i].2 := by
  native_decide

theorem decode_8546 : decode runtimeBytecode ⟨8546⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨0, by decide⟩
theorem decode_8547 : decode runtimeBytecode ⟨8547⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨1, by decide⟩
theorem decode_8548 : decode runtimeBytecode ⟨8548⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8586⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨2, by decide⟩
theorem decode_8551 : decode runtimeBytecode ⟨8551⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8580⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨3, by decide⟩
theorem decode_8554 : decode runtimeBytecode ⟨8554⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8574⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨4, by decide⟩
theorem decode_8557 : decode runtimeBytecode ⟨8557⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8568⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨5, by decide⟩
theorem decode_8560 : decode runtimeBytecode ⟨8560⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8592⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨6, by decide⟩
theorem decode_8563 : decode runtimeBytecode ⟨8563⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨7, by decide⟩
theorem decode_8564 : decode runtimeBytecode ⟨8564⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨8, by decide⟩
theorem decode_8567 : decode runtimeBytecode ⟨8567⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨9, by decide⟩
theorem decode_8568 : decode runtimeBytecode ⟨8568⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨10, by decide⟩
theorem decode_8569 : decode runtimeBytecode ⟨8569⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨11, by decide⟩
theorem decode_8570 : decode runtimeBytecode ⟨8570⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨12, by decide⟩
theorem decode_8573 : decode runtimeBytecode ⟨8573⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨13, by decide⟩
theorem decode_8574 : decode runtimeBytecode ⟨8574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨14, by decide⟩
theorem decode_8575 : decode runtimeBytecode ⟨8575⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨15, by decide⟩
theorem decode_8576 : decode runtimeBytecode ⟨8576⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨16, by decide⟩
theorem decode_8579 : decode runtimeBytecode ⟨8579⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨17, by decide⟩
theorem decode_8580 : decode runtimeBytecode ⟨8580⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨18, by decide⟩
theorem decode_8581 : decode runtimeBytecode ⟨8581⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨19, by decide⟩
theorem decode_8582 : decode runtimeBytecode ⟨8582⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨20, by decide⟩
theorem decode_8585 : decode runtimeBytecode ⟨8585⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨21, by decide⟩
theorem decode_8586 : decode runtimeBytecode ⟨8586⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨22, by decide⟩
theorem decode_8587 : decode runtimeBytecode ⟨8587⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨23, by decide⟩
theorem decode_8588 : decode runtimeBytecode ⟨8588⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8266⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨24, by decide⟩
theorem decode_8591 : decode runtimeBytecode ⟨8591⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨25, by decide⟩
theorem decode_8592 : decode runtimeBytecode ⟨8592⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨26, by decide⟩
theorem decode_8593 : decode runtimeBytecode ⟨8593⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨27, by decide⟩
theorem decode_8594 : decode runtimeBytecode ⟨8594⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨28, by decide⟩
theorem decode_8596 : decode runtimeBytecode ⟨8596⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨29, by decide⟩
theorem decode_8597 : decode runtimeBytecode ⟨8597⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨30, by decide⟩
theorem decode_8598 : decode runtimeBytecode ⟨8598⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨31, by decide⟩
theorem decode_8599 : decode runtimeBytecode ⟨8599⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨32, by decide⟩
theorem decode_8601 : decode runtimeBytecode ⟨8601⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨33, by decide⟩
theorem decode_8602 : decode runtimeBytecode ⟨8602⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨34, by decide⟩
theorem decode_8603 : decode runtimeBytecode ⟨8603⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨35, by decide⟩
theorem decode_8604 : decode runtimeBytecode ⟨8604⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨36, by decide⟩
theorem decode_8606 : decode runtimeBytecode ⟨8606⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨37, by decide⟩
theorem decode_8607 : decode runtimeBytecode ⟨8607⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨38, by decide⟩
theorem decode_8608 : decode runtimeBytecode ⟨8608⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨39, by decide⟩
theorem decode_8609 : decode runtimeBytecode ⟨8609⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨40, by decide⟩
theorem decode_8611 : decode runtimeBytecode ⟨8611⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨41, by decide⟩
theorem decode_8612 : decode runtimeBytecode ⟨8612⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨42, by decide⟩
theorem decode_8613 : decode runtimeBytecode ⟨8613⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨43, by decide⟩
theorem decode_8615 : decode runtimeBytecode ⟨8615⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨44, by decide⟩
theorem decode_8616 : decode runtimeBytecode ⟨8616⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨45, by decide⟩
theorem decode_8617 : decode runtimeBytecode ⟨8617⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨46, by decide⟩
theorem decode_8618 : decode runtimeBytecode ⟨8618⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨47, by decide⟩
theorem decode_8619 : decode runtimeBytecode ⟨8619⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨48, by decide⟩
theorem decode_8620 : decode runtimeBytecode ⟨8620⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨49, by decide⟩
theorem decode_8621 : decode runtimeBytecode ⟨8621⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨50, by decide⟩
theorem decode_8622 : decode runtimeBytecode ⟨8622⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨51, by decide⟩
theorem decode_8623 : decode runtimeBytecode ⟨8623⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨52, by decide⟩
theorem decode_8624 : decode runtimeBytecode ⟨8624⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨53, by decide⟩
theorem decode_8625 : decode runtimeBytecode ⟨8625⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨54, by decide⟩
theorem decode_8627 : decode runtimeBytecode ⟨8627⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨55, by decide⟩
theorem decode_8628 : decode runtimeBytecode ⟨8628⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨56, by decide⟩
theorem decode_8629 : decode runtimeBytecode ⟨8629⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨57, by decide⟩
theorem decode_8630 : decode runtimeBytecode ⟨8630⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨58, by decide⟩
theorem decode_8631 : decode runtimeBytecode ⟨8631⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨59, by decide⟩
theorem decode_8632 : decode runtimeBytecode ⟨8632⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨60, by decide⟩
theorem decode_8633 : decode runtimeBytecode ⟨8633⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨61, by decide⟩
theorem decode_8634 : decode runtimeBytecode ⟨8634⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨62, by decide⟩
theorem decode_8635 : decode runtimeBytecode ⟨8635⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨63, by decide⟩
theorem decode_8636 : decode runtimeBytecode ⟨8636⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨64, by decide⟩
theorem decode_8638 : decode runtimeBytecode ⟨8638⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨65, by decide⟩
theorem decode_8639 : decode runtimeBytecode ⟨8639⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨66, by decide⟩
theorem decode_8640 : decode runtimeBytecode ⟨8640⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8997⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨67, by decide⟩
theorem decode_8643 : decode runtimeBytecode ⟨8643⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨68, by decide⟩
theorem decode_8644 : decode runtimeBytecode ⟨8644⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨69, by decide⟩
theorem decode_8645 : decode runtimeBytecode ⟨8645⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨70, by decide⟩
theorem decode_8646 : decode runtimeBytecode ⟨8646⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨71, by decide⟩
theorem decode_8647 : decode runtimeBytecode ⟨8647⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨72, by decide⟩
theorem decode_8650 : decode runtimeBytecode ⟨8650⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨73, by decide⟩
theorem decode_8651 : decode runtimeBytecode ⟨8651⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨74, by decide⟩
theorem decode_8652 : decode runtimeBytecode ⟨8652⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨75, by decide⟩
theorem decode_8653 : decode runtimeBytecode ⟨8653⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨76, by decide⟩
theorem decode_8654 : decode runtimeBytecode ⟨8654⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨77, by decide⟩
theorem decode_8656 : decode runtimeBytecode ⟨8656⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨78, by decide⟩
theorem decode_8659 : decode runtimeBytecode ⟨8659⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨79, by decide⟩
theorem decode_8660 : decode runtimeBytecode ⟨8660⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨80, by decide⟩
theorem decode_8661 : decode runtimeBytecode ⟨8661⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨81, by decide⟩
theorem decode_8662 : decode runtimeBytecode ⟨8662⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨82, by decide⟩
theorem decode_8663 : decode runtimeBytecode ⟨8663⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨83, by decide⟩
theorem decode_8664 : decode runtimeBytecode ⟨8664⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨84, by decide⟩
theorem decode_8666 : decode runtimeBytecode ⟨8666⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨85, by decide⟩
theorem decode_8669 : decode runtimeBytecode ⟨8669⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨86, by decide⟩
theorem decode_8670 : decode runtimeBytecode ⟨8670⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨87, by decide⟩
theorem decode_8671 : decode runtimeBytecode ⟨8671⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨88, by decide⟩
theorem decode_8672 : decode runtimeBytecode ⟨8672⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨89, by decide⟩
theorem decode_8673 : decode runtimeBytecode ⟨8673⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨90, by decide⟩
theorem decode_8674 : decode runtimeBytecode ⟨8674⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨91, by decide⟩
theorem decode_8676 : decode runtimeBytecode ⟨8676⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨92, by decide⟩
theorem decode_8679 : decode runtimeBytecode ⟨8679⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨93, by decide⟩
theorem decode_8680 : decode runtimeBytecode ⟨8680⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨94, by decide⟩
theorem decode_8681 : decode runtimeBytecode ⟨8681⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨95, by decide⟩
theorem decode_8682 : decode runtimeBytecode ⟨8682⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨96, by decide⟩
theorem decode_8683 : decode runtimeBytecode ⟨8683⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨97, by decide⟩
theorem decode_8684 : decode runtimeBytecode ⟨8684⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨98, by decide⟩
theorem decode_8686 : decode runtimeBytecode ⟨8686⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes62] using generatedDecodes62_correct ⟨99, by decide⟩

end Ripemd160Old
