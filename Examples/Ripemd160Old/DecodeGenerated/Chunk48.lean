import Examples.Ripemd160Old.DecodeGenerated.Chunk47

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes48 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨6568⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6569⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6570⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6571⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6572⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6573⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6574⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6575⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨6577⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6578⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6579⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6580⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6581⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6582⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6274⟩, 2))),
  (⟨6585⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6586⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6587⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨6589⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨6590⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨6591⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6592⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨6593⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6594⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6883⟩, 2))),
  (⟨6597⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6598⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6599⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨6601⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6602⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6872⟩, 2))),
  (⟨6605⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6606⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6607⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨6609⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6610⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6862⟩, 2))),
  (⟨6613⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6614⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6615⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨6617⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6618⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6851⟩, 2))),
  (⟨6621⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6622⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6623⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨6625⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6626⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6840⟩, 2))),
  (⟨6629⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6630⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6631⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨6633⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6634⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6829⟩, 2))),
  (⟨6637⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6638⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6639⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨6641⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6642⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6818⟩, 2))),
  (⟨6645⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6646⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6647⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨6649⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6650⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6807⟩, 2))),
  (⟨6653⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6654⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6655⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨6657⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6658⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6796⟩, 2))),
  (⟨6661⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6662⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6663⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨6665⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6666⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6785⟩, 2))),
  (⟨6669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6670⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6671⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨6672⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6673⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6774⟩, 2))),
  (⟨6676⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6677⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6678⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨6680⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6681⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6763⟩, 2))),
  (⟨6684⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6685⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6686⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨6688⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6689⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6753⟩, 2))),
  (⟨6692⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6693⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6694⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨6696⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6697⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6742⟩, 2))),
  (⟨6700⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6701⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6702⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨6704⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6705⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6731⟩, 2))),
  (⟨6708⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6709⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨6711⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6712⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6721⟩, 2))),
  (⟨6715⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6716⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6717⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)))
]

private theorem generatedDecodes48_correct : ∀ i : Fin generatedDecodes48.size,
    decode runtimeBytecode generatedDecodes48[i].1 = generatedDecodes48[i].2 := by
  native_decide

theorem decode_6568 : decode runtimeBytecode ⟨6568⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨0, by decide⟩
theorem decode_6569 : decode runtimeBytecode ⟨6569⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨1, by decide⟩
theorem decode_6570 : decode runtimeBytecode ⟨6570⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨2, by decide⟩
theorem decode_6571 : decode runtimeBytecode ⟨6571⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨3, by decide⟩
theorem decode_6572 : decode runtimeBytecode ⟨6572⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨4, by decide⟩
theorem decode_6573 : decode runtimeBytecode ⟨6573⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨5, by decide⟩
theorem decode_6574 : decode runtimeBytecode ⟨6574⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨6, by decide⟩
theorem decode_6575 : decode runtimeBytecode ⟨6575⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨7, by decide⟩
theorem decode_6577 : decode runtimeBytecode ⟨6577⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨8, by decide⟩
theorem decode_6578 : decode runtimeBytecode ⟨6578⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨9, by decide⟩
theorem decode_6579 : decode runtimeBytecode ⟨6579⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨10, by decide⟩
theorem decode_6580 : decode runtimeBytecode ⟨6580⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨11, by decide⟩
theorem decode_6581 : decode runtimeBytecode ⟨6581⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨12, by decide⟩
theorem decode_6582 : decode runtimeBytecode ⟨6582⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6274⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨13, by decide⟩
theorem decode_6585 : decode runtimeBytecode ⟨6585⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨14, by decide⟩
theorem decode_6586 : decode runtimeBytecode ⟨6586⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨15, by decide⟩
theorem decode_6587 : decode runtimeBytecode ⟨6587⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨16, by decide⟩
theorem decode_6589 : decode runtimeBytecode ⟨6589⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨17, by decide⟩
theorem decode_6590 : decode runtimeBytecode ⟨6590⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨18, by decide⟩
theorem decode_6591 : decode runtimeBytecode ⟨6591⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨19, by decide⟩
theorem decode_6592 : decode runtimeBytecode ⟨6592⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨20, by decide⟩
theorem decode_6593 : decode runtimeBytecode ⟨6593⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨21, by decide⟩
theorem decode_6594 : decode runtimeBytecode ⟨6594⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6883⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨22, by decide⟩
theorem decode_6597 : decode runtimeBytecode ⟨6597⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨23, by decide⟩
theorem decode_6598 : decode runtimeBytecode ⟨6598⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨24, by decide⟩
theorem decode_6599 : decode runtimeBytecode ⟨6599⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨25, by decide⟩
theorem decode_6601 : decode runtimeBytecode ⟨6601⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨26, by decide⟩
theorem decode_6602 : decode runtimeBytecode ⟨6602⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6872⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨27, by decide⟩
theorem decode_6605 : decode runtimeBytecode ⟨6605⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨28, by decide⟩
theorem decode_6606 : decode runtimeBytecode ⟨6606⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨29, by decide⟩
theorem decode_6607 : decode runtimeBytecode ⟨6607⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨30, by decide⟩
theorem decode_6609 : decode runtimeBytecode ⟨6609⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨31, by decide⟩
theorem decode_6610 : decode runtimeBytecode ⟨6610⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6862⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨32, by decide⟩
theorem decode_6613 : decode runtimeBytecode ⟨6613⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨33, by decide⟩
theorem decode_6614 : decode runtimeBytecode ⟨6614⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨34, by decide⟩
theorem decode_6615 : decode runtimeBytecode ⟨6615⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨35, by decide⟩
theorem decode_6617 : decode runtimeBytecode ⟨6617⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨36, by decide⟩
theorem decode_6618 : decode runtimeBytecode ⟨6618⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6851⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨37, by decide⟩
theorem decode_6621 : decode runtimeBytecode ⟨6621⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨38, by decide⟩
theorem decode_6622 : decode runtimeBytecode ⟨6622⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨39, by decide⟩
theorem decode_6623 : decode runtimeBytecode ⟨6623⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨40, by decide⟩
theorem decode_6625 : decode runtimeBytecode ⟨6625⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨41, by decide⟩
theorem decode_6626 : decode runtimeBytecode ⟨6626⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6840⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨42, by decide⟩
theorem decode_6629 : decode runtimeBytecode ⟨6629⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨43, by decide⟩
theorem decode_6630 : decode runtimeBytecode ⟨6630⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨44, by decide⟩
theorem decode_6631 : decode runtimeBytecode ⟨6631⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨45, by decide⟩
theorem decode_6633 : decode runtimeBytecode ⟨6633⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨46, by decide⟩
theorem decode_6634 : decode runtimeBytecode ⟨6634⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6829⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨47, by decide⟩
theorem decode_6637 : decode runtimeBytecode ⟨6637⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨48, by decide⟩
theorem decode_6638 : decode runtimeBytecode ⟨6638⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨49, by decide⟩
theorem decode_6639 : decode runtimeBytecode ⟨6639⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨50, by decide⟩
theorem decode_6641 : decode runtimeBytecode ⟨6641⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨51, by decide⟩
theorem decode_6642 : decode runtimeBytecode ⟨6642⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6818⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨52, by decide⟩
theorem decode_6645 : decode runtimeBytecode ⟨6645⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨53, by decide⟩
theorem decode_6646 : decode runtimeBytecode ⟨6646⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨54, by decide⟩
theorem decode_6647 : decode runtimeBytecode ⟨6647⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨55, by decide⟩
theorem decode_6649 : decode runtimeBytecode ⟨6649⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨56, by decide⟩
theorem decode_6650 : decode runtimeBytecode ⟨6650⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6807⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨57, by decide⟩
theorem decode_6653 : decode runtimeBytecode ⟨6653⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨58, by decide⟩
theorem decode_6654 : decode runtimeBytecode ⟨6654⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨59, by decide⟩
theorem decode_6655 : decode runtimeBytecode ⟨6655⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨60, by decide⟩
theorem decode_6657 : decode runtimeBytecode ⟨6657⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨61, by decide⟩
theorem decode_6658 : decode runtimeBytecode ⟨6658⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6796⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨62, by decide⟩
theorem decode_6661 : decode runtimeBytecode ⟨6661⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨63, by decide⟩
theorem decode_6662 : decode runtimeBytecode ⟨6662⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨64, by decide⟩
theorem decode_6663 : decode runtimeBytecode ⟨6663⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨65, by decide⟩
theorem decode_6665 : decode runtimeBytecode ⟨6665⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨66, by decide⟩
theorem decode_6666 : decode runtimeBytecode ⟨6666⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6785⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨67, by decide⟩
theorem decode_6669 : decode runtimeBytecode ⟨6669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨68, by decide⟩
theorem decode_6670 : decode runtimeBytecode ⟨6670⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨69, by decide⟩
theorem decode_6671 : decode runtimeBytecode ⟨6671⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨70, by decide⟩
theorem decode_6672 : decode runtimeBytecode ⟨6672⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨71, by decide⟩
theorem decode_6673 : decode runtimeBytecode ⟨6673⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6774⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨72, by decide⟩
theorem decode_6676 : decode runtimeBytecode ⟨6676⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨73, by decide⟩
theorem decode_6677 : decode runtimeBytecode ⟨6677⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨74, by decide⟩
theorem decode_6678 : decode runtimeBytecode ⟨6678⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨75, by decide⟩
theorem decode_6680 : decode runtimeBytecode ⟨6680⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨76, by decide⟩
theorem decode_6681 : decode runtimeBytecode ⟨6681⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6763⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨77, by decide⟩
theorem decode_6684 : decode runtimeBytecode ⟨6684⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨78, by decide⟩
theorem decode_6685 : decode runtimeBytecode ⟨6685⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨79, by decide⟩
theorem decode_6686 : decode runtimeBytecode ⟨6686⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨80, by decide⟩
theorem decode_6688 : decode runtimeBytecode ⟨6688⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨81, by decide⟩
theorem decode_6689 : decode runtimeBytecode ⟨6689⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6753⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨82, by decide⟩
theorem decode_6692 : decode runtimeBytecode ⟨6692⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨83, by decide⟩
theorem decode_6693 : decode runtimeBytecode ⟨6693⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨84, by decide⟩
theorem decode_6694 : decode runtimeBytecode ⟨6694⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨85, by decide⟩
theorem decode_6696 : decode runtimeBytecode ⟨6696⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨86, by decide⟩
theorem decode_6697 : decode runtimeBytecode ⟨6697⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6742⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨87, by decide⟩
theorem decode_6700 : decode runtimeBytecode ⟨6700⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨88, by decide⟩
theorem decode_6701 : decode runtimeBytecode ⟨6701⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨89, by decide⟩
theorem decode_6702 : decode runtimeBytecode ⟨6702⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨90, by decide⟩
theorem decode_6704 : decode runtimeBytecode ⟨6704⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨91, by decide⟩
theorem decode_6705 : decode runtimeBytecode ⟨6705⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6731⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨92, by decide⟩
theorem decode_6708 : decode runtimeBytecode ⟨6708⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨93, by decide⟩
theorem decode_6709 : decode runtimeBytecode ⟨6709⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨94, by decide⟩
theorem decode_6711 : decode runtimeBytecode ⟨6711⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨95, by decide⟩
theorem decode_6712 : decode runtimeBytecode ⟨6712⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6721⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨96, by decide⟩
theorem decode_6715 : decode runtimeBytecode ⟨6715⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨97, by decide⟩
theorem decode_6716 : decode runtimeBytecode ⟨6716⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨98, by decide⟩
theorem decode_6717 : decode runtimeBytecode ⟨6717⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)) := by
  simpa [generatedDecodes48] using generatedDecodes48_correct ⟨99, by decide⟩

end Ripemd160Old
