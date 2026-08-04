import Examples.Ripemd160Old.DecodeGenerated.Chunk54

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes55 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7580⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7581⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7582⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7584⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7585⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7724⟩, 2))),
  (⟨7588⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7589⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7590⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7592⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7593⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7713⟩, 2))),
  (⟨7596⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7597⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨7598⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7599⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7600⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7702⟩, 2))),
  (⟨7603⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7604⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7605⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7607⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7608⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7691⟩, 2))),
  (⟨7611⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7612⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7613⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7615⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7616⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7680⟩, 2))),
  (⟨7619⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7620⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7621⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7623⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7624⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7669⟩, 2))),
  (⟨7627⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7628⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7629⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7631⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7632⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7658⟩, 2))),
  (⟨7635⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7636⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7638⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7639⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7648⟩, 2))),
  (⟨7642⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7643⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7644⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2))),
  (⟨7647⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7648⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7649⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7651⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7653⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7654⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7657⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7658⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7659⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7660⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7661⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7662⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7664⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7665⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7668⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7670⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7671⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7672⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7673⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7675⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7676⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7679⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7680⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7681⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7682⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7683⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7684⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7686⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7687⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7690⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7691⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7692⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7693⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7694⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7695⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7697⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7698⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7701⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7702⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7703⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7704⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7705⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7706⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7708⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7709⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7712⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7713⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7714⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7715⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7716⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7717⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7719⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7720⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7723⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7724⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7725⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes55_correct : ∀ i : Fin generatedDecodes55.size,
    decode runtimeBytecode generatedDecodes55[i].1 = generatedDecodes55[i].2 := by
  native_decide

theorem decode_7580 : decode runtimeBytecode ⟨7580⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨0, by decide⟩
theorem decode_7581 : decode runtimeBytecode ⟨7581⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨1, by decide⟩
theorem decode_7582 : decode runtimeBytecode ⟨7582⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨2, by decide⟩
theorem decode_7584 : decode runtimeBytecode ⟨7584⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨3, by decide⟩
theorem decode_7585 : decode runtimeBytecode ⟨7585⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7724⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨4, by decide⟩
theorem decode_7588 : decode runtimeBytecode ⟨7588⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨5, by decide⟩
theorem decode_7589 : decode runtimeBytecode ⟨7589⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨6, by decide⟩
theorem decode_7590 : decode runtimeBytecode ⟨7590⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨7, by decide⟩
theorem decode_7592 : decode runtimeBytecode ⟨7592⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨8, by decide⟩
theorem decode_7593 : decode runtimeBytecode ⟨7593⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7713⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨9, by decide⟩
theorem decode_7596 : decode runtimeBytecode ⟨7596⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨10, by decide⟩
theorem decode_7597 : decode runtimeBytecode ⟨7597⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨11, by decide⟩
theorem decode_7598 : decode runtimeBytecode ⟨7598⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨12, by decide⟩
theorem decode_7599 : decode runtimeBytecode ⟨7599⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨13, by decide⟩
theorem decode_7600 : decode runtimeBytecode ⟨7600⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7702⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨14, by decide⟩
theorem decode_7603 : decode runtimeBytecode ⟨7603⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨15, by decide⟩
theorem decode_7604 : decode runtimeBytecode ⟨7604⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨16, by decide⟩
theorem decode_7605 : decode runtimeBytecode ⟨7605⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨17, by decide⟩
theorem decode_7607 : decode runtimeBytecode ⟨7607⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨18, by decide⟩
theorem decode_7608 : decode runtimeBytecode ⟨7608⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7691⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨19, by decide⟩
theorem decode_7611 : decode runtimeBytecode ⟨7611⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨20, by decide⟩
theorem decode_7612 : decode runtimeBytecode ⟨7612⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨21, by decide⟩
theorem decode_7613 : decode runtimeBytecode ⟨7613⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨22, by decide⟩
theorem decode_7615 : decode runtimeBytecode ⟨7615⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨23, by decide⟩
theorem decode_7616 : decode runtimeBytecode ⟨7616⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7680⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨24, by decide⟩
theorem decode_7619 : decode runtimeBytecode ⟨7619⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨25, by decide⟩
theorem decode_7620 : decode runtimeBytecode ⟨7620⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨26, by decide⟩
theorem decode_7621 : decode runtimeBytecode ⟨7621⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨27, by decide⟩
theorem decode_7623 : decode runtimeBytecode ⟨7623⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨28, by decide⟩
theorem decode_7624 : decode runtimeBytecode ⟨7624⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7669⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨29, by decide⟩
theorem decode_7627 : decode runtimeBytecode ⟨7627⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨30, by decide⟩
theorem decode_7628 : decode runtimeBytecode ⟨7628⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨31, by decide⟩
theorem decode_7629 : decode runtimeBytecode ⟨7629⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨32, by decide⟩
theorem decode_7631 : decode runtimeBytecode ⟨7631⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨33, by decide⟩
theorem decode_7632 : decode runtimeBytecode ⟨7632⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7658⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨34, by decide⟩
theorem decode_7635 : decode runtimeBytecode ⟨7635⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨35, by decide⟩
theorem decode_7636 : decode runtimeBytecode ⟨7636⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨36, by decide⟩
theorem decode_7638 : decode runtimeBytecode ⟨7638⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨37, by decide⟩
theorem decode_7639 : decode runtimeBytecode ⟨7639⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7648⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨38, by decide⟩
theorem decode_7642 : decode runtimeBytecode ⟨7642⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨39, by decide⟩
theorem decode_7643 : decode runtimeBytecode ⟨7643⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨40, by decide⟩
theorem decode_7644 : decode runtimeBytecode ⟨7644⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨41, by decide⟩
theorem decode_7647 : decode runtimeBytecode ⟨7647⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨42, by decide⟩
theorem decode_7648 : decode runtimeBytecode ⟨7648⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨43, by decide⟩
theorem decode_7649 : decode runtimeBytecode ⟨7649⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨44, by decide⟩
theorem decode_7650 : decode runtimeBytecode ⟨7650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨45, by decide⟩
theorem decode_7651 : decode runtimeBytecode ⟨7651⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨46, by decide⟩
theorem decode_7653 : decode runtimeBytecode ⟨7653⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨47, by decide⟩
theorem decode_7654 : decode runtimeBytecode ⟨7654⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨48, by decide⟩
theorem decode_7657 : decode runtimeBytecode ⟨7657⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨49, by decide⟩
theorem decode_7658 : decode runtimeBytecode ⟨7658⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨50, by decide⟩
theorem decode_7659 : decode runtimeBytecode ⟨7659⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨51, by decide⟩
theorem decode_7660 : decode runtimeBytecode ⟨7660⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨52, by decide⟩
theorem decode_7661 : decode runtimeBytecode ⟨7661⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨53, by decide⟩
theorem decode_7662 : decode runtimeBytecode ⟨7662⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨54, by decide⟩
theorem decode_7664 : decode runtimeBytecode ⟨7664⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨55, by decide⟩
theorem decode_7665 : decode runtimeBytecode ⟨7665⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨56, by decide⟩
theorem decode_7668 : decode runtimeBytecode ⟨7668⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨57, by decide⟩
theorem decode_7669 : decode runtimeBytecode ⟨7669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨58, by decide⟩
theorem decode_7670 : decode runtimeBytecode ⟨7670⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨59, by decide⟩
theorem decode_7671 : decode runtimeBytecode ⟨7671⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨60, by decide⟩
theorem decode_7672 : decode runtimeBytecode ⟨7672⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨61, by decide⟩
theorem decode_7673 : decode runtimeBytecode ⟨7673⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨62, by decide⟩
theorem decode_7675 : decode runtimeBytecode ⟨7675⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨63, by decide⟩
theorem decode_7676 : decode runtimeBytecode ⟨7676⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨64, by decide⟩
theorem decode_7679 : decode runtimeBytecode ⟨7679⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨65, by decide⟩
theorem decode_7680 : decode runtimeBytecode ⟨7680⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨66, by decide⟩
theorem decode_7681 : decode runtimeBytecode ⟨7681⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨67, by decide⟩
theorem decode_7682 : decode runtimeBytecode ⟨7682⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨68, by decide⟩
theorem decode_7683 : decode runtimeBytecode ⟨7683⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨69, by decide⟩
theorem decode_7684 : decode runtimeBytecode ⟨7684⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨70, by decide⟩
theorem decode_7686 : decode runtimeBytecode ⟨7686⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨71, by decide⟩
theorem decode_7687 : decode runtimeBytecode ⟨7687⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨72, by decide⟩
theorem decode_7690 : decode runtimeBytecode ⟨7690⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨73, by decide⟩
theorem decode_7691 : decode runtimeBytecode ⟨7691⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨74, by decide⟩
theorem decode_7692 : decode runtimeBytecode ⟨7692⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨75, by decide⟩
theorem decode_7693 : decode runtimeBytecode ⟨7693⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨76, by decide⟩
theorem decode_7694 : decode runtimeBytecode ⟨7694⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨77, by decide⟩
theorem decode_7695 : decode runtimeBytecode ⟨7695⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨78, by decide⟩
theorem decode_7697 : decode runtimeBytecode ⟨7697⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨79, by decide⟩
theorem decode_7698 : decode runtimeBytecode ⟨7698⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨80, by decide⟩
theorem decode_7701 : decode runtimeBytecode ⟨7701⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨81, by decide⟩
theorem decode_7702 : decode runtimeBytecode ⟨7702⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨82, by decide⟩
theorem decode_7703 : decode runtimeBytecode ⟨7703⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨83, by decide⟩
theorem decode_7704 : decode runtimeBytecode ⟨7704⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨84, by decide⟩
theorem decode_7705 : decode runtimeBytecode ⟨7705⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨85, by decide⟩
theorem decode_7706 : decode runtimeBytecode ⟨7706⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨86, by decide⟩
theorem decode_7708 : decode runtimeBytecode ⟨7708⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨87, by decide⟩
theorem decode_7709 : decode runtimeBytecode ⟨7709⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨88, by decide⟩
theorem decode_7712 : decode runtimeBytecode ⟨7712⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨89, by decide⟩
theorem decode_7713 : decode runtimeBytecode ⟨7713⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨90, by decide⟩
theorem decode_7714 : decode runtimeBytecode ⟨7714⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨91, by decide⟩
theorem decode_7715 : decode runtimeBytecode ⟨7715⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨92, by decide⟩
theorem decode_7716 : decode runtimeBytecode ⟨7716⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨93, by decide⟩
theorem decode_7717 : decode runtimeBytecode ⟨7717⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨94, by decide⟩
theorem decode_7719 : decode runtimeBytecode ⟨7719⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨95, by decide⟩
theorem decode_7720 : decode runtimeBytecode ⟨7720⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨96, by decide⟩
theorem decode_7723 : decode runtimeBytecode ⟨7723⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨97, by decide⟩
theorem decode_7724 : decode runtimeBytecode ⟨7724⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨98, by decide⟩
theorem decode_7725 : decode runtimeBytecode ⟨7725⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes55] using generatedDecodes55_correct ⟨99, by decide⟩

end Ripemd160Old
