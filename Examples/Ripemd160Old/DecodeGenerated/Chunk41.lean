import Examples.Ripemd160Old.DecodeGenerated.Chunk40

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes41 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5674⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5675⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5676⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5677⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5678⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5679⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5680⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5681⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5682⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5683⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨5685⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5686⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5687⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5688⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5689⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5690⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5693⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5694⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5695⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5696⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨5698⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5699⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5700⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨5701⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5702⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨5703⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5704⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨5705⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5706⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6121⟩, 2))),
  (⟨5709⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5710⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5711⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨5713⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5714⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6102⟩, 2))),
  (⟨5717⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5718⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5719⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨5721⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5722⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6083⟩, 2))),
  (⟨5725⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5726⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5727⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨5729⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5730⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6064⟩, 2))),
  (⟨5733⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5734⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5735⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨5737⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5738⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6045⟩, 2))),
  (⟨5741⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5742⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5743⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨5745⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5746⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6026⟩, 2))),
  (⟨5749⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5750⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5751⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5753⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5754⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6007⟩, 2))),
  (⟨5757⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5758⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5759⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5761⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5762⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5988⟩, 2))),
  (⟨5765⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5766⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5767⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨5769⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5770⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5969⟩, 2))),
  (⟨5773⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5774⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5775⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨5777⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5778⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5950⟩, 2))),
  (⟨5781⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5782⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5783⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨5784⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5785⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5931⟩, 2))),
  (⟨5788⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5789⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5790⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5792⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5793⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5912⟩, 2))),
  (⟨5796⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5797⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5798⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5800⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5801⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5893⟩, 2))),
  (⟨5804⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5805⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5806⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5808⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5809⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5874⟩, 2))),
  (⟨5812⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5813⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5814⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5816⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5817⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5855⟩, 2))),
  (⟨5820⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none))
]

private theorem generatedDecodes41_correct : ∀ i : Fin generatedDecodes41.size,
    decode runtimeBytecode generatedDecodes41[i].1 = generatedDecodes41[i].2 := by
  native_decide

theorem decode_5674 : decode runtimeBytecode ⟨5674⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨0, by decide⟩
theorem decode_5675 : decode runtimeBytecode ⟨5675⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨1, by decide⟩
theorem decode_5676 : decode runtimeBytecode ⟨5676⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨2, by decide⟩
theorem decode_5677 : decode runtimeBytecode ⟨5677⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨3, by decide⟩
theorem decode_5678 : decode runtimeBytecode ⟨5678⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨4, by decide⟩
theorem decode_5679 : decode runtimeBytecode ⟨5679⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨5, by decide⟩
theorem decode_5680 : decode runtimeBytecode ⟨5680⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨6, by decide⟩
theorem decode_5681 : decode runtimeBytecode ⟨5681⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨7, by decide⟩
theorem decode_5682 : decode runtimeBytecode ⟨5682⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨8, by decide⟩
theorem decode_5683 : decode runtimeBytecode ⟨5683⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨9, by decide⟩
theorem decode_5685 : decode runtimeBytecode ⟨5685⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨10, by decide⟩
theorem decode_5686 : decode runtimeBytecode ⟨5686⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨11, by decide⟩
theorem decode_5687 : decode runtimeBytecode ⟨5687⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨12, by decide⟩
theorem decode_5688 : decode runtimeBytecode ⟨5688⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨13, by decide⟩
theorem decode_5689 : decode runtimeBytecode ⟨5689⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨14, by decide⟩
theorem decode_5690 : decode runtimeBytecode ⟨5690⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨15, by decide⟩
theorem decode_5693 : decode runtimeBytecode ⟨5693⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨16, by decide⟩
theorem decode_5694 : decode runtimeBytecode ⟨5694⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨17, by decide⟩
theorem decode_5695 : decode runtimeBytecode ⟨5695⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨18, by decide⟩
theorem decode_5696 : decode runtimeBytecode ⟨5696⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨19, by decide⟩
theorem decode_5698 : decode runtimeBytecode ⟨5698⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨20, by decide⟩
theorem decode_5699 : decode runtimeBytecode ⟨5699⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨21, by decide⟩
theorem decode_5700 : decode runtimeBytecode ⟨5700⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨22, by decide⟩
theorem decode_5701 : decode runtimeBytecode ⟨5701⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨23, by decide⟩
theorem decode_5702 : decode runtimeBytecode ⟨5702⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨24, by decide⟩
theorem decode_5703 : decode runtimeBytecode ⟨5703⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨25, by decide⟩
theorem decode_5704 : decode runtimeBytecode ⟨5704⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨26, by decide⟩
theorem decode_5705 : decode runtimeBytecode ⟨5705⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨27, by decide⟩
theorem decode_5706 : decode runtimeBytecode ⟨5706⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6121⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨28, by decide⟩
theorem decode_5709 : decode runtimeBytecode ⟨5709⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨29, by decide⟩
theorem decode_5710 : decode runtimeBytecode ⟨5710⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨30, by decide⟩
theorem decode_5711 : decode runtimeBytecode ⟨5711⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨31, by decide⟩
theorem decode_5713 : decode runtimeBytecode ⟨5713⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨32, by decide⟩
theorem decode_5714 : decode runtimeBytecode ⟨5714⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6102⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨33, by decide⟩
theorem decode_5717 : decode runtimeBytecode ⟨5717⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨34, by decide⟩
theorem decode_5718 : decode runtimeBytecode ⟨5718⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨35, by decide⟩
theorem decode_5719 : decode runtimeBytecode ⟨5719⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨36, by decide⟩
theorem decode_5721 : decode runtimeBytecode ⟨5721⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨37, by decide⟩
theorem decode_5722 : decode runtimeBytecode ⟨5722⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6083⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨38, by decide⟩
theorem decode_5725 : decode runtimeBytecode ⟨5725⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨39, by decide⟩
theorem decode_5726 : decode runtimeBytecode ⟨5726⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨40, by decide⟩
theorem decode_5727 : decode runtimeBytecode ⟨5727⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨41, by decide⟩
theorem decode_5729 : decode runtimeBytecode ⟨5729⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨42, by decide⟩
theorem decode_5730 : decode runtimeBytecode ⟨5730⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6064⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨43, by decide⟩
theorem decode_5733 : decode runtimeBytecode ⟨5733⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨44, by decide⟩
theorem decode_5734 : decode runtimeBytecode ⟨5734⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨45, by decide⟩
theorem decode_5735 : decode runtimeBytecode ⟨5735⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨46, by decide⟩
theorem decode_5737 : decode runtimeBytecode ⟨5737⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨47, by decide⟩
theorem decode_5738 : decode runtimeBytecode ⟨5738⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6045⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨48, by decide⟩
theorem decode_5741 : decode runtimeBytecode ⟨5741⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨49, by decide⟩
theorem decode_5742 : decode runtimeBytecode ⟨5742⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨50, by decide⟩
theorem decode_5743 : decode runtimeBytecode ⟨5743⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨51, by decide⟩
theorem decode_5745 : decode runtimeBytecode ⟨5745⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨52, by decide⟩
theorem decode_5746 : decode runtimeBytecode ⟨5746⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6026⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨53, by decide⟩
theorem decode_5749 : decode runtimeBytecode ⟨5749⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨54, by decide⟩
theorem decode_5750 : decode runtimeBytecode ⟨5750⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨55, by decide⟩
theorem decode_5751 : decode runtimeBytecode ⟨5751⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨56, by decide⟩
theorem decode_5753 : decode runtimeBytecode ⟨5753⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨57, by decide⟩
theorem decode_5754 : decode runtimeBytecode ⟨5754⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6007⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨58, by decide⟩
theorem decode_5757 : decode runtimeBytecode ⟨5757⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨59, by decide⟩
theorem decode_5758 : decode runtimeBytecode ⟨5758⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨60, by decide⟩
theorem decode_5759 : decode runtimeBytecode ⟨5759⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨61, by decide⟩
theorem decode_5761 : decode runtimeBytecode ⟨5761⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨62, by decide⟩
theorem decode_5762 : decode runtimeBytecode ⟨5762⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5988⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨63, by decide⟩
theorem decode_5765 : decode runtimeBytecode ⟨5765⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨64, by decide⟩
theorem decode_5766 : decode runtimeBytecode ⟨5766⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨65, by decide⟩
theorem decode_5767 : decode runtimeBytecode ⟨5767⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨66, by decide⟩
theorem decode_5769 : decode runtimeBytecode ⟨5769⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨67, by decide⟩
theorem decode_5770 : decode runtimeBytecode ⟨5770⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5969⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨68, by decide⟩
theorem decode_5773 : decode runtimeBytecode ⟨5773⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨69, by decide⟩
theorem decode_5774 : decode runtimeBytecode ⟨5774⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨70, by decide⟩
theorem decode_5775 : decode runtimeBytecode ⟨5775⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨71, by decide⟩
theorem decode_5777 : decode runtimeBytecode ⟨5777⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨72, by decide⟩
theorem decode_5778 : decode runtimeBytecode ⟨5778⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5950⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨73, by decide⟩
theorem decode_5781 : decode runtimeBytecode ⟨5781⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨74, by decide⟩
theorem decode_5782 : decode runtimeBytecode ⟨5782⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨75, by decide⟩
theorem decode_5783 : decode runtimeBytecode ⟨5783⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨76, by decide⟩
theorem decode_5784 : decode runtimeBytecode ⟨5784⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨77, by decide⟩
theorem decode_5785 : decode runtimeBytecode ⟨5785⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5931⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨78, by decide⟩
theorem decode_5788 : decode runtimeBytecode ⟨5788⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨79, by decide⟩
theorem decode_5789 : decode runtimeBytecode ⟨5789⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨80, by decide⟩
theorem decode_5790 : decode runtimeBytecode ⟨5790⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨81, by decide⟩
theorem decode_5792 : decode runtimeBytecode ⟨5792⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨82, by decide⟩
theorem decode_5793 : decode runtimeBytecode ⟨5793⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5912⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨83, by decide⟩
theorem decode_5796 : decode runtimeBytecode ⟨5796⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨84, by decide⟩
theorem decode_5797 : decode runtimeBytecode ⟨5797⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨85, by decide⟩
theorem decode_5798 : decode runtimeBytecode ⟨5798⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨86, by decide⟩
theorem decode_5800 : decode runtimeBytecode ⟨5800⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨87, by decide⟩
theorem decode_5801 : decode runtimeBytecode ⟨5801⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5893⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨88, by decide⟩
theorem decode_5804 : decode runtimeBytecode ⟨5804⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨89, by decide⟩
theorem decode_5805 : decode runtimeBytecode ⟨5805⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨90, by decide⟩
theorem decode_5806 : decode runtimeBytecode ⟨5806⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨91, by decide⟩
theorem decode_5808 : decode runtimeBytecode ⟨5808⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨92, by decide⟩
theorem decode_5809 : decode runtimeBytecode ⟨5809⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5874⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨93, by decide⟩
theorem decode_5812 : decode runtimeBytecode ⟨5812⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨94, by decide⟩
theorem decode_5813 : decode runtimeBytecode ⟨5813⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨95, by decide⟩
theorem decode_5814 : decode runtimeBytecode ⟨5814⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨96, by decide⟩
theorem decode_5816 : decode runtimeBytecode ⟨5816⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨97, by decide⟩
theorem decode_5817 : decode runtimeBytecode ⟨5817⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5855⟩, 2)) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨98, by decide⟩
theorem decode_5820 : decode runtimeBytecode ⟨5820⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes41] using generatedDecodes41_correct ⟨99, by decide⟩

end Ripemd160Old
