import Examples.Ripemd160Old.DecodeGenerated.Chunk32

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes33 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4660⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4661⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4662⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4663⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4664⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4665⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4668⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4670⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4671⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4672⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4673⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4674⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4675⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4676⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4677⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨4679⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4680⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4681⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4682⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4683⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4684⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4687⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4688⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4689⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4690⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4691⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4692⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4693⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4694⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4695⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4696⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4698⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4699⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4700⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4701⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4702⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4703⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4706⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4707⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4708⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4709⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4710⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4711⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4712⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4713⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4714⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4715⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨4717⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4718⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4719⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4720⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4721⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4722⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4725⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4726⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4727⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4728⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4729⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4730⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4731⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4732⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4733⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4734⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨4736⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4737⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4738⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4739⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4740⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4741⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4744⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4745⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4746⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4747⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4748⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4749⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4750⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4751⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4752⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4753⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨4755⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4756⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4757⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4758⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4759⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4760⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4763⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4764⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4765⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4766⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4767⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4768⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4769⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4770⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4771⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4772⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4774⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4775⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4776⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4777⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes33_correct : ∀ i : Fin generatedDecodes33.size,
    decode runtimeBytecode generatedDecodes33[i].1 = generatedDecodes33[i].2 := by
  native_decide

theorem decode_4660 : decode runtimeBytecode ⟨4660⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨0, by decide⟩
theorem decode_4661 : decode runtimeBytecode ⟨4661⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨1, by decide⟩
theorem decode_4662 : decode runtimeBytecode ⟨4662⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨2, by decide⟩
theorem decode_4663 : decode runtimeBytecode ⟨4663⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨3, by decide⟩
theorem decode_4664 : decode runtimeBytecode ⟨4664⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨4, by decide⟩
theorem decode_4665 : decode runtimeBytecode ⟨4665⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨5, by decide⟩
theorem decode_4668 : decode runtimeBytecode ⟨4668⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨6, by decide⟩
theorem decode_4669 : decode runtimeBytecode ⟨4669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨7, by decide⟩
theorem decode_4670 : decode runtimeBytecode ⟨4670⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨8, by decide⟩
theorem decode_4671 : decode runtimeBytecode ⟨4671⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨9, by decide⟩
theorem decode_4672 : decode runtimeBytecode ⟨4672⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨10, by decide⟩
theorem decode_4673 : decode runtimeBytecode ⟨4673⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨11, by decide⟩
theorem decode_4674 : decode runtimeBytecode ⟨4674⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨12, by decide⟩
theorem decode_4675 : decode runtimeBytecode ⟨4675⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨13, by decide⟩
theorem decode_4676 : decode runtimeBytecode ⟨4676⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨14, by decide⟩
theorem decode_4677 : decode runtimeBytecode ⟨4677⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨15, by decide⟩
theorem decode_4679 : decode runtimeBytecode ⟨4679⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨16, by decide⟩
theorem decode_4680 : decode runtimeBytecode ⟨4680⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨17, by decide⟩
theorem decode_4681 : decode runtimeBytecode ⟨4681⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨18, by decide⟩
theorem decode_4682 : decode runtimeBytecode ⟨4682⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨19, by decide⟩
theorem decode_4683 : decode runtimeBytecode ⟨4683⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨20, by decide⟩
theorem decode_4684 : decode runtimeBytecode ⟨4684⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨21, by decide⟩
theorem decode_4687 : decode runtimeBytecode ⟨4687⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨22, by decide⟩
theorem decode_4688 : decode runtimeBytecode ⟨4688⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨23, by decide⟩
theorem decode_4689 : decode runtimeBytecode ⟨4689⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨24, by decide⟩
theorem decode_4690 : decode runtimeBytecode ⟨4690⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨25, by decide⟩
theorem decode_4691 : decode runtimeBytecode ⟨4691⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨26, by decide⟩
theorem decode_4692 : decode runtimeBytecode ⟨4692⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨27, by decide⟩
theorem decode_4693 : decode runtimeBytecode ⟨4693⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨28, by decide⟩
theorem decode_4694 : decode runtimeBytecode ⟨4694⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨29, by decide⟩
theorem decode_4695 : decode runtimeBytecode ⟨4695⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨30, by decide⟩
theorem decode_4696 : decode runtimeBytecode ⟨4696⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨31, by decide⟩
theorem decode_4698 : decode runtimeBytecode ⟨4698⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨32, by decide⟩
theorem decode_4699 : decode runtimeBytecode ⟨4699⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨33, by decide⟩
theorem decode_4700 : decode runtimeBytecode ⟨4700⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨34, by decide⟩
theorem decode_4701 : decode runtimeBytecode ⟨4701⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨35, by decide⟩
theorem decode_4702 : decode runtimeBytecode ⟨4702⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨36, by decide⟩
theorem decode_4703 : decode runtimeBytecode ⟨4703⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨37, by decide⟩
theorem decode_4706 : decode runtimeBytecode ⟨4706⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨38, by decide⟩
theorem decode_4707 : decode runtimeBytecode ⟨4707⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨39, by decide⟩
theorem decode_4708 : decode runtimeBytecode ⟨4708⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨40, by decide⟩
theorem decode_4709 : decode runtimeBytecode ⟨4709⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨41, by decide⟩
theorem decode_4710 : decode runtimeBytecode ⟨4710⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨42, by decide⟩
theorem decode_4711 : decode runtimeBytecode ⟨4711⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨43, by decide⟩
theorem decode_4712 : decode runtimeBytecode ⟨4712⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨44, by decide⟩
theorem decode_4713 : decode runtimeBytecode ⟨4713⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨45, by decide⟩
theorem decode_4714 : decode runtimeBytecode ⟨4714⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨46, by decide⟩
theorem decode_4715 : decode runtimeBytecode ⟨4715⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨47, by decide⟩
theorem decode_4717 : decode runtimeBytecode ⟨4717⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨48, by decide⟩
theorem decode_4718 : decode runtimeBytecode ⟨4718⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨49, by decide⟩
theorem decode_4719 : decode runtimeBytecode ⟨4719⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨50, by decide⟩
theorem decode_4720 : decode runtimeBytecode ⟨4720⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨51, by decide⟩
theorem decode_4721 : decode runtimeBytecode ⟨4721⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨52, by decide⟩
theorem decode_4722 : decode runtimeBytecode ⟨4722⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨53, by decide⟩
theorem decode_4725 : decode runtimeBytecode ⟨4725⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨54, by decide⟩
theorem decode_4726 : decode runtimeBytecode ⟨4726⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨55, by decide⟩
theorem decode_4727 : decode runtimeBytecode ⟨4727⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨56, by decide⟩
theorem decode_4728 : decode runtimeBytecode ⟨4728⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨57, by decide⟩
theorem decode_4729 : decode runtimeBytecode ⟨4729⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨58, by decide⟩
theorem decode_4730 : decode runtimeBytecode ⟨4730⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨59, by decide⟩
theorem decode_4731 : decode runtimeBytecode ⟨4731⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨60, by decide⟩
theorem decode_4732 : decode runtimeBytecode ⟨4732⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨61, by decide⟩
theorem decode_4733 : decode runtimeBytecode ⟨4733⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨62, by decide⟩
theorem decode_4734 : decode runtimeBytecode ⟨4734⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨63, by decide⟩
theorem decode_4736 : decode runtimeBytecode ⟨4736⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨64, by decide⟩
theorem decode_4737 : decode runtimeBytecode ⟨4737⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨65, by decide⟩
theorem decode_4738 : decode runtimeBytecode ⟨4738⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨66, by decide⟩
theorem decode_4739 : decode runtimeBytecode ⟨4739⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨67, by decide⟩
theorem decode_4740 : decode runtimeBytecode ⟨4740⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨68, by decide⟩
theorem decode_4741 : decode runtimeBytecode ⟨4741⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨69, by decide⟩
theorem decode_4744 : decode runtimeBytecode ⟨4744⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨70, by decide⟩
theorem decode_4745 : decode runtimeBytecode ⟨4745⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨71, by decide⟩
theorem decode_4746 : decode runtimeBytecode ⟨4746⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨72, by decide⟩
theorem decode_4747 : decode runtimeBytecode ⟨4747⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨73, by decide⟩
theorem decode_4748 : decode runtimeBytecode ⟨4748⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨74, by decide⟩
theorem decode_4749 : decode runtimeBytecode ⟨4749⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨75, by decide⟩
theorem decode_4750 : decode runtimeBytecode ⟨4750⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨76, by decide⟩
theorem decode_4751 : decode runtimeBytecode ⟨4751⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨77, by decide⟩
theorem decode_4752 : decode runtimeBytecode ⟨4752⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨78, by decide⟩
theorem decode_4753 : decode runtimeBytecode ⟨4753⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨79, by decide⟩
theorem decode_4755 : decode runtimeBytecode ⟨4755⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨80, by decide⟩
theorem decode_4756 : decode runtimeBytecode ⟨4756⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨81, by decide⟩
theorem decode_4757 : decode runtimeBytecode ⟨4757⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨82, by decide⟩
theorem decode_4758 : decode runtimeBytecode ⟨4758⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨83, by decide⟩
theorem decode_4759 : decode runtimeBytecode ⟨4759⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨84, by decide⟩
theorem decode_4760 : decode runtimeBytecode ⟨4760⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨85, by decide⟩
theorem decode_4763 : decode runtimeBytecode ⟨4763⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨86, by decide⟩
theorem decode_4764 : decode runtimeBytecode ⟨4764⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨87, by decide⟩
theorem decode_4765 : decode runtimeBytecode ⟨4765⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨88, by decide⟩
theorem decode_4766 : decode runtimeBytecode ⟨4766⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨89, by decide⟩
theorem decode_4767 : decode runtimeBytecode ⟨4767⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨90, by decide⟩
theorem decode_4768 : decode runtimeBytecode ⟨4768⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨91, by decide⟩
theorem decode_4769 : decode runtimeBytecode ⟨4769⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨92, by decide⟩
theorem decode_4770 : decode runtimeBytecode ⟨4770⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨93, by decide⟩
theorem decode_4771 : decode runtimeBytecode ⟨4771⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨94, by decide⟩
theorem decode_4772 : decode runtimeBytecode ⟨4772⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨95, by decide⟩
theorem decode_4774 : decode runtimeBytecode ⟨4774⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨96, by decide⟩
theorem decode_4775 : decode runtimeBytecode ⟨4775⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨97, by decide⟩
theorem decode_4776 : decode runtimeBytecode ⟨4776⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨98, by decide⟩
theorem decode_4777 : decode runtimeBytecode ⟨4777⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes33] using generatedDecodes33_correct ⟨99, by decide⟩

end Ripemd160Old
