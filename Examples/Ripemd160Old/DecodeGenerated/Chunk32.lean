import Examples.Ripemd160Old.DecodeGenerated.Chunk31

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes32 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4541⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4542⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4543⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4544⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨4546⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4547⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4548⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4549⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4550⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4551⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4554⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4555⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4556⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4557⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4558⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4559⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4560⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4561⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4562⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4563⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨4565⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4566⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4567⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4568⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4569⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4570⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4573⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4575⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4576⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4577⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4578⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4579⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4580⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4581⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4582⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4584⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4585⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4586⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4587⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4588⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4589⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4592⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4593⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4594⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4595⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4596⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4597⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4598⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4599⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4600⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4601⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨4603⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4604⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4605⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4606⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4607⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4608⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4611⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4612⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4613⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4614⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4615⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4616⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4617⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4618⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4619⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4620⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨4622⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4623⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4624⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4625⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4626⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4627⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4630⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4631⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4632⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4633⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4634⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4635⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4636⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4637⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4638⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4639⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨4641⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4642⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4643⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4644⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4645⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4646⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4649⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4651⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4652⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4653⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4654⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4655⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4656⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4657⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4658⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)))
]

private theorem generatedDecodes32_correct : ∀ i : Fin generatedDecodes32.size,
    decode runtimeBytecode generatedDecodes32[i].1 = generatedDecodes32[i].2 := by
  native_decide

theorem decode_4541 : decode runtimeBytecode ⟨4541⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨0, by decide⟩
theorem decode_4542 : decode runtimeBytecode ⟨4542⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨1, by decide⟩
theorem decode_4543 : decode runtimeBytecode ⟨4543⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨2, by decide⟩
theorem decode_4544 : decode runtimeBytecode ⟨4544⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨3, by decide⟩
theorem decode_4546 : decode runtimeBytecode ⟨4546⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨4, by decide⟩
theorem decode_4547 : decode runtimeBytecode ⟨4547⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨5, by decide⟩
theorem decode_4548 : decode runtimeBytecode ⟨4548⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨6, by decide⟩
theorem decode_4549 : decode runtimeBytecode ⟨4549⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨7, by decide⟩
theorem decode_4550 : decode runtimeBytecode ⟨4550⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨8, by decide⟩
theorem decode_4551 : decode runtimeBytecode ⟨4551⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨9, by decide⟩
theorem decode_4554 : decode runtimeBytecode ⟨4554⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨10, by decide⟩
theorem decode_4555 : decode runtimeBytecode ⟨4555⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨11, by decide⟩
theorem decode_4556 : decode runtimeBytecode ⟨4556⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨12, by decide⟩
theorem decode_4557 : decode runtimeBytecode ⟨4557⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨13, by decide⟩
theorem decode_4558 : decode runtimeBytecode ⟨4558⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨14, by decide⟩
theorem decode_4559 : decode runtimeBytecode ⟨4559⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨15, by decide⟩
theorem decode_4560 : decode runtimeBytecode ⟨4560⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨16, by decide⟩
theorem decode_4561 : decode runtimeBytecode ⟨4561⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨17, by decide⟩
theorem decode_4562 : decode runtimeBytecode ⟨4562⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨18, by decide⟩
theorem decode_4563 : decode runtimeBytecode ⟨4563⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨19, by decide⟩
theorem decode_4565 : decode runtimeBytecode ⟨4565⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨20, by decide⟩
theorem decode_4566 : decode runtimeBytecode ⟨4566⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨21, by decide⟩
theorem decode_4567 : decode runtimeBytecode ⟨4567⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨22, by decide⟩
theorem decode_4568 : decode runtimeBytecode ⟨4568⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨23, by decide⟩
theorem decode_4569 : decode runtimeBytecode ⟨4569⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨24, by decide⟩
theorem decode_4570 : decode runtimeBytecode ⟨4570⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨25, by decide⟩
theorem decode_4573 : decode runtimeBytecode ⟨4573⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨26, by decide⟩
theorem decode_4574 : decode runtimeBytecode ⟨4574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨27, by decide⟩
theorem decode_4575 : decode runtimeBytecode ⟨4575⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨28, by decide⟩
theorem decode_4576 : decode runtimeBytecode ⟨4576⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨29, by decide⟩
theorem decode_4577 : decode runtimeBytecode ⟨4577⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨30, by decide⟩
theorem decode_4578 : decode runtimeBytecode ⟨4578⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨31, by decide⟩
theorem decode_4579 : decode runtimeBytecode ⟨4579⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨32, by decide⟩
theorem decode_4580 : decode runtimeBytecode ⟨4580⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨33, by decide⟩
theorem decode_4581 : decode runtimeBytecode ⟨4581⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨34, by decide⟩
theorem decode_4582 : decode runtimeBytecode ⟨4582⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨35, by decide⟩
theorem decode_4584 : decode runtimeBytecode ⟨4584⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨36, by decide⟩
theorem decode_4585 : decode runtimeBytecode ⟨4585⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨37, by decide⟩
theorem decode_4586 : decode runtimeBytecode ⟨4586⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨38, by decide⟩
theorem decode_4587 : decode runtimeBytecode ⟨4587⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨39, by decide⟩
theorem decode_4588 : decode runtimeBytecode ⟨4588⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨40, by decide⟩
theorem decode_4589 : decode runtimeBytecode ⟨4589⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨41, by decide⟩
theorem decode_4592 : decode runtimeBytecode ⟨4592⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨42, by decide⟩
theorem decode_4593 : decode runtimeBytecode ⟨4593⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨43, by decide⟩
theorem decode_4594 : decode runtimeBytecode ⟨4594⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨44, by decide⟩
theorem decode_4595 : decode runtimeBytecode ⟨4595⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨45, by decide⟩
theorem decode_4596 : decode runtimeBytecode ⟨4596⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨46, by decide⟩
theorem decode_4597 : decode runtimeBytecode ⟨4597⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨47, by decide⟩
theorem decode_4598 : decode runtimeBytecode ⟨4598⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨48, by decide⟩
theorem decode_4599 : decode runtimeBytecode ⟨4599⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨49, by decide⟩
theorem decode_4600 : decode runtimeBytecode ⟨4600⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨50, by decide⟩
theorem decode_4601 : decode runtimeBytecode ⟨4601⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨51, by decide⟩
theorem decode_4603 : decode runtimeBytecode ⟨4603⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨52, by decide⟩
theorem decode_4604 : decode runtimeBytecode ⟨4604⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨53, by decide⟩
theorem decode_4605 : decode runtimeBytecode ⟨4605⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨54, by decide⟩
theorem decode_4606 : decode runtimeBytecode ⟨4606⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨55, by decide⟩
theorem decode_4607 : decode runtimeBytecode ⟨4607⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨56, by decide⟩
theorem decode_4608 : decode runtimeBytecode ⟨4608⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨57, by decide⟩
theorem decode_4611 : decode runtimeBytecode ⟨4611⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨58, by decide⟩
theorem decode_4612 : decode runtimeBytecode ⟨4612⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨59, by decide⟩
theorem decode_4613 : decode runtimeBytecode ⟨4613⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨60, by decide⟩
theorem decode_4614 : decode runtimeBytecode ⟨4614⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨61, by decide⟩
theorem decode_4615 : decode runtimeBytecode ⟨4615⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨62, by decide⟩
theorem decode_4616 : decode runtimeBytecode ⟨4616⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨63, by decide⟩
theorem decode_4617 : decode runtimeBytecode ⟨4617⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨64, by decide⟩
theorem decode_4618 : decode runtimeBytecode ⟨4618⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨65, by decide⟩
theorem decode_4619 : decode runtimeBytecode ⟨4619⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨66, by decide⟩
theorem decode_4620 : decode runtimeBytecode ⟨4620⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨67, by decide⟩
theorem decode_4622 : decode runtimeBytecode ⟨4622⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨68, by decide⟩
theorem decode_4623 : decode runtimeBytecode ⟨4623⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨69, by decide⟩
theorem decode_4624 : decode runtimeBytecode ⟨4624⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨70, by decide⟩
theorem decode_4625 : decode runtimeBytecode ⟨4625⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨71, by decide⟩
theorem decode_4626 : decode runtimeBytecode ⟨4626⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨72, by decide⟩
theorem decode_4627 : decode runtimeBytecode ⟨4627⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨73, by decide⟩
theorem decode_4630 : decode runtimeBytecode ⟨4630⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨74, by decide⟩
theorem decode_4631 : decode runtimeBytecode ⟨4631⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨75, by decide⟩
theorem decode_4632 : decode runtimeBytecode ⟨4632⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨76, by decide⟩
theorem decode_4633 : decode runtimeBytecode ⟨4633⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨77, by decide⟩
theorem decode_4634 : decode runtimeBytecode ⟨4634⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨78, by decide⟩
theorem decode_4635 : decode runtimeBytecode ⟨4635⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨79, by decide⟩
theorem decode_4636 : decode runtimeBytecode ⟨4636⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨80, by decide⟩
theorem decode_4637 : decode runtimeBytecode ⟨4637⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨81, by decide⟩
theorem decode_4638 : decode runtimeBytecode ⟨4638⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨82, by decide⟩
theorem decode_4639 : decode runtimeBytecode ⟨4639⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨83, by decide⟩
theorem decode_4641 : decode runtimeBytecode ⟨4641⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨84, by decide⟩
theorem decode_4642 : decode runtimeBytecode ⟨4642⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨85, by decide⟩
theorem decode_4643 : decode runtimeBytecode ⟨4643⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨86, by decide⟩
theorem decode_4644 : decode runtimeBytecode ⟨4644⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨87, by decide⟩
theorem decode_4645 : decode runtimeBytecode ⟨4645⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨88, by decide⟩
theorem decode_4646 : decode runtimeBytecode ⟨4646⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨89, by decide⟩
theorem decode_4649 : decode runtimeBytecode ⟨4649⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨90, by decide⟩
theorem decode_4650 : decode runtimeBytecode ⟨4650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨91, by decide⟩
theorem decode_4651 : decode runtimeBytecode ⟨4651⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨92, by decide⟩
theorem decode_4652 : decode runtimeBytecode ⟨4652⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨93, by decide⟩
theorem decode_4653 : decode runtimeBytecode ⟨4653⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨94, by decide⟩
theorem decode_4654 : decode runtimeBytecode ⟨4654⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨95, by decide⟩
theorem decode_4655 : decode runtimeBytecode ⟨4655⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨96, by decide⟩
theorem decode_4656 : decode runtimeBytecode ⟨4656⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨97, by decide⟩
theorem decode_4657 : decode runtimeBytecode ⟨4657⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨98, by decide⟩
theorem decode_4658 : decode runtimeBytecode ⟨4658⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes32] using generatedDecodes32_correct ⟨99, by decide⟩

end Ripemd160Old
