import Examples.Ripemd160Old.DecodeGenerated.Chunk39

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes40 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5554⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5555⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5556⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5557⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5560⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5561⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5562⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5563⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5564⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5565⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5566⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5567⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5568⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5569⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5571⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5572⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5573⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5575⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5576⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5579⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5580⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5581⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5582⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5583⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5584⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5585⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5586⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5587⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5588⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5590⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5591⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5592⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5593⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5594⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5595⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5598⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5599⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5600⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5601⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5602⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5603⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5604⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5605⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5606⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5607⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨5609⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5610⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5611⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5612⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5613⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5614⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5617⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5618⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5619⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5620⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5621⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5622⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5623⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5624⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5625⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5626⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5628⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5629⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5630⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5631⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5632⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5633⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5636⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5637⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5638⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5639⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5640⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5641⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5642⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5643⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5644⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5645⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨5647⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5648⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5649⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5651⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5652⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5655⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5656⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5657⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5658⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5659⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5660⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5661⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5662⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5663⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5664⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5666⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5667⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5668⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5670⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5671⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)))
]

private theorem generatedDecodes40_correct : ∀ i : Fin generatedDecodes40.size,
    decode runtimeBytecode generatedDecodes40[i].1 = generatedDecodes40[i].2 := by
  native_decide

theorem decode_5554 : decode runtimeBytecode ⟨5554⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨0, by decide⟩
theorem decode_5555 : decode runtimeBytecode ⟨5555⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨1, by decide⟩
theorem decode_5556 : decode runtimeBytecode ⟨5556⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨2, by decide⟩
theorem decode_5557 : decode runtimeBytecode ⟨5557⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨3, by decide⟩
theorem decode_5560 : decode runtimeBytecode ⟨5560⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨4, by decide⟩
theorem decode_5561 : decode runtimeBytecode ⟨5561⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨5, by decide⟩
theorem decode_5562 : decode runtimeBytecode ⟨5562⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨6, by decide⟩
theorem decode_5563 : decode runtimeBytecode ⟨5563⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨7, by decide⟩
theorem decode_5564 : decode runtimeBytecode ⟨5564⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨8, by decide⟩
theorem decode_5565 : decode runtimeBytecode ⟨5565⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨9, by decide⟩
theorem decode_5566 : decode runtimeBytecode ⟨5566⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨10, by decide⟩
theorem decode_5567 : decode runtimeBytecode ⟨5567⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨11, by decide⟩
theorem decode_5568 : decode runtimeBytecode ⟨5568⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨12, by decide⟩
theorem decode_5569 : decode runtimeBytecode ⟨5569⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨13, by decide⟩
theorem decode_5571 : decode runtimeBytecode ⟨5571⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨14, by decide⟩
theorem decode_5572 : decode runtimeBytecode ⟨5572⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨15, by decide⟩
theorem decode_5573 : decode runtimeBytecode ⟨5573⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨16, by decide⟩
theorem decode_5574 : decode runtimeBytecode ⟨5574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨17, by decide⟩
theorem decode_5575 : decode runtimeBytecode ⟨5575⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨18, by decide⟩
theorem decode_5576 : decode runtimeBytecode ⟨5576⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨19, by decide⟩
theorem decode_5579 : decode runtimeBytecode ⟨5579⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨20, by decide⟩
theorem decode_5580 : decode runtimeBytecode ⟨5580⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨21, by decide⟩
theorem decode_5581 : decode runtimeBytecode ⟨5581⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨22, by decide⟩
theorem decode_5582 : decode runtimeBytecode ⟨5582⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨23, by decide⟩
theorem decode_5583 : decode runtimeBytecode ⟨5583⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨24, by decide⟩
theorem decode_5584 : decode runtimeBytecode ⟨5584⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨25, by decide⟩
theorem decode_5585 : decode runtimeBytecode ⟨5585⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨26, by decide⟩
theorem decode_5586 : decode runtimeBytecode ⟨5586⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨27, by decide⟩
theorem decode_5587 : decode runtimeBytecode ⟨5587⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨28, by decide⟩
theorem decode_5588 : decode runtimeBytecode ⟨5588⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨29, by decide⟩
theorem decode_5590 : decode runtimeBytecode ⟨5590⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨30, by decide⟩
theorem decode_5591 : decode runtimeBytecode ⟨5591⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨31, by decide⟩
theorem decode_5592 : decode runtimeBytecode ⟨5592⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨32, by decide⟩
theorem decode_5593 : decode runtimeBytecode ⟨5593⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨33, by decide⟩
theorem decode_5594 : decode runtimeBytecode ⟨5594⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨34, by decide⟩
theorem decode_5595 : decode runtimeBytecode ⟨5595⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨35, by decide⟩
theorem decode_5598 : decode runtimeBytecode ⟨5598⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨36, by decide⟩
theorem decode_5599 : decode runtimeBytecode ⟨5599⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨37, by decide⟩
theorem decode_5600 : decode runtimeBytecode ⟨5600⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨38, by decide⟩
theorem decode_5601 : decode runtimeBytecode ⟨5601⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨39, by decide⟩
theorem decode_5602 : decode runtimeBytecode ⟨5602⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨40, by decide⟩
theorem decode_5603 : decode runtimeBytecode ⟨5603⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨41, by decide⟩
theorem decode_5604 : decode runtimeBytecode ⟨5604⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨42, by decide⟩
theorem decode_5605 : decode runtimeBytecode ⟨5605⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨43, by decide⟩
theorem decode_5606 : decode runtimeBytecode ⟨5606⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨44, by decide⟩
theorem decode_5607 : decode runtimeBytecode ⟨5607⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨45, by decide⟩
theorem decode_5609 : decode runtimeBytecode ⟨5609⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨46, by decide⟩
theorem decode_5610 : decode runtimeBytecode ⟨5610⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨47, by decide⟩
theorem decode_5611 : decode runtimeBytecode ⟨5611⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨48, by decide⟩
theorem decode_5612 : decode runtimeBytecode ⟨5612⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨49, by decide⟩
theorem decode_5613 : decode runtimeBytecode ⟨5613⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨50, by decide⟩
theorem decode_5614 : decode runtimeBytecode ⟨5614⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨51, by decide⟩
theorem decode_5617 : decode runtimeBytecode ⟨5617⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨52, by decide⟩
theorem decode_5618 : decode runtimeBytecode ⟨5618⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨53, by decide⟩
theorem decode_5619 : decode runtimeBytecode ⟨5619⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨54, by decide⟩
theorem decode_5620 : decode runtimeBytecode ⟨5620⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨55, by decide⟩
theorem decode_5621 : decode runtimeBytecode ⟨5621⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨56, by decide⟩
theorem decode_5622 : decode runtimeBytecode ⟨5622⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨57, by decide⟩
theorem decode_5623 : decode runtimeBytecode ⟨5623⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨58, by decide⟩
theorem decode_5624 : decode runtimeBytecode ⟨5624⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨59, by decide⟩
theorem decode_5625 : decode runtimeBytecode ⟨5625⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨60, by decide⟩
theorem decode_5626 : decode runtimeBytecode ⟨5626⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨61, by decide⟩
theorem decode_5628 : decode runtimeBytecode ⟨5628⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨62, by decide⟩
theorem decode_5629 : decode runtimeBytecode ⟨5629⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨63, by decide⟩
theorem decode_5630 : decode runtimeBytecode ⟨5630⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨64, by decide⟩
theorem decode_5631 : decode runtimeBytecode ⟨5631⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨65, by decide⟩
theorem decode_5632 : decode runtimeBytecode ⟨5632⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨66, by decide⟩
theorem decode_5633 : decode runtimeBytecode ⟨5633⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨67, by decide⟩
theorem decode_5636 : decode runtimeBytecode ⟨5636⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨68, by decide⟩
theorem decode_5637 : decode runtimeBytecode ⟨5637⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨69, by decide⟩
theorem decode_5638 : decode runtimeBytecode ⟨5638⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨70, by decide⟩
theorem decode_5639 : decode runtimeBytecode ⟨5639⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨71, by decide⟩
theorem decode_5640 : decode runtimeBytecode ⟨5640⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨72, by decide⟩
theorem decode_5641 : decode runtimeBytecode ⟨5641⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨73, by decide⟩
theorem decode_5642 : decode runtimeBytecode ⟨5642⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨74, by decide⟩
theorem decode_5643 : decode runtimeBytecode ⟨5643⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨75, by decide⟩
theorem decode_5644 : decode runtimeBytecode ⟨5644⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨76, by decide⟩
theorem decode_5645 : decode runtimeBytecode ⟨5645⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨77, by decide⟩
theorem decode_5647 : decode runtimeBytecode ⟨5647⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨78, by decide⟩
theorem decode_5648 : decode runtimeBytecode ⟨5648⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨79, by decide⟩
theorem decode_5649 : decode runtimeBytecode ⟨5649⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨80, by decide⟩
theorem decode_5650 : decode runtimeBytecode ⟨5650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨81, by decide⟩
theorem decode_5651 : decode runtimeBytecode ⟨5651⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨82, by decide⟩
theorem decode_5652 : decode runtimeBytecode ⟨5652⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨83, by decide⟩
theorem decode_5655 : decode runtimeBytecode ⟨5655⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨84, by decide⟩
theorem decode_5656 : decode runtimeBytecode ⟨5656⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨85, by decide⟩
theorem decode_5657 : decode runtimeBytecode ⟨5657⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨86, by decide⟩
theorem decode_5658 : decode runtimeBytecode ⟨5658⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨87, by decide⟩
theorem decode_5659 : decode runtimeBytecode ⟨5659⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨88, by decide⟩
theorem decode_5660 : decode runtimeBytecode ⟨5660⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨89, by decide⟩
theorem decode_5661 : decode runtimeBytecode ⟨5661⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨90, by decide⟩
theorem decode_5662 : decode runtimeBytecode ⟨5662⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨91, by decide⟩
theorem decode_5663 : decode runtimeBytecode ⟨5663⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨92, by decide⟩
theorem decode_5664 : decode runtimeBytecode ⟨5664⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨93, by decide⟩
theorem decode_5666 : decode runtimeBytecode ⟨5666⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨94, by decide⟩
theorem decode_5667 : decode runtimeBytecode ⟨5667⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨95, by decide⟩
theorem decode_5668 : decode runtimeBytecode ⟨5668⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨96, by decide⟩
theorem decode_5669 : decode runtimeBytecode ⟨5669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨97, by decide⟩
theorem decode_5670 : decode runtimeBytecode ⟨5670⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨98, by decide⟩
theorem decode_5671 : decode runtimeBytecode ⟨5671⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes40] using generatedDecodes40_correct ⟨99, by decide⟩

end Ripemd160Old
