import Examples.Ripemd160Old.DecodeGenerated.Chunk38

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes39 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5435⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5436⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5438⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5439⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5440⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5441⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5442⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5443⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5446⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5447⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5448⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5449⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5450⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5451⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5452⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5453⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5454⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5455⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5457⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5458⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5459⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5460⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5461⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5462⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5465⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5466⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5467⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5468⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5469⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5470⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5471⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5472⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5473⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5474⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5476⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5477⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5478⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5479⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5480⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5481⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5484⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5485⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5486⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5487⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5488⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5489⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5490⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5491⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5492⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5493⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨5495⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5496⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5497⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5498⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5499⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5500⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5503⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5504⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5505⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5506⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5507⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5508⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5509⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5510⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5511⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5512⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5514⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5515⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5516⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5517⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5518⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5519⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5522⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5523⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5524⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5525⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5526⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5527⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5528⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5529⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5530⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5531⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5533⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5534⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5535⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5536⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5537⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5538⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5541⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5542⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5543⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5544⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5545⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5546⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5547⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5548⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5549⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5550⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5552⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5553⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none))
]

private theorem generatedDecodes39_correct : ∀ i : Fin generatedDecodes39.size,
    decode runtimeBytecode generatedDecodes39[i].1 = generatedDecodes39[i].2 := by
  native_decide

theorem decode_5435 : decode runtimeBytecode ⟨5435⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨0, by decide⟩
theorem decode_5436 : decode runtimeBytecode ⟨5436⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨1, by decide⟩
theorem decode_5438 : decode runtimeBytecode ⟨5438⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨2, by decide⟩
theorem decode_5439 : decode runtimeBytecode ⟨5439⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨3, by decide⟩
theorem decode_5440 : decode runtimeBytecode ⟨5440⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨4, by decide⟩
theorem decode_5441 : decode runtimeBytecode ⟨5441⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨5, by decide⟩
theorem decode_5442 : decode runtimeBytecode ⟨5442⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨6, by decide⟩
theorem decode_5443 : decode runtimeBytecode ⟨5443⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨7, by decide⟩
theorem decode_5446 : decode runtimeBytecode ⟨5446⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨8, by decide⟩
theorem decode_5447 : decode runtimeBytecode ⟨5447⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨9, by decide⟩
theorem decode_5448 : decode runtimeBytecode ⟨5448⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨10, by decide⟩
theorem decode_5449 : decode runtimeBytecode ⟨5449⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨11, by decide⟩
theorem decode_5450 : decode runtimeBytecode ⟨5450⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨12, by decide⟩
theorem decode_5451 : decode runtimeBytecode ⟨5451⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨13, by decide⟩
theorem decode_5452 : decode runtimeBytecode ⟨5452⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨14, by decide⟩
theorem decode_5453 : decode runtimeBytecode ⟨5453⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨15, by decide⟩
theorem decode_5454 : decode runtimeBytecode ⟨5454⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨16, by decide⟩
theorem decode_5455 : decode runtimeBytecode ⟨5455⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨17, by decide⟩
theorem decode_5457 : decode runtimeBytecode ⟨5457⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨18, by decide⟩
theorem decode_5458 : decode runtimeBytecode ⟨5458⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨19, by decide⟩
theorem decode_5459 : decode runtimeBytecode ⟨5459⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨20, by decide⟩
theorem decode_5460 : decode runtimeBytecode ⟨5460⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨21, by decide⟩
theorem decode_5461 : decode runtimeBytecode ⟨5461⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨22, by decide⟩
theorem decode_5462 : decode runtimeBytecode ⟨5462⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨23, by decide⟩
theorem decode_5465 : decode runtimeBytecode ⟨5465⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨24, by decide⟩
theorem decode_5466 : decode runtimeBytecode ⟨5466⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨25, by decide⟩
theorem decode_5467 : decode runtimeBytecode ⟨5467⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨26, by decide⟩
theorem decode_5468 : decode runtimeBytecode ⟨5468⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨27, by decide⟩
theorem decode_5469 : decode runtimeBytecode ⟨5469⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨28, by decide⟩
theorem decode_5470 : decode runtimeBytecode ⟨5470⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨29, by decide⟩
theorem decode_5471 : decode runtimeBytecode ⟨5471⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨30, by decide⟩
theorem decode_5472 : decode runtimeBytecode ⟨5472⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨31, by decide⟩
theorem decode_5473 : decode runtimeBytecode ⟨5473⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨32, by decide⟩
theorem decode_5474 : decode runtimeBytecode ⟨5474⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨33, by decide⟩
theorem decode_5476 : decode runtimeBytecode ⟨5476⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨34, by decide⟩
theorem decode_5477 : decode runtimeBytecode ⟨5477⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨35, by decide⟩
theorem decode_5478 : decode runtimeBytecode ⟨5478⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨36, by decide⟩
theorem decode_5479 : decode runtimeBytecode ⟨5479⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨37, by decide⟩
theorem decode_5480 : decode runtimeBytecode ⟨5480⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨38, by decide⟩
theorem decode_5481 : decode runtimeBytecode ⟨5481⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨39, by decide⟩
theorem decode_5484 : decode runtimeBytecode ⟨5484⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨40, by decide⟩
theorem decode_5485 : decode runtimeBytecode ⟨5485⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨41, by decide⟩
theorem decode_5486 : decode runtimeBytecode ⟨5486⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨42, by decide⟩
theorem decode_5487 : decode runtimeBytecode ⟨5487⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨43, by decide⟩
theorem decode_5488 : decode runtimeBytecode ⟨5488⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨44, by decide⟩
theorem decode_5489 : decode runtimeBytecode ⟨5489⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨45, by decide⟩
theorem decode_5490 : decode runtimeBytecode ⟨5490⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨46, by decide⟩
theorem decode_5491 : decode runtimeBytecode ⟨5491⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨47, by decide⟩
theorem decode_5492 : decode runtimeBytecode ⟨5492⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨48, by decide⟩
theorem decode_5493 : decode runtimeBytecode ⟨5493⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨49, by decide⟩
theorem decode_5495 : decode runtimeBytecode ⟨5495⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨50, by decide⟩
theorem decode_5496 : decode runtimeBytecode ⟨5496⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨51, by decide⟩
theorem decode_5497 : decode runtimeBytecode ⟨5497⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨52, by decide⟩
theorem decode_5498 : decode runtimeBytecode ⟨5498⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨53, by decide⟩
theorem decode_5499 : decode runtimeBytecode ⟨5499⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨54, by decide⟩
theorem decode_5500 : decode runtimeBytecode ⟨5500⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨55, by decide⟩
theorem decode_5503 : decode runtimeBytecode ⟨5503⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨56, by decide⟩
theorem decode_5504 : decode runtimeBytecode ⟨5504⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨57, by decide⟩
theorem decode_5505 : decode runtimeBytecode ⟨5505⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨58, by decide⟩
theorem decode_5506 : decode runtimeBytecode ⟨5506⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨59, by decide⟩
theorem decode_5507 : decode runtimeBytecode ⟨5507⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨60, by decide⟩
theorem decode_5508 : decode runtimeBytecode ⟨5508⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨61, by decide⟩
theorem decode_5509 : decode runtimeBytecode ⟨5509⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨62, by decide⟩
theorem decode_5510 : decode runtimeBytecode ⟨5510⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨63, by decide⟩
theorem decode_5511 : decode runtimeBytecode ⟨5511⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨64, by decide⟩
theorem decode_5512 : decode runtimeBytecode ⟨5512⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨65, by decide⟩
theorem decode_5514 : decode runtimeBytecode ⟨5514⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨66, by decide⟩
theorem decode_5515 : decode runtimeBytecode ⟨5515⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨67, by decide⟩
theorem decode_5516 : decode runtimeBytecode ⟨5516⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨68, by decide⟩
theorem decode_5517 : decode runtimeBytecode ⟨5517⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨69, by decide⟩
theorem decode_5518 : decode runtimeBytecode ⟨5518⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨70, by decide⟩
theorem decode_5519 : decode runtimeBytecode ⟨5519⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨71, by decide⟩
theorem decode_5522 : decode runtimeBytecode ⟨5522⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨72, by decide⟩
theorem decode_5523 : decode runtimeBytecode ⟨5523⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨73, by decide⟩
theorem decode_5524 : decode runtimeBytecode ⟨5524⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨74, by decide⟩
theorem decode_5525 : decode runtimeBytecode ⟨5525⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨75, by decide⟩
theorem decode_5526 : decode runtimeBytecode ⟨5526⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨76, by decide⟩
theorem decode_5527 : decode runtimeBytecode ⟨5527⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨77, by decide⟩
theorem decode_5528 : decode runtimeBytecode ⟨5528⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨78, by decide⟩
theorem decode_5529 : decode runtimeBytecode ⟨5529⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨79, by decide⟩
theorem decode_5530 : decode runtimeBytecode ⟨5530⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨80, by decide⟩
theorem decode_5531 : decode runtimeBytecode ⟨5531⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨81, by decide⟩
theorem decode_5533 : decode runtimeBytecode ⟨5533⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨82, by decide⟩
theorem decode_5534 : decode runtimeBytecode ⟨5534⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨83, by decide⟩
theorem decode_5535 : decode runtimeBytecode ⟨5535⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨84, by decide⟩
theorem decode_5536 : decode runtimeBytecode ⟨5536⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨85, by decide⟩
theorem decode_5537 : decode runtimeBytecode ⟨5537⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨86, by decide⟩
theorem decode_5538 : decode runtimeBytecode ⟨5538⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨87, by decide⟩
theorem decode_5541 : decode runtimeBytecode ⟨5541⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨88, by decide⟩
theorem decode_5542 : decode runtimeBytecode ⟨5542⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨89, by decide⟩
theorem decode_5543 : decode runtimeBytecode ⟨5543⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨90, by decide⟩
theorem decode_5544 : decode runtimeBytecode ⟨5544⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨91, by decide⟩
theorem decode_5545 : decode runtimeBytecode ⟨5545⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨92, by decide⟩
theorem decode_5546 : decode runtimeBytecode ⟨5546⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨93, by decide⟩
theorem decode_5547 : decode runtimeBytecode ⟨5547⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨94, by decide⟩
theorem decode_5548 : decode runtimeBytecode ⟨5548⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨95, by decide⟩
theorem decode_5549 : decode runtimeBytecode ⟨5549⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨96, by decide⟩
theorem decode_5550 : decode runtimeBytecode ⟨5550⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨97, by decide⟩
theorem decode_5552 : decode runtimeBytecode ⟨5552⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨98, by decide⟩
theorem decode_5553 : decode runtimeBytecode ⟨5553⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes39] using generatedDecodes39_correct ⟨99, by decide⟩

end Ripemd160Old
