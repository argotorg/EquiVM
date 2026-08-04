import Examples.Ripemd160Old.DecodeGenerated.Chunk37

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes38 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5295⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5296⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5297⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨5299⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5300⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5580⟩, 2))),
  (⟨5303⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5304⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5305⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5307⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5308⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5561⟩, 2))),
  (⟨5311⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5312⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5313⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5315⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5316⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5542⟩, 2))),
  (⟨5319⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5320⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5321⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨5323⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5324⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5523⟩, 2))),
  (⟨5327⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5328⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5329⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨5331⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5332⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5504⟩, 2))),
  (⟨5335⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5336⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5337⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨5338⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5339⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5485⟩, 2))),
  (⟨5342⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5343⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5344⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5346⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5347⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5466⟩, 2))),
  (⟨5350⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5351⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5352⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5354⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5355⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5447⟩, 2))),
  (⟨5358⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5359⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5360⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5362⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5363⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5428⟩, 2))),
  (⟨5366⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5367⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5368⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5370⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5371⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5409⟩, 2))),
  (⟨5374⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5375⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨5377⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5378⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5391⟩, 2))),
  (⟨5381⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5382⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5383⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5384⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5385⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5386⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨5387⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2))),
  (⟨5390⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5391⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5392⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5393⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5394⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5395⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5396⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5397⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5398⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨5400⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5401⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5402⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5403⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5404⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5405⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5408⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5409⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5410⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5411⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5412⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5413⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5414⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5415⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5416⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5417⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5419⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5420⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5421⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5422⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5423⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5424⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2))),
  (⟨5427⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5428⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5429⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5430⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5431⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5432⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5433⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5434⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none))
]

private theorem generatedDecodes38_correct : ∀ i : Fin generatedDecodes38.size,
    decode runtimeBytecode generatedDecodes38[i].1 = generatedDecodes38[i].2 := by
  native_decide

theorem decode_5295 : decode runtimeBytecode ⟨5295⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨0, by decide⟩
theorem decode_5296 : decode runtimeBytecode ⟨5296⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨1, by decide⟩
theorem decode_5297 : decode runtimeBytecode ⟨5297⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨2, by decide⟩
theorem decode_5299 : decode runtimeBytecode ⟨5299⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨3, by decide⟩
theorem decode_5300 : decode runtimeBytecode ⟨5300⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5580⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨4, by decide⟩
theorem decode_5303 : decode runtimeBytecode ⟨5303⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨5, by decide⟩
theorem decode_5304 : decode runtimeBytecode ⟨5304⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨6, by decide⟩
theorem decode_5305 : decode runtimeBytecode ⟨5305⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨7, by decide⟩
theorem decode_5307 : decode runtimeBytecode ⟨5307⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨8, by decide⟩
theorem decode_5308 : decode runtimeBytecode ⟨5308⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5561⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨9, by decide⟩
theorem decode_5311 : decode runtimeBytecode ⟨5311⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨10, by decide⟩
theorem decode_5312 : decode runtimeBytecode ⟨5312⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨11, by decide⟩
theorem decode_5313 : decode runtimeBytecode ⟨5313⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨12, by decide⟩
theorem decode_5315 : decode runtimeBytecode ⟨5315⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨13, by decide⟩
theorem decode_5316 : decode runtimeBytecode ⟨5316⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5542⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨14, by decide⟩
theorem decode_5319 : decode runtimeBytecode ⟨5319⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨15, by decide⟩
theorem decode_5320 : decode runtimeBytecode ⟨5320⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨16, by decide⟩
theorem decode_5321 : decode runtimeBytecode ⟨5321⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨17, by decide⟩
theorem decode_5323 : decode runtimeBytecode ⟨5323⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨18, by decide⟩
theorem decode_5324 : decode runtimeBytecode ⟨5324⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5523⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨19, by decide⟩
theorem decode_5327 : decode runtimeBytecode ⟨5327⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨20, by decide⟩
theorem decode_5328 : decode runtimeBytecode ⟨5328⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨21, by decide⟩
theorem decode_5329 : decode runtimeBytecode ⟨5329⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨22, by decide⟩
theorem decode_5331 : decode runtimeBytecode ⟨5331⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨23, by decide⟩
theorem decode_5332 : decode runtimeBytecode ⟨5332⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5504⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨24, by decide⟩
theorem decode_5335 : decode runtimeBytecode ⟨5335⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨25, by decide⟩
theorem decode_5336 : decode runtimeBytecode ⟨5336⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨26, by decide⟩
theorem decode_5337 : decode runtimeBytecode ⟨5337⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨27, by decide⟩
theorem decode_5338 : decode runtimeBytecode ⟨5338⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨28, by decide⟩
theorem decode_5339 : decode runtimeBytecode ⟨5339⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5485⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨29, by decide⟩
theorem decode_5342 : decode runtimeBytecode ⟨5342⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨30, by decide⟩
theorem decode_5343 : decode runtimeBytecode ⟨5343⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨31, by decide⟩
theorem decode_5344 : decode runtimeBytecode ⟨5344⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨32, by decide⟩
theorem decode_5346 : decode runtimeBytecode ⟨5346⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨33, by decide⟩
theorem decode_5347 : decode runtimeBytecode ⟨5347⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5466⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨34, by decide⟩
theorem decode_5350 : decode runtimeBytecode ⟨5350⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨35, by decide⟩
theorem decode_5351 : decode runtimeBytecode ⟨5351⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨36, by decide⟩
theorem decode_5352 : decode runtimeBytecode ⟨5352⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨37, by decide⟩
theorem decode_5354 : decode runtimeBytecode ⟨5354⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨38, by decide⟩
theorem decode_5355 : decode runtimeBytecode ⟨5355⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5447⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨39, by decide⟩
theorem decode_5358 : decode runtimeBytecode ⟨5358⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨40, by decide⟩
theorem decode_5359 : decode runtimeBytecode ⟨5359⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨41, by decide⟩
theorem decode_5360 : decode runtimeBytecode ⟨5360⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨42, by decide⟩
theorem decode_5362 : decode runtimeBytecode ⟨5362⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨43, by decide⟩
theorem decode_5363 : decode runtimeBytecode ⟨5363⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5428⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨44, by decide⟩
theorem decode_5366 : decode runtimeBytecode ⟨5366⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨45, by decide⟩
theorem decode_5367 : decode runtimeBytecode ⟨5367⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨46, by decide⟩
theorem decode_5368 : decode runtimeBytecode ⟨5368⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨47, by decide⟩
theorem decode_5370 : decode runtimeBytecode ⟨5370⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨48, by decide⟩
theorem decode_5371 : decode runtimeBytecode ⟨5371⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5409⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨49, by decide⟩
theorem decode_5374 : decode runtimeBytecode ⟨5374⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨50, by decide⟩
theorem decode_5375 : decode runtimeBytecode ⟨5375⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨51, by decide⟩
theorem decode_5377 : decode runtimeBytecode ⟨5377⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨52, by decide⟩
theorem decode_5378 : decode runtimeBytecode ⟨5378⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5391⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨53, by decide⟩
theorem decode_5381 : decode runtimeBytecode ⟨5381⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨54, by decide⟩
theorem decode_5382 : decode runtimeBytecode ⟨5382⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨55, by decide⟩
theorem decode_5383 : decode runtimeBytecode ⟨5383⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨56, by decide⟩
theorem decode_5384 : decode runtimeBytecode ⟨5384⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨57, by decide⟩
theorem decode_5385 : decode runtimeBytecode ⟨5385⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨58, by decide⟩
theorem decode_5386 : decode runtimeBytecode ⟨5386⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨59, by decide⟩
theorem decode_5387 : decode runtimeBytecode ⟨5387⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨60, by decide⟩
theorem decode_5390 : decode runtimeBytecode ⟨5390⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨61, by decide⟩
theorem decode_5391 : decode runtimeBytecode ⟨5391⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨62, by decide⟩
theorem decode_5392 : decode runtimeBytecode ⟨5392⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨63, by decide⟩
theorem decode_5393 : decode runtimeBytecode ⟨5393⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨64, by decide⟩
theorem decode_5394 : decode runtimeBytecode ⟨5394⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨65, by decide⟩
theorem decode_5395 : decode runtimeBytecode ⟨5395⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨66, by decide⟩
theorem decode_5396 : decode runtimeBytecode ⟨5396⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨67, by decide⟩
theorem decode_5397 : decode runtimeBytecode ⟨5397⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨68, by decide⟩
theorem decode_5398 : decode runtimeBytecode ⟨5398⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨69, by decide⟩
theorem decode_5400 : decode runtimeBytecode ⟨5400⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨70, by decide⟩
theorem decode_5401 : decode runtimeBytecode ⟨5401⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨71, by decide⟩
theorem decode_5402 : decode runtimeBytecode ⟨5402⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨72, by decide⟩
theorem decode_5403 : decode runtimeBytecode ⟨5403⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨73, by decide⟩
theorem decode_5404 : decode runtimeBytecode ⟨5404⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨74, by decide⟩
theorem decode_5405 : decode runtimeBytecode ⟨5405⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨75, by decide⟩
theorem decode_5408 : decode runtimeBytecode ⟨5408⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨76, by decide⟩
theorem decode_5409 : decode runtimeBytecode ⟨5409⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨77, by decide⟩
theorem decode_5410 : decode runtimeBytecode ⟨5410⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨78, by decide⟩
theorem decode_5411 : decode runtimeBytecode ⟨5411⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨79, by decide⟩
theorem decode_5412 : decode runtimeBytecode ⟨5412⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨80, by decide⟩
theorem decode_5413 : decode runtimeBytecode ⟨5413⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨81, by decide⟩
theorem decode_5414 : decode runtimeBytecode ⟨5414⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨82, by decide⟩
theorem decode_5415 : decode runtimeBytecode ⟨5415⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨83, by decide⟩
theorem decode_5416 : decode runtimeBytecode ⟨5416⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨84, by decide⟩
theorem decode_5417 : decode runtimeBytecode ⟨5417⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨85, by decide⟩
theorem decode_5419 : decode runtimeBytecode ⟨5419⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨86, by decide⟩
theorem decode_5420 : decode runtimeBytecode ⟨5420⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨87, by decide⟩
theorem decode_5421 : decode runtimeBytecode ⟨5421⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨88, by decide⟩
theorem decode_5422 : decode runtimeBytecode ⟨5422⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨89, by decide⟩
theorem decode_5423 : decode runtimeBytecode ⟨5423⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨90, by decide⟩
theorem decode_5424 : decode runtimeBytecode ⟨5424⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5382⟩, 2)) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨91, by decide⟩
theorem decode_5427 : decode runtimeBytecode ⟨5427⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨92, by decide⟩
theorem decode_5428 : decode runtimeBytecode ⟨5428⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨93, by decide⟩
theorem decode_5429 : decode runtimeBytecode ⟨5429⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨94, by decide⟩
theorem decode_5430 : decode runtimeBytecode ⟨5430⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨95, by decide⟩
theorem decode_5431 : decode runtimeBytecode ⟨5431⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨96, by decide⟩
theorem decode_5432 : decode runtimeBytecode ⟨5432⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨97, by decide⟩
theorem decode_5433 : decode runtimeBytecode ⟨5433⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨98, by decide⟩
theorem decode_5434 : decode runtimeBytecode ⟨5434⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes38] using generatedDecodes38_correct ⟨99, by decide⟩

end Ripemd160Old
