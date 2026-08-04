import Examples.Ripemd160Old.DecodeGenerated.Chunk00

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes1 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨387⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4010⟩, 2))),
  (⟨390⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨391⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨392⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨393⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨394⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨396⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨397⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨398⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4001⟩, 2))),
  (⟨401⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨402⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨403⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨405⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨406⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨407⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨409⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨410⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none)),
  (⟨411⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨412⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3693⟩, 2))),
  (⟨415⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨416⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨417⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨48⟩, 1))),
  (⟨419⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨420⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨421⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨31⟩, 1))),
  (⟨423⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨424⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none)),
  (⟨425⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨426⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3385⟩, 2))),
  (⟨429⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨430⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨431⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨433⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨434⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨435⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨47⟩, 1))),
  (⟨437⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨438⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none)),
  (⟨439⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨440⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3077⟩, 2))),
  (⟨443⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨444⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨445⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1))),
  (⟨447⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨448⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none)),
  (⟨449⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2769⟩, 2))),
  (⟨452⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨453⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨454⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨455⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none)),
  (⟨456⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨457⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨458⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨459⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2323⟩, 2))),
  (⟨462⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨463⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨464⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨466⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨467⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1877⟩, 2))),
  (⟨470⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨471⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨472⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨474⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨475⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1431⟩, 2))),
  (⟨478⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨479⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨480⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨482⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨483⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨985⟩, 2))),
  (⟨486⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨487⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨489⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨490⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨540⟩, 2))),
  (⟨493⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨494⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨495⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨496⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨498⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨499⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨500⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨501⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨502⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨503⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨504⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨505⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨506⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨507⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2))),
  (⟨510⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨511⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨512⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨513⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨514⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨515⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨516⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨517⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨519⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨520⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨521⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨522⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2))),
  (⟨525⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨526⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none))
]

private theorem generatedDecodes1_correct : ∀ i : Fin generatedDecodes1.size,
    decode runtimeBytecode generatedDecodes1[i].1 = generatedDecodes1[i].2 := by
  native_decide

theorem decode_387 : decode runtimeBytecode ⟨387⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4010⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨0, by decide⟩
theorem decode_390 : decode runtimeBytecode ⟨390⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨1, by decide⟩
theorem decode_391 : decode runtimeBytecode ⟨391⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨2, by decide⟩
theorem decode_392 : decode runtimeBytecode ⟨392⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨3, by decide⟩
theorem decode_393 : decode runtimeBytecode ⟨393⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨4, by decide⟩
theorem decode_394 : decode runtimeBytecode ⟨394⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨5, by decide⟩
theorem decode_396 : decode runtimeBytecode ⟨396⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨6, by decide⟩
theorem decode_397 : decode runtimeBytecode ⟨397⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨7, by decide⟩
theorem decode_398 : decode runtimeBytecode ⟨398⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4001⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨8, by decide⟩
theorem decode_401 : decode runtimeBytecode ⟨401⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨9, by decide⟩
theorem decode_402 : decode runtimeBytecode ⟨402⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨10, by decide⟩
theorem decode_403 : decode runtimeBytecode ⟨403⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨11, by decide⟩
theorem decode_405 : decode runtimeBytecode ⟨405⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨12, by decide⟩
theorem decode_406 : decode runtimeBytecode ⟨406⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨13, by decide⟩
theorem decode_407 : decode runtimeBytecode ⟨407⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨14, by decide⟩
theorem decode_409 : decode runtimeBytecode ⟨409⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨15, by decide⟩
theorem decode_410 : decode runtimeBytecode ⟨410⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨16, by decide⟩
theorem decode_411 : decode runtimeBytecode ⟨411⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨17, by decide⟩
theorem decode_412 : decode runtimeBytecode ⟨412⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3693⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨18, by decide⟩
theorem decode_415 : decode runtimeBytecode ⟨415⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨19, by decide⟩
theorem decode_416 : decode runtimeBytecode ⟨416⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨20, by decide⟩
theorem decode_417 : decode runtimeBytecode ⟨417⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨48⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨21, by decide⟩
theorem decode_419 : decode runtimeBytecode ⟨419⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨22, by decide⟩
theorem decode_420 : decode runtimeBytecode ⟨420⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨23, by decide⟩
theorem decode_421 : decode runtimeBytecode ⟨421⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨31⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨24, by decide⟩
theorem decode_423 : decode runtimeBytecode ⟨423⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨25, by decide⟩
theorem decode_424 : decode runtimeBytecode ⟨424⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨26, by decide⟩
theorem decode_425 : decode runtimeBytecode ⟨425⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨27, by decide⟩
theorem decode_426 : decode runtimeBytecode ⟨426⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3385⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨28, by decide⟩
theorem decode_429 : decode runtimeBytecode ⟨429⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨29, by decide⟩
theorem decode_430 : decode runtimeBytecode ⟨430⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨30, by decide⟩
theorem decode_431 : decode runtimeBytecode ⟨431⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨31, by decide⟩
theorem decode_433 : decode runtimeBytecode ⟨433⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨32, by decide⟩
theorem decode_434 : decode runtimeBytecode ⟨434⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨33, by decide⟩
theorem decode_435 : decode runtimeBytecode ⟨435⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨47⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨34, by decide⟩
theorem decode_437 : decode runtimeBytecode ⟨437⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨35, by decide⟩
theorem decode_438 : decode runtimeBytecode ⟨438⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨36, by decide⟩
theorem decode_439 : decode runtimeBytecode ⟨439⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨37, by decide⟩
theorem decode_440 : decode runtimeBytecode ⟨440⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3077⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨38, by decide⟩
theorem decode_443 : decode runtimeBytecode ⟨443⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨39, by decide⟩
theorem decode_444 : decode runtimeBytecode ⟨444⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨40, by decide⟩
theorem decode_445 : decode runtimeBytecode ⟨445⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨63⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨41, by decide⟩
theorem decode_447 : decode runtimeBytecode ⟨447⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨42, by decide⟩
theorem decode_448 : decode runtimeBytecode ⟨448⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.GT), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨43, by decide⟩
theorem decode_449 : decode runtimeBytecode ⟨449⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2769⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨44, by decide⟩
theorem decode_452 : decode runtimeBytecode ⟨452⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨45, by decide⟩
theorem decode_453 : decode runtimeBytecode ⟨453⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨46, by decide⟩
theorem decode_454 : decode runtimeBytecode ⟨454⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨47, by decide⟩
theorem decode_455 : decode runtimeBytecode ⟨455⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨48, by decide⟩
theorem decode_456 : decode runtimeBytecode ⟨456⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨49, by decide⟩
theorem decode_457 : decode runtimeBytecode ⟨457⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨50, by decide⟩
theorem decode_458 : decode runtimeBytecode ⟨458⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨51, by decide⟩
theorem decode_459 : decode runtimeBytecode ⟨459⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2323⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨52, by decide⟩
theorem decode_462 : decode runtimeBytecode ⟨462⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨53, by decide⟩
theorem decode_463 : decode runtimeBytecode ⟨463⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨54, by decide⟩
theorem decode_464 : decode runtimeBytecode ⟨464⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨55, by decide⟩
theorem decode_466 : decode runtimeBytecode ⟨466⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨56, by decide⟩
theorem decode_467 : decode runtimeBytecode ⟨467⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1877⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨57, by decide⟩
theorem decode_470 : decode runtimeBytecode ⟨470⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨58, by decide⟩
theorem decode_471 : decode runtimeBytecode ⟨471⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨59, by decide⟩
theorem decode_472 : decode runtimeBytecode ⟨472⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨60, by decide⟩
theorem decode_474 : decode runtimeBytecode ⟨474⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨61, by decide⟩
theorem decode_475 : decode runtimeBytecode ⟨475⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1431⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨62, by decide⟩
theorem decode_478 : decode runtimeBytecode ⟨478⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨63, by decide⟩
theorem decode_479 : decode runtimeBytecode ⟨479⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨64, by decide⟩
theorem decode_480 : decode runtimeBytecode ⟨480⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨65, by decide⟩
theorem decode_482 : decode runtimeBytecode ⟨482⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨66, by decide⟩
theorem decode_483 : decode runtimeBytecode ⟨483⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨985⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨67, by decide⟩
theorem decode_486 : decode runtimeBytecode ⟨486⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨68, by decide⟩
theorem decode_487 : decode runtimeBytecode ⟨487⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨69, by decide⟩
theorem decode_489 : decode runtimeBytecode ⟨489⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨70, by decide⟩
theorem decode_490 : decode runtimeBytecode ⟨490⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨540⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨71, by decide⟩
theorem decode_493 : decode runtimeBytecode ⟨493⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨72, by decide⟩
theorem decode_494 : decode runtimeBytecode ⟨494⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨73, by decide⟩
theorem decode_495 : decode runtimeBytecode ⟨495⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨74, by decide⟩
theorem decode_496 : decode runtimeBytecode ⟨496⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨75, by decide⟩
theorem decode_498 : decode runtimeBytecode ⟨498⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨76, by decide⟩
theorem decode_499 : decode runtimeBytecode ⟨499⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨77, by decide⟩
theorem decode_500 : decode runtimeBytecode ⟨500⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨78, by decide⟩
theorem decode_501 : decode runtimeBytecode ⟨501⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨79, by decide⟩
theorem decode_502 : decode runtimeBytecode ⟨502⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨80, by decide⟩
theorem decode_503 : decode runtimeBytecode ⟨503⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨81, by decide⟩
theorem decode_504 : decode runtimeBytecode ⟨504⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨82, by decide⟩
theorem decode_505 : decode runtimeBytecode ⟨505⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨83, by decide⟩
theorem decode_506 : decode runtimeBytecode ⟨506⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨84, by decide⟩
theorem decode_507 : decode runtimeBytecode ⟨507⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨85, by decide⟩
theorem decode_510 : decode runtimeBytecode ⟨510⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨86, by decide⟩
theorem decode_511 : decode runtimeBytecode ⟨511⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨87, by decide⟩
theorem decode_512 : decode runtimeBytecode ⟨512⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨88, by decide⟩
theorem decode_513 : decode runtimeBytecode ⟨513⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨89, by decide⟩
theorem decode_514 : decode runtimeBytecode ⟨514⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨90, by decide⟩
theorem decode_515 : decode runtimeBytecode ⟨515⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨91, by decide⟩
theorem decode_516 : decode runtimeBytecode ⟨516⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨92, by decide⟩
theorem decode_517 : decode runtimeBytecode ⟨517⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨93, by decide⟩
theorem decode_519 : decode runtimeBytecode ⟨519⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨94, by decide⟩
theorem decode_520 : decode runtimeBytecode ⟨520⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨95, by decide⟩
theorem decode_521 : decode runtimeBytecode ⟨521⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨96, by decide⟩
theorem decode_522 : decode runtimeBytecode ⟨522⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2)) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨97, by decide⟩
theorem decode_525 : decode runtimeBytecode ⟨525⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨98, by decide⟩
theorem decode_526 : decode runtimeBytecode ⟨526⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes1] using generatedDecodes1_correct ⟨99, by decide⟩

end Ripemd160Old
