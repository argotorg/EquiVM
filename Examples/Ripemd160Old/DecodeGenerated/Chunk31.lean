import Examples.Ripemd160Old.DecodeGenerated.Chunk30

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes31 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4399⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4400⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4707⟩, 2))),
  (⟨4403⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4404⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4405⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4407⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4408⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4688⟩, 2))),
  (⟨4411⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4412⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4413⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨4415⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4416⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4669⟩, 2))),
  (⟨4419⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4420⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4421⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨4423⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4424⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4650⟩, 2))),
  (⟨4427⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4428⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4429⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨4431⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4432⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4631⟩, 2))),
  (⟨4435⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4436⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4437⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨4439⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4440⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4612⟩, 2))),
  (⟨4443⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4444⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4445⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨4446⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4447⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4593⟩, 2))),
  (⟨4450⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4451⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4452⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨4454⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4455⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4574⟩, 2))),
  (⟨4458⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4459⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4460⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨4462⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4463⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4555⟩, 2))),
  (⟨4466⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4467⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4468⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨4470⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4471⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4536⟩, 2))),
  (⟨4474⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4475⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4476⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨4478⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4479⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4517⟩, 2))),
  (⟨4482⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4483⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨4485⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4486⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4499⟩, 2))),
  (⟨4489⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4490⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4491⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4492⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4493⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4494⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4495⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2))),
  (⟨4498⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4499⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4500⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4501⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4502⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4503⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4504⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4505⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4506⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨4508⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4509⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4510⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4511⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4512⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4513⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4516⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4517⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4518⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4519⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4520⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4521⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4522⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4523⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4524⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4525⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨4527⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4528⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4529⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4530⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4531⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4532⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4535⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4536⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4537⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4538⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4539⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4540⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none))
]

private theorem generatedDecodes31_correct : ∀ i : Fin generatedDecodes31.size,
    decode runtimeBytecode generatedDecodes31[i].1 = generatedDecodes31[i].2 := by
  native_decide

theorem decode_4399 : decode runtimeBytecode ⟨4399⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨0, by decide⟩
theorem decode_4400 : decode runtimeBytecode ⟨4400⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4707⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨1, by decide⟩
theorem decode_4403 : decode runtimeBytecode ⟨4403⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨2, by decide⟩
theorem decode_4404 : decode runtimeBytecode ⟨4404⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨3, by decide⟩
theorem decode_4405 : decode runtimeBytecode ⟨4405⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨4, by decide⟩
theorem decode_4407 : decode runtimeBytecode ⟨4407⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨5, by decide⟩
theorem decode_4408 : decode runtimeBytecode ⟨4408⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4688⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨6, by decide⟩
theorem decode_4411 : decode runtimeBytecode ⟨4411⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨7, by decide⟩
theorem decode_4412 : decode runtimeBytecode ⟨4412⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨8, by decide⟩
theorem decode_4413 : decode runtimeBytecode ⟨4413⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨9, by decide⟩
theorem decode_4415 : decode runtimeBytecode ⟨4415⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨10, by decide⟩
theorem decode_4416 : decode runtimeBytecode ⟨4416⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4669⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨11, by decide⟩
theorem decode_4419 : decode runtimeBytecode ⟨4419⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨12, by decide⟩
theorem decode_4420 : decode runtimeBytecode ⟨4420⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨13, by decide⟩
theorem decode_4421 : decode runtimeBytecode ⟨4421⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨14, by decide⟩
theorem decode_4423 : decode runtimeBytecode ⟨4423⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨15, by decide⟩
theorem decode_4424 : decode runtimeBytecode ⟨4424⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4650⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨16, by decide⟩
theorem decode_4427 : decode runtimeBytecode ⟨4427⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨17, by decide⟩
theorem decode_4428 : decode runtimeBytecode ⟨4428⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨18, by decide⟩
theorem decode_4429 : decode runtimeBytecode ⟨4429⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨19, by decide⟩
theorem decode_4431 : decode runtimeBytecode ⟨4431⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨20, by decide⟩
theorem decode_4432 : decode runtimeBytecode ⟨4432⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4631⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨21, by decide⟩
theorem decode_4435 : decode runtimeBytecode ⟨4435⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨22, by decide⟩
theorem decode_4436 : decode runtimeBytecode ⟨4436⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨23, by decide⟩
theorem decode_4437 : decode runtimeBytecode ⟨4437⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨24, by decide⟩
theorem decode_4439 : decode runtimeBytecode ⟨4439⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨25, by decide⟩
theorem decode_4440 : decode runtimeBytecode ⟨4440⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4612⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨26, by decide⟩
theorem decode_4443 : decode runtimeBytecode ⟨4443⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨27, by decide⟩
theorem decode_4444 : decode runtimeBytecode ⟨4444⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨28, by decide⟩
theorem decode_4445 : decode runtimeBytecode ⟨4445⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨29, by decide⟩
theorem decode_4446 : decode runtimeBytecode ⟨4446⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨30, by decide⟩
theorem decode_4447 : decode runtimeBytecode ⟨4447⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4593⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨31, by decide⟩
theorem decode_4450 : decode runtimeBytecode ⟨4450⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨32, by decide⟩
theorem decode_4451 : decode runtimeBytecode ⟨4451⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨33, by decide⟩
theorem decode_4452 : decode runtimeBytecode ⟨4452⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨34, by decide⟩
theorem decode_4454 : decode runtimeBytecode ⟨4454⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨35, by decide⟩
theorem decode_4455 : decode runtimeBytecode ⟨4455⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4574⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨36, by decide⟩
theorem decode_4458 : decode runtimeBytecode ⟨4458⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨37, by decide⟩
theorem decode_4459 : decode runtimeBytecode ⟨4459⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨38, by decide⟩
theorem decode_4460 : decode runtimeBytecode ⟨4460⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨39, by decide⟩
theorem decode_4462 : decode runtimeBytecode ⟨4462⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨40, by decide⟩
theorem decode_4463 : decode runtimeBytecode ⟨4463⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4555⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨41, by decide⟩
theorem decode_4466 : decode runtimeBytecode ⟨4466⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨42, by decide⟩
theorem decode_4467 : decode runtimeBytecode ⟨4467⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨43, by decide⟩
theorem decode_4468 : decode runtimeBytecode ⟨4468⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨44, by decide⟩
theorem decode_4470 : decode runtimeBytecode ⟨4470⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨45, by decide⟩
theorem decode_4471 : decode runtimeBytecode ⟨4471⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4536⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨46, by decide⟩
theorem decode_4474 : decode runtimeBytecode ⟨4474⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨47, by decide⟩
theorem decode_4475 : decode runtimeBytecode ⟨4475⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨48, by decide⟩
theorem decode_4476 : decode runtimeBytecode ⟨4476⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨49, by decide⟩
theorem decode_4478 : decode runtimeBytecode ⟨4478⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨50, by decide⟩
theorem decode_4479 : decode runtimeBytecode ⟨4479⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4517⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨51, by decide⟩
theorem decode_4482 : decode runtimeBytecode ⟨4482⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨52, by decide⟩
theorem decode_4483 : decode runtimeBytecode ⟨4483⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨53, by decide⟩
theorem decode_4485 : decode runtimeBytecode ⟨4485⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨54, by decide⟩
theorem decode_4486 : decode runtimeBytecode ⟨4486⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4499⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨55, by decide⟩
theorem decode_4489 : decode runtimeBytecode ⟨4489⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨56, by decide⟩
theorem decode_4490 : decode runtimeBytecode ⟨4490⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨57, by decide⟩
theorem decode_4491 : decode runtimeBytecode ⟨4491⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨58, by decide⟩
theorem decode_4492 : decode runtimeBytecode ⟨4492⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨59, by decide⟩
theorem decode_4493 : decode runtimeBytecode ⟨4493⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨60, by decide⟩
theorem decode_4494 : decode runtimeBytecode ⟨4494⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨61, by decide⟩
theorem decode_4495 : decode runtimeBytecode ⟨4495⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨62, by decide⟩
theorem decode_4498 : decode runtimeBytecode ⟨4498⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨63, by decide⟩
theorem decode_4499 : decode runtimeBytecode ⟨4499⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨64, by decide⟩
theorem decode_4500 : decode runtimeBytecode ⟨4500⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨65, by decide⟩
theorem decode_4501 : decode runtimeBytecode ⟨4501⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨66, by decide⟩
theorem decode_4502 : decode runtimeBytecode ⟨4502⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨67, by decide⟩
theorem decode_4503 : decode runtimeBytecode ⟨4503⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨68, by decide⟩
theorem decode_4504 : decode runtimeBytecode ⟨4504⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨69, by decide⟩
theorem decode_4505 : decode runtimeBytecode ⟨4505⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨70, by decide⟩
theorem decode_4506 : decode runtimeBytecode ⟨4506⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨71, by decide⟩
theorem decode_4508 : decode runtimeBytecode ⟨4508⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨72, by decide⟩
theorem decode_4509 : decode runtimeBytecode ⟨4509⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨73, by decide⟩
theorem decode_4510 : decode runtimeBytecode ⟨4510⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨74, by decide⟩
theorem decode_4511 : decode runtimeBytecode ⟨4511⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨75, by decide⟩
theorem decode_4512 : decode runtimeBytecode ⟨4512⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨76, by decide⟩
theorem decode_4513 : decode runtimeBytecode ⟨4513⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨77, by decide⟩
theorem decode_4516 : decode runtimeBytecode ⟨4516⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨78, by decide⟩
theorem decode_4517 : decode runtimeBytecode ⟨4517⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨79, by decide⟩
theorem decode_4518 : decode runtimeBytecode ⟨4518⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨80, by decide⟩
theorem decode_4519 : decode runtimeBytecode ⟨4519⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨81, by decide⟩
theorem decode_4520 : decode runtimeBytecode ⟨4520⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨82, by decide⟩
theorem decode_4521 : decode runtimeBytecode ⟨4521⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨83, by decide⟩
theorem decode_4522 : decode runtimeBytecode ⟨4522⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨84, by decide⟩
theorem decode_4523 : decode runtimeBytecode ⟨4523⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨85, by decide⟩
theorem decode_4524 : decode runtimeBytecode ⟨4524⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨86, by decide⟩
theorem decode_4525 : decode runtimeBytecode ⟨4525⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨87, by decide⟩
theorem decode_4527 : decode runtimeBytecode ⟨4527⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨88, by decide⟩
theorem decode_4528 : decode runtimeBytecode ⟨4528⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨89, by decide⟩
theorem decode_4529 : decode runtimeBytecode ⟨4529⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨90, by decide⟩
theorem decode_4530 : decode runtimeBytecode ⟨4530⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨91, by decide⟩
theorem decode_4531 : decode runtimeBytecode ⟨4531⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨92, by decide⟩
theorem decode_4532 : decode runtimeBytecode ⟨4532⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨93, by decide⟩
theorem decode_4535 : decode runtimeBytecode ⟨4535⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨94, by decide⟩
theorem decode_4536 : decode runtimeBytecode ⟨4536⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨95, by decide⟩
theorem decode_4537 : decode runtimeBytecode ⟨4537⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨96, by decide⟩
theorem decode_4538 : decode runtimeBytecode ⟨4538⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨97, by decide⟩
theorem decode_4539 : decode runtimeBytecode ⟨4539⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨98, by decide⟩
theorem decode_4540 : decode runtimeBytecode ⟨4540⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes31] using generatedDecodes31_correct ⟨99, by decide⟩

end Ripemd160Old
