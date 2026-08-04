import Examples.Ripemd160Old.DecodeGenerated.Chunk29

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes30 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4259⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6894⟩, 2))),
  (⟨4262⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4263⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨4265⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4266⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6586⟩, 2))),
  (⟨4269⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4270⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4271⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4272⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none)),
  (⟨4273⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4274⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4275⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4276⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6140⟩, 2))),
  (⟨4279⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4280⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4281⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨4283⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4284⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5694⟩, 2))),
  (⟨4287⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4288⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4289⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨4291⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4292⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5248⟩, 2))),
  (⟨4295⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4296⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4297⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨4299⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4300⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4802⟩, 2))),
  (⟨4303⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4304⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨4306⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4307⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4357⟩, 2))),
  (⟨4310⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4311⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4312⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4313⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨4315⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨4316⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4317⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4318⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4319⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4320⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4321⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4322⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4323⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4324⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2))),
  (⟨4327⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4328⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4329⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4330⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4331⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4332⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨4333⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨4334⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨4336⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨4337⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4338⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨4339⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2))),
  (⟨4342⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4343⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4344⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨4346⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨4347⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4348⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨4349⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨4351⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨4352⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4353⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨4354⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4355⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨4356⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4357⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4358⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨4360⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4361⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4362⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4363⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4364⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨4365⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4366⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4367⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4368⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4783⟩, 2))),
  (⟨4371⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4372⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4373⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨4375⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4376⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4764⟩, 2))),
  (⟨4379⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4380⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4381⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨4383⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4384⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4745⟩, 2))),
  (⟨4387⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4388⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4389⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨4391⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4392⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4726⟩, 2))),
  (⟨4395⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4396⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4397⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)))
]

private theorem generatedDecodes30_correct : ∀ i : Fin generatedDecodes30.size,
    decode runtimeBytecode generatedDecodes30[i].1 = generatedDecodes30[i].2 := by
  native_decide

theorem decode_4259 : decode runtimeBytecode ⟨4259⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6894⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨0, by decide⟩
theorem decode_4262 : decode runtimeBytecode ⟨4262⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨1, by decide⟩
theorem decode_4263 : decode runtimeBytecode ⟨4263⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨2, by decide⟩
theorem decode_4265 : decode runtimeBytecode ⟨4265⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨3, by decide⟩
theorem decode_4266 : decode runtimeBytecode ⟨4266⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6586⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨4, by decide⟩
theorem decode_4269 : decode runtimeBytecode ⟨4269⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨5, by decide⟩
theorem decode_4270 : decode runtimeBytecode ⟨4270⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨6, by decide⟩
theorem decode_4271 : decode runtimeBytecode ⟨4271⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨7, by decide⟩
theorem decode_4272 : decode runtimeBytecode ⟨4272⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨8, by decide⟩
theorem decode_4273 : decode runtimeBytecode ⟨4273⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨9, by decide⟩
theorem decode_4274 : decode runtimeBytecode ⟨4274⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨10, by decide⟩
theorem decode_4275 : decode runtimeBytecode ⟨4275⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨11, by decide⟩
theorem decode_4276 : decode runtimeBytecode ⟨4276⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6140⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨12, by decide⟩
theorem decode_4279 : decode runtimeBytecode ⟨4279⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨13, by decide⟩
theorem decode_4280 : decode runtimeBytecode ⟨4280⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨14, by decide⟩
theorem decode_4281 : decode runtimeBytecode ⟨4281⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨15, by decide⟩
theorem decode_4283 : decode runtimeBytecode ⟨4283⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨16, by decide⟩
theorem decode_4284 : decode runtimeBytecode ⟨4284⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5694⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨17, by decide⟩
theorem decode_4287 : decode runtimeBytecode ⟨4287⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨18, by decide⟩
theorem decode_4288 : decode runtimeBytecode ⟨4288⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨19, by decide⟩
theorem decode_4289 : decode runtimeBytecode ⟨4289⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨20, by decide⟩
theorem decode_4291 : decode runtimeBytecode ⟨4291⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨21, by decide⟩
theorem decode_4292 : decode runtimeBytecode ⟨4292⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5248⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨22, by decide⟩
theorem decode_4295 : decode runtimeBytecode ⟨4295⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨23, by decide⟩
theorem decode_4296 : decode runtimeBytecode ⟨4296⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨24, by decide⟩
theorem decode_4297 : decode runtimeBytecode ⟨4297⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨25, by decide⟩
theorem decode_4299 : decode runtimeBytecode ⟨4299⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨26, by decide⟩
theorem decode_4300 : decode runtimeBytecode ⟨4300⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4802⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨27, by decide⟩
theorem decode_4303 : decode runtimeBytecode ⟨4303⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨28, by decide⟩
theorem decode_4304 : decode runtimeBytecode ⟨4304⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨29, by decide⟩
theorem decode_4306 : decode runtimeBytecode ⟨4306⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨30, by decide⟩
theorem decode_4307 : decode runtimeBytecode ⟨4307⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4357⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨31, by decide⟩
theorem decode_4310 : decode runtimeBytecode ⟨4310⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨32, by decide⟩
theorem decode_4311 : decode runtimeBytecode ⟨4311⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨33, by decide⟩
theorem decode_4312 : decode runtimeBytecode ⟨4312⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨34, by decide⟩
theorem decode_4313 : decode runtimeBytecode ⟨4313⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨35, by decide⟩
theorem decode_4315 : decode runtimeBytecode ⟨4315⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨36, by decide⟩
theorem decode_4316 : decode runtimeBytecode ⟨4316⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨37, by decide⟩
theorem decode_4317 : decode runtimeBytecode ⟨4317⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨38, by decide⟩
theorem decode_4318 : decode runtimeBytecode ⟨4318⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨39, by decide⟩
theorem decode_4319 : decode runtimeBytecode ⟨4319⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨40, by decide⟩
theorem decode_4320 : decode runtimeBytecode ⟨4320⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨41, by decide⟩
theorem decode_4321 : decode runtimeBytecode ⟨4321⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨42, by decide⟩
theorem decode_4322 : decode runtimeBytecode ⟨4322⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨43, by decide⟩
theorem decode_4323 : decode runtimeBytecode ⟨4323⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨44, by decide⟩
theorem decode_4324 : decode runtimeBytecode ⟨4324⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨45, by decide⟩
theorem decode_4327 : decode runtimeBytecode ⟨4327⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨46, by decide⟩
theorem decode_4328 : decode runtimeBytecode ⟨4328⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨47, by decide⟩
theorem decode_4329 : decode runtimeBytecode ⟨4329⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨48, by decide⟩
theorem decode_4330 : decode runtimeBytecode ⟨4330⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨49, by decide⟩
theorem decode_4331 : decode runtimeBytecode ⟨4331⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨50, by decide⟩
theorem decode_4332 : decode runtimeBytecode ⟨4332⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨51, by decide⟩
theorem decode_4333 : decode runtimeBytecode ⟨4333⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨52, by decide⟩
theorem decode_4334 : decode runtimeBytecode ⟨4334⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨53, by decide⟩
theorem decode_4336 : decode runtimeBytecode ⟨4336⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨54, by decide⟩
theorem decode_4337 : decode runtimeBytecode ⟨4337⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨55, by decide⟩
theorem decode_4338 : decode runtimeBytecode ⟨4338⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨56, by decide⟩
theorem decode_4339 : decode runtimeBytecode ⟨4339⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨268⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨57, by decide⟩
theorem decode_4342 : decode runtimeBytecode ⟨4342⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨58, by decide⟩
theorem decode_4343 : decode runtimeBytecode ⟨4343⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨59, by decide⟩
theorem decode_4344 : decode runtimeBytecode ⟨4344⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨60, by decide⟩
theorem decode_4346 : decode runtimeBytecode ⟨4346⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨61, by decide⟩
theorem decode_4347 : decode runtimeBytecode ⟨4347⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨62, by decide⟩
theorem decode_4348 : decode runtimeBytecode ⟨4348⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨63, by decide⟩
theorem decode_4349 : decode runtimeBytecode ⟨4349⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨64, by decide⟩
theorem decode_4351 : decode runtimeBytecode ⟨4351⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨65, by decide⟩
theorem decode_4352 : decode runtimeBytecode ⟨4352⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨66, by decide⟩
theorem decode_4353 : decode runtimeBytecode ⟨4353⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨67, by decide⟩
theorem decode_4354 : decode runtimeBytecode ⟨4354⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨68, by decide⟩
theorem decode_4355 : decode runtimeBytecode ⟨4355⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨69, by decide⟩
theorem decode_4356 : decode runtimeBytecode ⟨4356⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨70, by decide⟩
theorem decode_4357 : decode runtimeBytecode ⟨4357⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨71, by decide⟩
theorem decode_4358 : decode runtimeBytecode ⟨4358⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨72, by decide⟩
theorem decode_4360 : decode runtimeBytecode ⟨4360⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨73, by decide⟩
theorem decode_4361 : decode runtimeBytecode ⟨4361⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨74, by decide⟩
theorem decode_4362 : decode runtimeBytecode ⟨4362⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨75, by decide⟩
theorem decode_4363 : decode runtimeBytecode ⟨4363⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨76, by decide⟩
theorem decode_4364 : decode runtimeBytecode ⟨4364⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨77, by decide⟩
theorem decode_4365 : decode runtimeBytecode ⟨4365⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨78, by decide⟩
theorem decode_4366 : decode runtimeBytecode ⟨4366⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨79, by decide⟩
theorem decode_4367 : decode runtimeBytecode ⟨4367⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨80, by decide⟩
theorem decode_4368 : decode runtimeBytecode ⟨4368⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4783⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨81, by decide⟩
theorem decode_4371 : decode runtimeBytecode ⟨4371⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨82, by decide⟩
theorem decode_4372 : decode runtimeBytecode ⟨4372⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨83, by decide⟩
theorem decode_4373 : decode runtimeBytecode ⟨4373⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨84, by decide⟩
theorem decode_4375 : decode runtimeBytecode ⟨4375⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨85, by decide⟩
theorem decode_4376 : decode runtimeBytecode ⟨4376⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4764⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨86, by decide⟩
theorem decode_4379 : decode runtimeBytecode ⟨4379⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨87, by decide⟩
theorem decode_4380 : decode runtimeBytecode ⟨4380⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨88, by decide⟩
theorem decode_4381 : decode runtimeBytecode ⟨4381⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨89, by decide⟩
theorem decode_4383 : decode runtimeBytecode ⟨4383⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨90, by decide⟩
theorem decode_4384 : decode runtimeBytecode ⟨4384⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4745⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨91, by decide⟩
theorem decode_4387 : decode runtimeBytecode ⟨4387⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨92, by decide⟩
theorem decode_4388 : decode runtimeBytecode ⟨4388⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨93, by decide⟩
theorem decode_4389 : decode runtimeBytecode ⟨4389⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨94, by decide⟩
theorem decode_4391 : decode runtimeBytecode ⟨4391⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨95, by decide⟩
theorem decode_4392 : decode runtimeBytecode ⟨4392⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4726⟩, 2)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨96, by decide⟩
theorem decode_4395 : decode runtimeBytecode ⟨4395⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨97, by decide⟩
theorem decode_4396 : decode runtimeBytecode ⟨4396⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨98, by decide⟩
theorem decode_4397 : decode runtimeBytecode ⟨4397⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes30] using generatedDecodes30_correct ⟨99, by decide⟩

end Ripemd160Old
