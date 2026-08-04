import Examples.Ripemd160Old.DecodeGenerated.Chunk28

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes29 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4120⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4121⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4122⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2))),
  (⟨4125⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4126⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4127⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨4129⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4130⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4343⟩, 2))),
  (⟨4133⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨10⟩, 1))),
  (⟨4135⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨4140⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4141⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨4142⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4143⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4144⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨4145⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨4146⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4147⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4148⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4149⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨4151⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨4152⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4153⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4154⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4155⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4328⟩, 2))),
  (⟨4158⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨4160⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none)),
  (⟨4161⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4162⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4163⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4164⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨4165⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none)),
  (⟨4166⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨4168⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨4169⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨4170⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨4171⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none)),
  (⟨4172⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨4173⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4174⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨4175⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨4177⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨4178⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none)),
  (⟨4179⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4180⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4181⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4182⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP12), none)),
  (⟨4183⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨4184⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4185⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4186⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none)),
  (⟨4187⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4188⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4189⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4190⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8238⟩, 2))),
  (⟨4193⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4194⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4195⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨4197⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4198⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8207⟩, 2))),
  (⟨4201⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4202⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4203⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨4205⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4206⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8180⟩, 2))),
  (⟨4209⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4210⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4211⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨4213⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4214⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8151⟩, 2))),
  (⟨4217⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4218⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨4220⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4221⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8130⟩, 2))),
  (⟨4224⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4225⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4226⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4227⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4228⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4229⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4230⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4231⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none)),
  (⟨4232⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4233⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4234⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4235⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7821⟩, 2))),
  (⟨4238⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4239⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4240⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨4242⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4243⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7512⟩, 2))),
  (⟨4246⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4247⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4248⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨4250⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4251⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7203⟩, 2))),
  (⟨4254⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4255⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4256⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨4258⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes29_correct : ∀ i : Fin generatedDecodes29.size,
    decode runtimeBytecode generatedDecodes29[i].1 = generatedDecodes29[i].2 := by
  native_decide

theorem decode_4120 : decode runtimeBytecode ⟨4120⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨0, by decide⟩
theorem decode_4121 : decode runtimeBytecode ⟨4121⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨1, by decide⟩
theorem decode_4122 : decode runtimeBytecode ⟨4122⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨2, by decide⟩
theorem decode_4125 : decode runtimeBytecode ⟨4125⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨3, by decide⟩
theorem decode_4126 : decode runtimeBytecode ⟨4126⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨4, by decide⟩
theorem decode_4127 : decode runtimeBytecode ⟨4127⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨5, by decide⟩
theorem decode_4129 : decode runtimeBytecode ⟨4129⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨6, by decide⟩
theorem decode_4130 : decode runtimeBytecode ⟨4130⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4343⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨7, by decide⟩
theorem decode_4133 : decode runtimeBytecode ⟨4133⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨10⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨8, by decide⟩
theorem decode_4135 : decode runtimeBytecode ⟨4135⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨9, by decide⟩
theorem decode_4140 : decode runtimeBytecode ⟨4140⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨10, by decide⟩
theorem decode_4141 : decode runtimeBytecode ⟨4141⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨11, by decide⟩
theorem decode_4142 : decode runtimeBytecode ⟨4142⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨12, by decide⟩
theorem decode_4143 : decode runtimeBytecode ⟨4143⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨13, by decide⟩
theorem decode_4144 : decode runtimeBytecode ⟨4144⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨14, by decide⟩
theorem decode_4145 : decode runtimeBytecode ⟨4145⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨15, by decide⟩
theorem decode_4146 : decode runtimeBytecode ⟨4146⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨16, by decide⟩
theorem decode_4147 : decode runtimeBytecode ⟨4147⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨17, by decide⟩
theorem decode_4148 : decode runtimeBytecode ⟨4148⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨18, by decide⟩
theorem decode_4149 : decode runtimeBytecode ⟨4149⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨19, by decide⟩
theorem decode_4151 : decode runtimeBytecode ⟨4151⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨20, by decide⟩
theorem decode_4152 : decode runtimeBytecode ⟨4152⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨21, by decide⟩
theorem decode_4153 : decode runtimeBytecode ⟨4153⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨22, by decide⟩
theorem decode_4154 : decode runtimeBytecode ⟨4154⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨23, by decide⟩
theorem decode_4155 : decode runtimeBytecode ⟨4155⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4328⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨24, by decide⟩
theorem decode_4158 : decode runtimeBytecode ⟨4158⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨25, by decide⟩
theorem decode_4160 : decode runtimeBytecode ⟨4160⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨26, by decide⟩
theorem decode_4161 : decode runtimeBytecode ⟨4161⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨27, by decide⟩
theorem decode_4162 : decode runtimeBytecode ⟨4162⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨28, by decide⟩
theorem decode_4163 : decode runtimeBytecode ⟨4163⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨29, by decide⟩
theorem decode_4164 : decode runtimeBytecode ⟨4164⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨30, by decide⟩
theorem decode_4165 : decode runtimeBytecode ⟨4165⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨31, by decide⟩
theorem decode_4166 : decode runtimeBytecode ⟨4166⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨32, by decide⟩
theorem decode_4168 : decode runtimeBytecode ⟨4168⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨33, by decide⟩
theorem decode_4169 : decode runtimeBytecode ⟨4169⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨34, by decide⟩
theorem decode_4170 : decode runtimeBytecode ⟨4170⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨35, by decide⟩
theorem decode_4171 : decode runtimeBytecode ⟨4171⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨36, by decide⟩
theorem decode_4172 : decode runtimeBytecode ⟨4172⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨37, by decide⟩
theorem decode_4173 : decode runtimeBytecode ⟨4173⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨38, by decide⟩
theorem decode_4174 : decode runtimeBytecode ⟨4174⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨39, by decide⟩
theorem decode_4175 : decode runtimeBytecode ⟨4175⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨40, by decide⟩
theorem decode_4177 : decode runtimeBytecode ⟨4177⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨41, by decide⟩
theorem decode_4178 : decode runtimeBytecode ⟨4178⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨42, by decide⟩
theorem decode_4179 : decode runtimeBytecode ⟨4179⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨43, by decide⟩
theorem decode_4180 : decode runtimeBytecode ⟨4180⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨44, by decide⟩
theorem decode_4181 : decode runtimeBytecode ⟨4181⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨45, by decide⟩
theorem decode_4182 : decode runtimeBytecode ⟨4182⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP12), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨46, by decide⟩
theorem decode_4183 : decode runtimeBytecode ⟨4183⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨47, by decide⟩
theorem decode_4184 : decode runtimeBytecode ⟨4184⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨48, by decide⟩
theorem decode_4185 : decode runtimeBytecode ⟨4185⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨49, by decide⟩
theorem decode_4186 : decode runtimeBytecode ⟨4186⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨50, by decide⟩
theorem decode_4187 : decode runtimeBytecode ⟨4187⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨51, by decide⟩
theorem decode_4188 : decode runtimeBytecode ⟨4188⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨52, by decide⟩
theorem decode_4189 : decode runtimeBytecode ⟨4189⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨53, by decide⟩
theorem decode_4190 : decode runtimeBytecode ⟨4190⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8238⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨54, by decide⟩
theorem decode_4193 : decode runtimeBytecode ⟨4193⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨55, by decide⟩
theorem decode_4194 : decode runtimeBytecode ⟨4194⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨56, by decide⟩
theorem decode_4195 : decode runtimeBytecode ⟨4195⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨57, by decide⟩
theorem decode_4197 : decode runtimeBytecode ⟨4197⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨58, by decide⟩
theorem decode_4198 : decode runtimeBytecode ⟨4198⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8207⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨59, by decide⟩
theorem decode_4201 : decode runtimeBytecode ⟨4201⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨60, by decide⟩
theorem decode_4202 : decode runtimeBytecode ⟨4202⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨61, by decide⟩
theorem decode_4203 : decode runtimeBytecode ⟨4203⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨62, by decide⟩
theorem decode_4205 : decode runtimeBytecode ⟨4205⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨63, by decide⟩
theorem decode_4206 : decode runtimeBytecode ⟨4206⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8180⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨64, by decide⟩
theorem decode_4209 : decode runtimeBytecode ⟨4209⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨65, by decide⟩
theorem decode_4210 : decode runtimeBytecode ⟨4210⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨66, by decide⟩
theorem decode_4211 : decode runtimeBytecode ⟨4211⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨67, by decide⟩
theorem decode_4213 : decode runtimeBytecode ⟨4213⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨68, by decide⟩
theorem decode_4214 : decode runtimeBytecode ⟨4214⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8151⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨69, by decide⟩
theorem decode_4217 : decode runtimeBytecode ⟨4217⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨70, by decide⟩
theorem decode_4218 : decode runtimeBytecode ⟨4218⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨71, by decide⟩
theorem decode_4220 : decode runtimeBytecode ⟨4220⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨72, by decide⟩
theorem decode_4221 : decode runtimeBytecode ⟨4221⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8130⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨73, by decide⟩
theorem decode_4224 : decode runtimeBytecode ⟨4224⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨74, by decide⟩
theorem decode_4225 : decode runtimeBytecode ⟨4225⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨75, by decide⟩
theorem decode_4226 : decode runtimeBytecode ⟨4226⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨76, by decide⟩
theorem decode_4227 : decode runtimeBytecode ⟨4227⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨77, by decide⟩
theorem decode_4228 : decode runtimeBytecode ⟨4228⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨78, by decide⟩
theorem decode_4229 : decode runtimeBytecode ⟨4229⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨79, by decide⟩
theorem decode_4230 : decode runtimeBytecode ⟨4230⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨80, by decide⟩
theorem decode_4231 : decode runtimeBytecode ⟨4231⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨81, by decide⟩
theorem decode_4232 : decode runtimeBytecode ⟨4232⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨82, by decide⟩
theorem decode_4233 : decode runtimeBytecode ⟨4233⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨83, by decide⟩
theorem decode_4234 : decode runtimeBytecode ⟨4234⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨84, by decide⟩
theorem decode_4235 : decode runtimeBytecode ⟨4235⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7821⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨85, by decide⟩
theorem decode_4238 : decode runtimeBytecode ⟨4238⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨86, by decide⟩
theorem decode_4239 : decode runtimeBytecode ⟨4239⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨87, by decide⟩
theorem decode_4240 : decode runtimeBytecode ⟨4240⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨88, by decide⟩
theorem decode_4242 : decode runtimeBytecode ⟨4242⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨89, by decide⟩
theorem decode_4243 : decode runtimeBytecode ⟨4243⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7512⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨90, by decide⟩
theorem decode_4246 : decode runtimeBytecode ⟨4246⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨91, by decide⟩
theorem decode_4247 : decode runtimeBytecode ⟨4247⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨92, by decide⟩
theorem decode_4248 : decode runtimeBytecode ⟨4248⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨93, by decide⟩
theorem decode_4250 : decode runtimeBytecode ⟨4250⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨94, by decide⟩
theorem decode_4251 : decode runtimeBytecode ⟨4251⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7203⟩, 2)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨95, by decide⟩
theorem decode_4254 : decode runtimeBytecode ⟨4254⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨96, by decide⟩
theorem decode_4255 : decode runtimeBytecode ⟨4255⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨97, by decide⟩
theorem decode_4256 : decode runtimeBytecode ⟨4256⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨98, by decide⟩
theorem decode_4258 : decode runtimeBytecode ⟨4258⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes29] using generatedDecodes29_correct ⟨99, by decide⟩

end Ripemd160Old
