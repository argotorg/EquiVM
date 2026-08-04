import Examples.Ripemd160Old.DecodeGenerated.Chunk27

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes28 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3991⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3992⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3993⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3994⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3996⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3997⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨4000⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4001⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4002⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4003⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4004⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4005⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4006⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨402⟩, 2))),
  (⟨4009⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4010⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4011⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4012⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4013⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4014⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4015⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨4016⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none)),
  (⟨4017⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none)),
  (⟨4018⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨4019⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨4020⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨4021⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4022⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2840853838⟩, 4))),
  (⟨4027⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4028⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2))),
  (⟨4031⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4033⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4034⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4035⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4036⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4037⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4038⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨4039⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none)),
  (⟨4040⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4041⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none)),
  (⟨4042⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨4043⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4044⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4045⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4046⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨4047⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4048⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2400959708⟩, 4))),
  (⟨4053⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4054⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2))),
  (⟨4057⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4058⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4059⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4060⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4061⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4062⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4063⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4065⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4066⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨4067⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none)),
  (⟨4068⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨4069⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨4070⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4071⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1859775393⟩, 4))),
  (⟨4076⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4077⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2))),
  (⟨4080⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4081⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4082⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4083⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨4084⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4085⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4086⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4087⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨4088⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4089⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨4090⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4091⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨4092⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none)),
  (⟨4093⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4094⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4095⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨4096⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨4097⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4098⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1518500249⟩, 4))),
  (⟨4103⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨4104⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2))),
  (⟨4107⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4108⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4109⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4110⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none)),
  (⟨4111⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4112⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4113⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4114⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4115⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4116⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4117⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨4118⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨4119⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none))
]

private theorem generatedDecodes28_correct : ∀ i : Fin generatedDecodes28.size,
    decode runtimeBytecode generatedDecodes28[i].1 = generatedDecodes28[i].2 := by
  native_decide

theorem decode_3991 : decode runtimeBytecode ⟨3991⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨0, by decide⟩
theorem decode_3992 : decode runtimeBytecode ⟨3992⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨1, by decide⟩
theorem decode_3993 : decode runtimeBytecode ⟨3993⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨2, by decide⟩
theorem decode_3994 : decode runtimeBytecode ⟨3994⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨3, by decide⟩
theorem decode_3996 : decode runtimeBytecode ⟨3996⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨4, by decide⟩
theorem decode_3997 : decode runtimeBytecode ⟨3997⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨5, by decide⟩
theorem decode_4000 : decode runtimeBytecode ⟨4000⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨6, by decide⟩
theorem decode_4001 : decode runtimeBytecode ⟨4001⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨7, by decide⟩
theorem decode_4002 : decode runtimeBytecode ⟨4002⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨8, by decide⟩
theorem decode_4003 : decode runtimeBytecode ⟨4003⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨9, by decide⟩
theorem decode_4004 : decode runtimeBytecode ⟨4004⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨10, by decide⟩
theorem decode_4005 : decode runtimeBytecode ⟨4005⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨11, by decide⟩
theorem decode_4006 : decode runtimeBytecode ⟨4006⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨402⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨12, by decide⟩
theorem decode_4009 : decode runtimeBytecode ⟨4009⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨13, by decide⟩
theorem decode_4010 : decode runtimeBytecode ⟨4010⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨14, by decide⟩
theorem decode_4011 : decode runtimeBytecode ⟨4011⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨15, by decide⟩
theorem decode_4012 : decode runtimeBytecode ⟨4012⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨16, by decide⟩
theorem decode_4013 : decode runtimeBytecode ⟨4013⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨17, by decide⟩
theorem decode_4014 : decode runtimeBytecode ⟨4014⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨18, by decide⟩
theorem decode_4015 : decode runtimeBytecode ⟨4015⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨19, by decide⟩
theorem decode_4016 : decode runtimeBytecode ⟨4016⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨20, by decide⟩
theorem decode_4017 : decode runtimeBytecode ⟨4017⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨21, by decide⟩
theorem decode_4018 : decode runtimeBytecode ⟨4018⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨22, by decide⟩
theorem decode_4019 : decode runtimeBytecode ⟨4019⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨23, by decide⟩
theorem decode_4020 : decode runtimeBytecode ⟨4020⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨24, by decide⟩
theorem decode_4021 : decode runtimeBytecode ⟨4021⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨25, by decide⟩
theorem decode_4022 : decode runtimeBytecode ⟨4022⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2840853838⟩, 4)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨26, by decide⟩
theorem decode_4027 : decode runtimeBytecode ⟨4027⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨27, by decide⟩
theorem decode_4028 : decode runtimeBytecode ⟨4028⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨28, by decide⟩
theorem decode_4031 : decode runtimeBytecode ⟨4031⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨29, by decide⟩
theorem decode_4032 : decode runtimeBytecode ⟨4032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨30, by decide⟩
theorem decode_4033 : decode runtimeBytecode ⟨4033⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨31, by decide⟩
theorem decode_4034 : decode runtimeBytecode ⟨4034⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨32, by decide⟩
theorem decode_4035 : decode runtimeBytecode ⟨4035⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨33, by decide⟩
theorem decode_4036 : decode runtimeBytecode ⟨4036⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨34, by decide⟩
theorem decode_4037 : decode runtimeBytecode ⟨4037⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨35, by decide⟩
theorem decode_4038 : decode runtimeBytecode ⟨4038⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨36, by decide⟩
theorem decode_4039 : decode runtimeBytecode ⟨4039⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨37, by decide⟩
theorem decode_4040 : decode runtimeBytecode ⟨4040⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨38, by decide⟩
theorem decode_4041 : decode runtimeBytecode ⟨4041⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨39, by decide⟩
theorem decode_4042 : decode runtimeBytecode ⟨4042⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨40, by decide⟩
theorem decode_4043 : decode runtimeBytecode ⟨4043⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨41, by decide⟩
theorem decode_4044 : decode runtimeBytecode ⟨4044⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨42, by decide⟩
theorem decode_4045 : decode runtimeBytecode ⟨4045⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨43, by decide⟩
theorem decode_4046 : decode runtimeBytecode ⟨4046⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨44, by decide⟩
theorem decode_4047 : decode runtimeBytecode ⟨4047⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨45, by decide⟩
theorem decode_4048 : decode runtimeBytecode ⟨4048⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2400959708⟩, 4)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨46, by decide⟩
theorem decode_4053 : decode runtimeBytecode ⟨4053⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨47, by decide⟩
theorem decode_4054 : decode runtimeBytecode ⟨4054⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨48, by decide⟩
theorem decode_4057 : decode runtimeBytecode ⟨4057⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨49, by decide⟩
theorem decode_4058 : decode runtimeBytecode ⟨4058⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨50, by decide⟩
theorem decode_4059 : decode runtimeBytecode ⟨4059⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨51, by decide⟩
theorem decode_4060 : decode runtimeBytecode ⟨4060⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨52, by decide⟩
theorem decode_4061 : decode runtimeBytecode ⟨4061⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨53, by decide⟩
theorem decode_4062 : decode runtimeBytecode ⟨4062⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨54, by decide⟩
theorem decode_4063 : decode runtimeBytecode ⟨4063⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨55, by decide⟩
theorem decode_4064 : decode runtimeBytecode ⟨4064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨56, by decide⟩
theorem decode_4065 : decode runtimeBytecode ⟨4065⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨57, by decide⟩
theorem decode_4066 : decode runtimeBytecode ⟨4066⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨58, by decide⟩
theorem decode_4067 : decode runtimeBytecode ⟨4067⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨59, by decide⟩
theorem decode_4068 : decode runtimeBytecode ⟨4068⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨60, by decide⟩
theorem decode_4069 : decode runtimeBytecode ⟨4069⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨61, by decide⟩
theorem decode_4070 : decode runtimeBytecode ⟨4070⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨62, by decide⟩
theorem decode_4071 : decode runtimeBytecode ⟨4071⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1859775393⟩, 4)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨63, by decide⟩
theorem decode_4076 : decode runtimeBytecode ⟨4076⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨64, by decide⟩
theorem decode_4077 : decode runtimeBytecode ⟨4077⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨65, by decide⟩
theorem decode_4080 : decode runtimeBytecode ⟨4080⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨66, by decide⟩
theorem decode_4081 : decode runtimeBytecode ⟨4081⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨67, by decide⟩
theorem decode_4082 : decode runtimeBytecode ⟨4082⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨68, by decide⟩
theorem decode_4083 : decode runtimeBytecode ⟨4083⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨69, by decide⟩
theorem decode_4084 : decode runtimeBytecode ⟨4084⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨70, by decide⟩
theorem decode_4085 : decode runtimeBytecode ⟨4085⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨71, by decide⟩
theorem decode_4086 : decode runtimeBytecode ⟨4086⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨72, by decide⟩
theorem decode_4087 : decode runtimeBytecode ⟨4087⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨73, by decide⟩
theorem decode_4088 : decode runtimeBytecode ⟨4088⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨74, by decide⟩
theorem decode_4089 : decode runtimeBytecode ⟨4089⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨75, by decide⟩
theorem decode_4090 : decode runtimeBytecode ⟨4090⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨76, by decide⟩
theorem decode_4091 : decode runtimeBytecode ⟨4091⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨77, by decide⟩
theorem decode_4092 : decode runtimeBytecode ⟨4092⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.NOT), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨78, by decide⟩
theorem decode_4093 : decode runtimeBytecode ⟨4093⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨79, by decide⟩
theorem decode_4094 : decode runtimeBytecode ⟨4094⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨80, by decide⟩
theorem decode_4095 : decode runtimeBytecode ⟨4095⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨81, by decide⟩
theorem decode_4096 : decode runtimeBytecode ⟨4096⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨82, by decide⟩
theorem decode_4097 : decode runtimeBytecode ⟨4097⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨83, by decide⟩
theorem decode_4098 : decode runtimeBytecode ⟨4098⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1518500249⟩, 4)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨84, by decide⟩
theorem decode_4103 : decode runtimeBytecode ⟨4103⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨85, by decide⟩
theorem decode_4104 : decode runtimeBytecode ⟨4104⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨391⟩, 2)) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨86, by decide⟩
theorem decode_4107 : decode runtimeBytecode ⟨4107⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨87, by decide⟩
theorem decode_4108 : decode runtimeBytecode ⟨4108⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨88, by decide⟩
theorem decode_4109 : decode runtimeBytecode ⟨4109⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨89, by decide⟩
theorem decode_4110 : decode runtimeBytecode ⟨4110⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP9), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨90, by decide⟩
theorem decode_4111 : decode runtimeBytecode ⟨4111⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨91, by decide⟩
theorem decode_4112 : decode runtimeBytecode ⟨4112⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨92, by decide⟩
theorem decode_4113 : decode runtimeBytecode ⟨4113⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨93, by decide⟩
theorem decode_4114 : decode runtimeBytecode ⟨4114⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨94, by decide⟩
theorem decode_4115 : decode runtimeBytecode ⟨4115⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨95, by decide⟩
theorem decode_4116 : decode runtimeBytecode ⟨4116⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨96, by decide⟩
theorem decode_4117 : decode runtimeBytecode ⟨4117⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨97, by decide⟩
theorem decode_4118 : decode runtimeBytecode ⟨4118⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨98, by decide⟩
theorem decode_4119 : decode runtimeBytecode ⟨4119⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes28] using generatedDecodes28_correct ⟨99, by decide⟩

end Ripemd160Old
