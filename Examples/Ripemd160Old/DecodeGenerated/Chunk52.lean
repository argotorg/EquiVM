import Examples.Ripemd160Old.DecodeGenerated.Chunk51

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes52 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7144⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7147⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7148⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7149⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7150⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7151⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7152⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7154⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7155⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7158⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7159⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7160⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7161⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7162⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7163⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7165⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7166⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7169⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7170⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7171⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7172⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7173⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7174⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7176⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7177⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7180⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7181⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7182⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7183⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7184⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7185⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7187⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7188⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7191⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7192⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7193⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7194⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7195⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7196⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7198⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7199⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7202⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7203⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7204⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7205⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨7207⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7208⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨7209⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7210⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7211⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7212⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7501⟩, 2))),
  (⟨7215⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7216⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7217⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7219⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7220⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7490⟩, 2))),
  (⟨7223⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7224⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7225⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7227⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7228⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7479⟩, 2))),
  (⟨7231⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7232⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7233⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7235⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7236⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7468⟩, 2))),
  (⟨7239⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7240⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7241⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7243⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7244⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7457⟩, 2))),
  (⟨7247⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7248⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7249⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7251⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7252⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7446⟩, 2))),
  (⟨7255⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7256⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7257⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7259⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7260⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7435⟩, 2))),
  (⟨7263⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7264⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7265⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7267⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7268⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7424⟩, 2))),
  (⟨7271⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7272⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7273⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7275⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7276⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7413⟩, 2))),
  (⟨7279⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7280⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7281⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7283⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7284⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7402⟩, 2))),
  (⟨7287⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7288⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨7289⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7290⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes52_correct : ∀ i : Fin generatedDecodes52.size,
    decode runtimeBytecode generatedDecodes52[i].1 = generatedDecodes52[i].2 := by
  native_decide

theorem decode_7144 : decode runtimeBytecode ⟨7144⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨0, by decide⟩
theorem decode_7147 : decode runtimeBytecode ⟨7147⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨1, by decide⟩
theorem decode_7148 : decode runtimeBytecode ⟨7148⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨2, by decide⟩
theorem decode_7149 : decode runtimeBytecode ⟨7149⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨3, by decide⟩
theorem decode_7150 : decode runtimeBytecode ⟨7150⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨4, by decide⟩
theorem decode_7151 : decode runtimeBytecode ⟨7151⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨5, by decide⟩
theorem decode_7152 : decode runtimeBytecode ⟨7152⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨6, by decide⟩
theorem decode_7154 : decode runtimeBytecode ⟨7154⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨7, by decide⟩
theorem decode_7155 : decode runtimeBytecode ⟨7155⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨8, by decide⟩
theorem decode_7158 : decode runtimeBytecode ⟨7158⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨9, by decide⟩
theorem decode_7159 : decode runtimeBytecode ⟨7159⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨10, by decide⟩
theorem decode_7160 : decode runtimeBytecode ⟨7160⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨11, by decide⟩
theorem decode_7161 : decode runtimeBytecode ⟨7161⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨12, by decide⟩
theorem decode_7162 : decode runtimeBytecode ⟨7162⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨13, by decide⟩
theorem decode_7163 : decode runtimeBytecode ⟨7163⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨14, by decide⟩
theorem decode_7165 : decode runtimeBytecode ⟨7165⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨15, by decide⟩
theorem decode_7166 : decode runtimeBytecode ⟨7166⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨16, by decide⟩
theorem decode_7169 : decode runtimeBytecode ⟨7169⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨17, by decide⟩
theorem decode_7170 : decode runtimeBytecode ⟨7170⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨18, by decide⟩
theorem decode_7171 : decode runtimeBytecode ⟨7171⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨19, by decide⟩
theorem decode_7172 : decode runtimeBytecode ⟨7172⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨20, by decide⟩
theorem decode_7173 : decode runtimeBytecode ⟨7173⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨21, by decide⟩
theorem decode_7174 : decode runtimeBytecode ⟨7174⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨22, by decide⟩
theorem decode_7176 : decode runtimeBytecode ⟨7176⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨23, by decide⟩
theorem decode_7177 : decode runtimeBytecode ⟨7177⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨24, by decide⟩
theorem decode_7180 : decode runtimeBytecode ⟨7180⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨25, by decide⟩
theorem decode_7181 : decode runtimeBytecode ⟨7181⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨26, by decide⟩
theorem decode_7182 : decode runtimeBytecode ⟨7182⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨27, by decide⟩
theorem decode_7183 : decode runtimeBytecode ⟨7183⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨28, by decide⟩
theorem decode_7184 : decode runtimeBytecode ⟨7184⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨29, by decide⟩
theorem decode_7185 : decode runtimeBytecode ⟨7185⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨30, by decide⟩
theorem decode_7187 : decode runtimeBytecode ⟨7187⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨31, by decide⟩
theorem decode_7188 : decode runtimeBytecode ⟨7188⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨32, by decide⟩
theorem decode_7191 : decode runtimeBytecode ⟨7191⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨33, by decide⟩
theorem decode_7192 : decode runtimeBytecode ⟨7192⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨34, by decide⟩
theorem decode_7193 : decode runtimeBytecode ⟨7193⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨35, by decide⟩
theorem decode_7194 : decode runtimeBytecode ⟨7194⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨36, by decide⟩
theorem decode_7195 : decode runtimeBytecode ⟨7195⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨37, by decide⟩
theorem decode_7196 : decode runtimeBytecode ⟨7196⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨38, by decide⟩
theorem decode_7198 : decode runtimeBytecode ⟨7198⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨39, by decide⟩
theorem decode_7199 : decode runtimeBytecode ⟨7199⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨40, by decide⟩
theorem decode_7202 : decode runtimeBytecode ⟨7202⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨41, by decide⟩
theorem decode_7203 : decode runtimeBytecode ⟨7203⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨42, by decide⟩
theorem decode_7204 : decode runtimeBytecode ⟨7204⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨43, by decide⟩
theorem decode_7205 : decode runtimeBytecode ⟨7205⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨44, by decide⟩
theorem decode_7207 : decode runtimeBytecode ⟨7207⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨45, by decide⟩
theorem decode_7208 : decode runtimeBytecode ⟨7208⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨46, by decide⟩
theorem decode_7209 : decode runtimeBytecode ⟨7209⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨47, by decide⟩
theorem decode_7210 : decode runtimeBytecode ⟨7210⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨48, by decide⟩
theorem decode_7211 : decode runtimeBytecode ⟨7211⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨49, by decide⟩
theorem decode_7212 : decode runtimeBytecode ⟨7212⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7501⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨50, by decide⟩
theorem decode_7215 : decode runtimeBytecode ⟨7215⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨51, by decide⟩
theorem decode_7216 : decode runtimeBytecode ⟨7216⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨52, by decide⟩
theorem decode_7217 : decode runtimeBytecode ⟨7217⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨53, by decide⟩
theorem decode_7219 : decode runtimeBytecode ⟨7219⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨54, by decide⟩
theorem decode_7220 : decode runtimeBytecode ⟨7220⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7490⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨55, by decide⟩
theorem decode_7223 : decode runtimeBytecode ⟨7223⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨56, by decide⟩
theorem decode_7224 : decode runtimeBytecode ⟨7224⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨57, by decide⟩
theorem decode_7225 : decode runtimeBytecode ⟨7225⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨58, by decide⟩
theorem decode_7227 : decode runtimeBytecode ⟨7227⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨59, by decide⟩
theorem decode_7228 : decode runtimeBytecode ⟨7228⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7479⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨60, by decide⟩
theorem decode_7231 : decode runtimeBytecode ⟨7231⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨61, by decide⟩
theorem decode_7232 : decode runtimeBytecode ⟨7232⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨62, by decide⟩
theorem decode_7233 : decode runtimeBytecode ⟨7233⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨63, by decide⟩
theorem decode_7235 : decode runtimeBytecode ⟨7235⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨64, by decide⟩
theorem decode_7236 : decode runtimeBytecode ⟨7236⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7468⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨65, by decide⟩
theorem decode_7239 : decode runtimeBytecode ⟨7239⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨66, by decide⟩
theorem decode_7240 : decode runtimeBytecode ⟨7240⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨67, by decide⟩
theorem decode_7241 : decode runtimeBytecode ⟨7241⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨68, by decide⟩
theorem decode_7243 : decode runtimeBytecode ⟨7243⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨69, by decide⟩
theorem decode_7244 : decode runtimeBytecode ⟨7244⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7457⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨70, by decide⟩
theorem decode_7247 : decode runtimeBytecode ⟨7247⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨71, by decide⟩
theorem decode_7248 : decode runtimeBytecode ⟨7248⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨72, by decide⟩
theorem decode_7249 : decode runtimeBytecode ⟨7249⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨73, by decide⟩
theorem decode_7251 : decode runtimeBytecode ⟨7251⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨74, by decide⟩
theorem decode_7252 : decode runtimeBytecode ⟨7252⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7446⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨75, by decide⟩
theorem decode_7255 : decode runtimeBytecode ⟨7255⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨76, by decide⟩
theorem decode_7256 : decode runtimeBytecode ⟨7256⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨77, by decide⟩
theorem decode_7257 : decode runtimeBytecode ⟨7257⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨78, by decide⟩
theorem decode_7259 : decode runtimeBytecode ⟨7259⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨79, by decide⟩
theorem decode_7260 : decode runtimeBytecode ⟨7260⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7435⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨80, by decide⟩
theorem decode_7263 : decode runtimeBytecode ⟨7263⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨81, by decide⟩
theorem decode_7264 : decode runtimeBytecode ⟨7264⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨82, by decide⟩
theorem decode_7265 : decode runtimeBytecode ⟨7265⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨83, by decide⟩
theorem decode_7267 : decode runtimeBytecode ⟨7267⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨84, by decide⟩
theorem decode_7268 : decode runtimeBytecode ⟨7268⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7424⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨85, by decide⟩
theorem decode_7271 : decode runtimeBytecode ⟨7271⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨86, by decide⟩
theorem decode_7272 : decode runtimeBytecode ⟨7272⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨87, by decide⟩
theorem decode_7273 : decode runtimeBytecode ⟨7273⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨88, by decide⟩
theorem decode_7275 : decode runtimeBytecode ⟨7275⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨89, by decide⟩
theorem decode_7276 : decode runtimeBytecode ⟨7276⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7413⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨90, by decide⟩
theorem decode_7279 : decode runtimeBytecode ⟨7279⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨91, by decide⟩
theorem decode_7280 : decode runtimeBytecode ⟨7280⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨92, by decide⟩
theorem decode_7281 : decode runtimeBytecode ⟨7281⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨93, by decide⟩
theorem decode_7283 : decode runtimeBytecode ⟨7283⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨94, by decide⟩
theorem decode_7284 : decode runtimeBytecode ⟨7284⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7402⟩, 2)) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨95, by decide⟩
theorem decode_7287 : decode runtimeBytecode ⟨7287⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨96, by decide⟩
theorem decode_7288 : decode runtimeBytecode ⟨7288⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨97, by decide⟩
theorem decode_7289 : decode runtimeBytecode ⟨7289⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨98, by decide⟩
theorem decode_7290 : decode runtimeBytecode ⟨7290⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes52] using generatedDecodes52_correct ⟨99, by decide⟩

end Ripemd160Old
