import Examples.Ripemd160Old.DecodeGenerated.Chunk50

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes51 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7005⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7006⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7050⟩, 2))),
  (⟨7009⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7010⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7011⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7013⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7014⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7040⟩, 2))),
  (⟨7017⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7018⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7020⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7021⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7030⟩, 2))),
  (⟨7024⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7025⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7026⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2))),
  (⟨7029⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7030⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7031⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7033⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7035⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7036⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7039⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7040⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7041⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7042⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7043⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7044⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨7045⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7046⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7049⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7050⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7051⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7052⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7053⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7054⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7056⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7057⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7060⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7061⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7062⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7063⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7065⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7067⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7068⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7071⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7072⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7073⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7074⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7075⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7076⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7078⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7079⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7082⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7083⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7084⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7085⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7086⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7087⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7089⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7090⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7093⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7094⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7095⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7096⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7097⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7098⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7100⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7101⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7104⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7105⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7106⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7107⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7108⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7109⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7111⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7112⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7115⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7116⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7117⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7118⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7119⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7120⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7121⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7122⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7125⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7126⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7127⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7128⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7129⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7130⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7132⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7133⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2))),
  (⟨7136⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7137⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7138⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7139⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7140⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7141⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7143⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none))
]

private theorem generatedDecodes51_correct : ∀ i : Fin generatedDecodes51.size,
    decode runtimeBytecode generatedDecodes51[i].1 = generatedDecodes51[i].2 := by
  native_decide

theorem decode_7005 : decode runtimeBytecode ⟨7005⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨0, by decide⟩
theorem decode_7006 : decode runtimeBytecode ⟨7006⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7050⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨1, by decide⟩
theorem decode_7009 : decode runtimeBytecode ⟨7009⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨2, by decide⟩
theorem decode_7010 : decode runtimeBytecode ⟨7010⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨3, by decide⟩
theorem decode_7011 : decode runtimeBytecode ⟨7011⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨4, by decide⟩
theorem decode_7013 : decode runtimeBytecode ⟨7013⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨5, by decide⟩
theorem decode_7014 : decode runtimeBytecode ⟨7014⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7040⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨6, by decide⟩
theorem decode_7017 : decode runtimeBytecode ⟨7017⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨7, by decide⟩
theorem decode_7018 : decode runtimeBytecode ⟨7018⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨8, by decide⟩
theorem decode_7020 : decode runtimeBytecode ⟨7020⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨9, by decide⟩
theorem decode_7021 : decode runtimeBytecode ⟨7021⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7030⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨10, by decide⟩
theorem decode_7024 : decode runtimeBytecode ⟨7024⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨11, by decide⟩
theorem decode_7025 : decode runtimeBytecode ⟨7025⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨12, by decide⟩
theorem decode_7026 : decode runtimeBytecode ⟨7026⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨13, by decide⟩
theorem decode_7029 : decode runtimeBytecode ⟨7029⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨14, by decide⟩
theorem decode_7030 : decode runtimeBytecode ⟨7030⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨15, by decide⟩
theorem decode_7031 : decode runtimeBytecode ⟨7031⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨16, by decide⟩
theorem decode_7032 : decode runtimeBytecode ⟨7032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨17, by decide⟩
theorem decode_7033 : decode runtimeBytecode ⟨7033⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨18, by decide⟩
theorem decode_7035 : decode runtimeBytecode ⟨7035⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨19, by decide⟩
theorem decode_7036 : decode runtimeBytecode ⟨7036⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨20, by decide⟩
theorem decode_7039 : decode runtimeBytecode ⟨7039⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨21, by decide⟩
theorem decode_7040 : decode runtimeBytecode ⟨7040⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨22, by decide⟩
theorem decode_7041 : decode runtimeBytecode ⟨7041⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨23, by decide⟩
theorem decode_7042 : decode runtimeBytecode ⟨7042⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨24, by decide⟩
theorem decode_7043 : decode runtimeBytecode ⟨7043⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨25, by decide⟩
theorem decode_7044 : decode runtimeBytecode ⟨7044⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨26, by decide⟩
theorem decode_7045 : decode runtimeBytecode ⟨7045⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨27, by decide⟩
theorem decode_7046 : decode runtimeBytecode ⟨7046⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨28, by decide⟩
theorem decode_7049 : decode runtimeBytecode ⟨7049⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨29, by decide⟩
theorem decode_7050 : decode runtimeBytecode ⟨7050⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨30, by decide⟩
theorem decode_7051 : decode runtimeBytecode ⟨7051⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨31, by decide⟩
theorem decode_7052 : decode runtimeBytecode ⟨7052⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨32, by decide⟩
theorem decode_7053 : decode runtimeBytecode ⟨7053⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨33, by decide⟩
theorem decode_7054 : decode runtimeBytecode ⟨7054⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨34, by decide⟩
theorem decode_7056 : decode runtimeBytecode ⟨7056⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨35, by decide⟩
theorem decode_7057 : decode runtimeBytecode ⟨7057⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨36, by decide⟩
theorem decode_7060 : decode runtimeBytecode ⟨7060⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨37, by decide⟩
theorem decode_7061 : decode runtimeBytecode ⟨7061⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨38, by decide⟩
theorem decode_7062 : decode runtimeBytecode ⟨7062⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨39, by decide⟩
theorem decode_7063 : decode runtimeBytecode ⟨7063⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨40, by decide⟩
theorem decode_7064 : decode runtimeBytecode ⟨7064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨41, by decide⟩
theorem decode_7065 : decode runtimeBytecode ⟨7065⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨42, by decide⟩
theorem decode_7067 : decode runtimeBytecode ⟨7067⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨43, by decide⟩
theorem decode_7068 : decode runtimeBytecode ⟨7068⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨44, by decide⟩
theorem decode_7071 : decode runtimeBytecode ⟨7071⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨45, by decide⟩
theorem decode_7072 : decode runtimeBytecode ⟨7072⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨46, by decide⟩
theorem decode_7073 : decode runtimeBytecode ⟨7073⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨47, by decide⟩
theorem decode_7074 : decode runtimeBytecode ⟨7074⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨48, by decide⟩
theorem decode_7075 : decode runtimeBytecode ⟨7075⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨49, by decide⟩
theorem decode_7076 : decode runtimeBytecode ⟨7076⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨50, by decide⟩
theorem decode_7078 : decode runtimeBytecode ⟨7078⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨51, by decide⟩
theorem decode_7079 : decode runtimeBytecode ⟨7079⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨52, by decide⟩
theorem decode_7082 : decode runtimeBytecode ⟨7082⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨53, by decide⟩
theorem decode_7083 : decode runtimeBytecode ⟨7083⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨54, by decide⟩
theorem decode_7084 : decode runtimeBytecode ⟨7084⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨55, by decide⟩
theorem decode_7085 : decode runtimeBytecode ⟨7085⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨56, by decide⟩
theorem decode_7086 : decode runtimeBytecode ⟨7086⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨57, by decide⟩
theorem decode_7087 : decode runtimeBytecode ⟨7087⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨58, by decide⟩
theorem decode_7089 : decode runtimeBytecode ⟨7089⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨59, by decide⟩
theorem decode_7090 : decode runtimeBytecode ⟨7090⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨60, by decide⟩
theorem decode_7093 : decode runtimeBytecode ⟨7093⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨61, by decide⟩
theorem decode_7094 : decode runtimeBytecode ⟨7094⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨62, by decide⟩
theorem decode_7095 : decode runtimeBytecode ⟨7095⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨63, by decide⟩
theorem decode_7096 : decode runtimeBytecode ⟨7096⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨64, by decide⟩
theorem decode_7097 : decode runtimeBytecode ⟨7097⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨65, by decide⟩
theorem decode_7098 : decode runtimeBytecode ⟨7098⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨66, by decide⟩
theorem decode_7100 : decode runtimeBytecode ⟨7100⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨67, by decide⟩
theorem decode_7101 : decode runtimeBytecode ⟨7101⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨68, by decide⟩
theorem decode_7104 : decode runtimeBytecode ⟨7104⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨69, by decide⟩
theorem decode_7105 : decode runtimeBytecode ⟨7105⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨70, by decide⟩
theorem decode_7106 : decode runtimeBytecode ⟨7106⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨71, by decide⟩
theorem decode_7107 : decode runtimeBytecode ⟨7107⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨72, by decide⟩
theorem decode_7108 : decode runtimeBytecode ⟨7108⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨73, by decide⟩
theorem decode_7109 : decode runtimeBytecode ⟨7109⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨74, by decide⟩
theorem decode_7111 : decode runtimeBytecode ⟨7111⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨75, by decide⟩
theorem decode_7112 : decode runtimeBytecode ⟨7112⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨76, by decide⟩
theorem decode_7115 : decode runtimeBytecode ⟨7115⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨77, by decide⟩
theorem decode_7116 : decode runtimeBytecode ⟨7116⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨78, by decide⟩
theorem decode_7117 : decode runtimeBytecode ⟨7117⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨79, by decide⟩
theorem decode_7118 : decode runtimeBytecode ⟨7118⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨80, by decide⟩
theorem decode_7119 : decode runtimeBytecode ⟨7119⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨81, by decide⟩
theorem decode_7120 : decode runtimeBytecode ⟨7120⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨82, by decide⟩
theorem decode_7121 : decode runtimeBytecode ⟨7121⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨83, by decide⟩
theorem decode_7122 : decode runtimeBytecode ⟨7122⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨84, by decide⟩
theorem decode_7125 : decode runtimeBytecode ⟨7125⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨85, by decide⟩
theorem decode_7126 : decode runtimeBytecode ⟨7126⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨86, by decide⟩
theorem decode_7127 : decode runtimeBytecode ⟨7127⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨87, by decide⟩
theorem decode_7128 : decode runtimeBytecode ⟨7128⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨88, by decide⟩
theorem decode_7129 : decode runtimeBytecode ⟨7129⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨89, by decide⟩
theorem decode_7130 : decode runtimeBytecode ⟨7130⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨90, by decide⟩
theorem decode_7132 : decode runtimeBytecode ⟨7132⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨91, by decide⟩
theorem decode_7133 : decode runtimeBytecode ⟨7133⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7025⟩, 2)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨92, by decide⟩
theorem decode_7136 : decode runtimeBytecode ⟨7136⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨93, by decide⟩
theorem decode_7137 : decode runtimeBytecode ⟨7137⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨94, by decide⟩
theorem decode_7138 : decode runtimeBytecode ⟨7138⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨95, by decide⟩
theorem decode_7139 : decode runtimeBytecode ⟨7139⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨96, by decide⟩
theorem decode_7140 : decode runtimeBytecode ⟨7140⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨97, by decide⟩
theorem decode_7141 : decode runtimeBytecode ⟨7141⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨98, by decide⟩
theorem decode_7143 : decode runtimeBytecode ⟨7143⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes51] using generatedDecodes51_correct ⟨99, by decide⟩

end Ripemd160Old
