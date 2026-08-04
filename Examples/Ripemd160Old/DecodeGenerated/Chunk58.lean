import Examples.Ripemd160Old.DecodeGenerated.Chunk57

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes58 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8014⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨8016⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8017⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8020⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8021⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8022⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8023⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8024⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8025⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨8027⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8028⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8031⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8033⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8034⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8035⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8036⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨8038⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8039⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8042⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8043⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8044⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8045⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8046⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8047⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨8049⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8050⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8053⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8054⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8055⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8056⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8057⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8058⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨8060⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8061⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8065⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8066⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8067⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8068⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8069⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨8071⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8072⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8075⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8076⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8077⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8078⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8079⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8080⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨8082⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8083⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8086⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8087⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8088⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8089⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8090⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8091⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8092⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8093⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8096⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8097⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8098⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8099⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8100⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8101⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨8103⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8104⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8107⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8108⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8109⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8110⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8111⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8112⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨8114⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8115⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8118⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8119⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8120⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8121⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8122⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8123⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨8125⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8126⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8129⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8130⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8131⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8132⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8133⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨8134⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8135⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8136⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨8137⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8138⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨8139⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none)),
  (⟨8140⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8141⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8142⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨8143⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨8144⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨8145⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none))
]

private theorem generatedDecodes58_correct : ∀ i : Fin generatedDecodes58.size,
    decode runtimeBytecode generatedDecodes58[i].1 = generatedDecodes58[i].2 := by
  native_decide

theorem decode_8014 : decode runtimeBytecode ⟨8014⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨0, by decide⟩
theorem decode_8016 : decode runtimeBytecode ⟨8016⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨1, by decide⟩
theorem decode_8017 : decode runtimeBytecode ⟨8017⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨2, by decide⟩
theorem decode_8020 : decode runtimeBytecode ⟨8020⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨3, by decide⟩
theorem decode_8021 : decode runtimeBytecode ⟨8021⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨4, by decide⟩
theorem decode_8022 : decode runtimeBytecode ⟨8022⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨5, by decide⟩
theorem decode_8023 : decode runtimeBytecode ⟨8023⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨6, by decide⟩
theorem decode_8024 : decode runtimeBytecode ⟨8024⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨7, by decide⟩
theorem decode_8025 : decode runtimeBytecode ⟨8025⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨8, by decide⟩
theorem decode_8027 : decode runtimeBytecode ⟨8027⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨9, by decide⟩
theorem decode_8028 : decode runtimeBytecode ⟨8028⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨10, by decide⟩
theorem decode_8031 : decode runtimeBytecode ⟨8031⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨11, by decide⟩
theorem decode_8032 : decode runtimeBytecode ⟨8032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨12, by decide⟩
theorem decode_8033 : decode runtimeBytecode ⟨8033⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨13, by decide⟩
theorem decode_8034 : decode runtimeBytecode ⟨8034⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨14, by decide⟩
theorem decode_8035 : decode runtimeBytecode ⟨8035⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨15, by decide⟩
theorem decode_8036 : decode runtimeBytecode ⟨8036⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨16, by decide⟩
theorem decode_8038 : decode runtimeBytecode ⟨8038⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨17, by decide⟩
theorem decode_8039 : decode runtimeBytecode ⟨8039⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨18, by decide⟩
theorem decode_8042 : decode runtimeBytecode ⟨8042⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨19, by decide⟩
theorem decode_8043 : decode runtimeBytecode ⟨8043⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨20, by decide⟩
theorem decode_8044 : decode runtimeBytecode ⟨8044⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨21, by decide⟩
theorem decode_8045 : decode runtimeBytecode ⟨8045⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨22, by decide⟩
theorem decode_8046 : decode runtimeBytecode ⟨8046⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨23, by decide⟩
theorem decode_8047 : decode runtimeBytecode ⟨8047⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨24, by decide⟩
theorem decode_8049 : decode runtimeBytecode ⟨8049⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨25, by decide⟩
theorem decode_8050 : decode runtimeBytecode ⟨8050⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨26, by decide⟩
theorem decode_8053 : decode runtimeBytecode ⟨8053⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨27, by decide⟩
theorem decode_8054 : decode runtimeBytecode ⟨8054⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨28, by decide⟩
theorem decode_8055 : decode runtimeBytecode ⟨8055⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨29, by decide⟩
theorem decode_8056 : decode runtimeBytecode ⟨8056⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨30, by decide⟩
theorem decode_8057 : decode runtimeBytecode ⟨8057⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨31, by decide⟩
theorem decode_8058 : decode runtimeBytecode ⟨8058⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨32, by decide⟩
theorem decode_8060 : decode runtimeBytecode ⟨8060⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨33, by decide⟩
theorem decode_8061 : decode runtimeBytecode ⟨8061⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨34, by decide⟩
theorem decode_8064 : decode runtimeBytecode ⟨8064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨35, by decide⟩
theorem decode_8065 : decode runtimeBytecode ⟨8065⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨36, by decide⟩
theorem decode_8066 : decode runtimeBytecode ⟨8066⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨37, by decide⟩
theorem decode_8067 : decode runtimeBytecode ⟨8067⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨38, by decide⟩
theorem decode_8068 : decode runtimeBytecode ⟨8068⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨39, by decide⟩
theorem decode_8069 : decode runtimeBytecode ⟨8069⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨40, by decide⟩
theorem decode_8071 : decode runtimeBytecode ⟨8071⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨41, by decide⟩
theorem decode_8072 : decode runtimeBytecode ⟨8072⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨42, by decide⟩
theorem decode_8075 : decode runtimeBytecode ⟨8075⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨43, by decide⟩
theorem decode_8076 : decode runtimeBytecode ⟨8076⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨44, by decide⟩
theorem decode_8077 : decode runtimeBytecode ⟨8077⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨45, by decide⟩
theorem decode_8078 : decode runtimeBytecode ⟨8078⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨46, by decide⟩
theorem decode_8079 : decode runtimeBytecode ⟨8079⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨47, by decide⟩
theorem decode_8080 : decode runtimeBytecode ⟨8080⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨48, by decide⟩
theorem decode_8082 : decode runtimeBytecode ⟨8082⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨49, by decide⟩
theorem decode_8083 : decode runtimeBytecode ⟨8083⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨50, by decide⟩
theorem decode_8086 : decode runtimeBytecode ⟨8086⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨51, by decide⟩
theorem decode_8087 : decode runtimeBytecode ⟨8087⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨52, by decide⟩
theorem decode_8088 : decode runtimeBytecode ⟨8088⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨53, by decide⟩
theorem decode_8089 : decode runtimeBytecode ⟨8089⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨54, by decide⟩
theorem decode_8090 : decode runtimeBytecode ⟨8090⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨55, by decide⟩
theorem decode_8091 : decode runtimeBytecode ⟨8091⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨56, by decide⟩
theorem decode_8092 : decode runtimeBytecode ⟨8092⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨57, by decide⟩
theorem decode_8093 : decode runtimeBytecode ⟨8093⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨58, by decide⟩
theorem decode_8096 : decode runtimeBytecode ⟨8096⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨59, by decide⟩
theorem decode_8097 : decode runtimeBytecode ⟨8097⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨60, by decide⟩
theorem decode_8098 : decode runtimeBytecode ⟨8098⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨61, by decide⟩
theorem decode_8099 : decode runtimeBytecode ⟨8099⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨62, by decide⟩
theorem decode_8100 : decode runtimeBytecode ⟨8100⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨63, by decide⟩
theorem decode_8101 : decode runtimeBytecode ⟨8101⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨64, by decide⟩
theorem decode_8103 : decode runtimeBytecode ⟨8103⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨65, by decide⟩
theorem decode_8104 : decode runtimeBytecode ⟨8104⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨66, by decide⟩
theorem decode_8107 : decode runtimeBytecode ⟨8107⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨67, by decide⟩
theorem decode_8108 : decode runtimeBytecode ⟨8108⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨68, by decide⟩
theorem decode_8109 : decode runtimeBytecode ⟨8109⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨69, by decide⟩
theorem decode_8110 : decode runtimeBytecode ⟨8110⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨70, by decide⟩
theorem decode_8111 : decode runtimeBytecode ⟨8111⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨71, by decide⟩
theorem decode_8112 : decode runtimeBytecode ⟨8112⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨72, by decide⟩
theorem decode_8114 : decode runtimeBytecode ⟨8114⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨73, by decide⟩
theorem decode_8115 : decode runtimeBytecode ⟨8115⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨74, by decide⟩
theorem decode_8118 : decode runtimeBytecode ⟨8118⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨75, by decide⟩
theorem decode_8119 : decode runtimeBytecode ⟨8119⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨76, by decide⟩
theorem decode_8120 : decode runtimeBytecode ⟨8120⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨77, by decide⟩
theorem decode_8121 : decode runtimeBytecode ⟨8121⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨78, by decide⟩
theorem decode_8122 : decode runtimeBytecode ⟨8122⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨79, by decide⟩
theorem decode_8123 : decode runtimeBytecode ⟨8123⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨80, by decide⟩
theorem decode_8125 : decode runtimeBytecode ⟨8125⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨81, by decide⟩
theorem decode_8126 : decode runtimeBytecode ⟨8126⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨82, by decide⟩
theorem decode_8129 : decode runtimeBytecode ⟨8129⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨83, by decide⟩
theorem decode_8130 : decode runtimeBytecode ⟨8130⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨84, by decide⟩
theorem decode_8131 : decode runtimeBytecode ⟨8131⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨85, by decide⟩
theorem decode_8132 : decode runtimeBytecode ⟨8132⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨86, by decide⟩
theorem decode_8133 : decode runtimeBytecode ⟨8133⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨87, by decide⟩
theorem decode_8134 : decode runtimeBytecode ⟨8134⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨88, by decide⟩
theorem decode_8135 : decode runtimeBytecode ⟨8135⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨89, by decide⟩
theorem decode_8136 : decode runtimeBytecode ⟨8136⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨90, by decide⟩
theorem decode_8137 : decode runtimeBytecode ⟨8137⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨91, by decide⟩
theorem decode_8138 : decode runtimeBytecode ⟨8138⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨92, by decide⟩
theorem decode_8139 : decode runtimeBytecode ⟨8139⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.XOR), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨93, by decide⟩
theorem decode_8140 : decode runtimeBytecode ⟨8140⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨94, by decide⟩
theorem decode_8141 : decode runtimeBytecode ⟨8141⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨95, by decide⟩
theorem decode_8142 : decode runtimeBytecode ⟨8142⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨96, by decide⟩
theorem decode_8143 : decode runtimeBytecode ⟨8143⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨97, by decide⟩
theorem decode_8144 : decode runtimeBytecode ⟨8144⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨98, by decide⟩
theorem decode_8145 : decode runtimeBytecode ⟨8145⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes58] using generatedDecodes58_correct ⟨99, by decide⟩

end Ripemd160Old
