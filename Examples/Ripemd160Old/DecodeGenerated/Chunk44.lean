import Examples.Ripemd160Old.DecodeGenerated.Chunk43

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes44 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨6060⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6063⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6065⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6066⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6067⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6068⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6069⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6070⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6071⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6072⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨6074⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6075⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6076⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6077⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6078⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6079⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6082⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6083⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6084⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6085⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6086⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6087⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6088⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6089⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6090⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6091⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨6093⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6094⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6095⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6096⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6097⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6098⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6101⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6102⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6103⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6104⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6105⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6106⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6107⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6108⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6109⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6110⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨6112⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6113⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6114⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6115⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6116⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6117⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6120⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6121⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6122⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6123⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6124⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6125⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6126⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6127⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6128⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6129⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨6131⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6132⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6133⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6134⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6135⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6136⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6139⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6140⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6141⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6142⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨6144⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6145⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6146⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨6147⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6148⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨6149⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6150⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨6151⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6152⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6567⟩, 2))),
  (⟨6155⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6156⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6157⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨6159⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6160⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6548⟩, 2))),
  (⟨6163⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6164⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6165⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨6167⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6168⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6529⟩, 2))),
  (⟨6171⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6172⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6173⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨6175⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6176⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6510⟩, 2))),
  (⟨6179⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6180⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6181⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨6183⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6184⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6491⟩, 2))),
  (⟨6187⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6188⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none))
]

private theorem generatedDecodes44_correct : ∀ i : Fin generatedDecodes44.size,
    decode runtimeBytecode generatedDecodes44[i].1 = generatedDecodes44[i].2 := by
  native_decide

theorem decode_6060 : decode runtimeBytecode ⟨6060⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨0, by decide⟩
theorem decode_6063 : decode runtimeBytecode ⟨6063⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨1, by decide⟩
theorem decode_6064 : decode runtimeBytecode ⟨6064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨2, by decide⟩
theorem decode_6065 : decode runtimeBytecode ⟨6065⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨3, by decide⟩
theorem decode_6066 : decode runtimeBytecode ⟨6066⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨4, by decide⟩
theorem decode_6067 : decode runtimeBytecode ⟨6067⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨5, by decide⟩
theorem decode_6068 : decode runtimeBytecode ⟨6068⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨6, by decide⟩
theorem decode_6069 : decode runtimeBytecode ⟨6069⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨7, by decide⟩
theorem decode_6070 : decode runtimeBytecode ⟨6070⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨8, by decide⟩
theorem decode_6071 : decode runtimeBytecode ⟨6071⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨9, by decide⟩
theorem decode_6072 : decode runtimeBytecode ⟨6072⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨10, by decide⟩
theorem decode_6074 : decode runtimeBytecode ⟨6074⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨11, by decide⟩
theorem decode_6075 : decode runtimeBytecode ⟨6075⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨12, by decide⟩
theorem decode_6076 : decode runtimeBytecode ⟨6076⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨13, by decide⟩
theorem decode_6077 : decode runtimeBytecode ⟨6077⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨14, by decide⟩
theorem decode_6078 : decode runtimeBytecode ⟨6078⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨15, by decide⟩
theorem decode_6079 : decode runtimeBytecode ⟨6079⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨16, by decide⟩
theorem decode_6082 : decode runtimeBytecode ⟨6082⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨17, by decide⟩
theorem decode_6083 : decode runtimeBytecode ⟨6083⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨18, by decide⟩
theorem decode_6084 : decode runtimeBytecode ⟨6084⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨19, by decide⟩
theorem decode_6085 : decode runtimeBytecode ⟨6085⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨20, by decide⟩
theorem decode_6086 : decode runtimeBytecode ⟨6086⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨21, by decide⟩
theorem decode_6087 : decode runtimeBytecode ⟨6087⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨22, by decide⟩
theorem decode_6088 : decode runtimeBytecode ⟨6088⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨23, by decide⟩
theorem decode_6089 : decode runtimeBytecode ⟨6089⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨24, by decide⟩
theorem decode_6090 : decode runtimeBytecode ⟨6090⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨25, by decide⟩
theorem decode_6091 : decode runtimeBytecode ⟨6091⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨26, by decide⟩
theorem decode_6093 : decode runtimeBytecode ⟨6093⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨27, by decide⟩
theorem decode_6094 : decode runtimeBytecode ⟨6094⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨28, by decide⟩
theorem decode_6095 : decode runtimeBytecode ⟨6095⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨29, by decide⟩
theorem decode_6096 : decode runtimeBytecode ⟨6096⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨30, by decide⟩
theorem decode_6097 : decode runtimeBytecode ⟨6097⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨31, by decide⟩
theorem decode_6098 : decode runtimeBytecode ⟨6098⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨32, by decide⟩
theorem decode_6101 : decode runtimeBytecode ⟨6101⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨33, by decide⟩
theorem decode_6102 : decode runtimeBytecode ⟨6102⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨34, by decide⟩
theorem decode_6103 : decode runtimeBytecode ⟨6103⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨35, by decide⟩
theorem decode_6104 : decode runtimeBytecode ⟨6104⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨36, by decide⟩
theorem decode_6105 : decode runtimeBytecode ⟨6105⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨37, by decide⟩
theorem decode_6106 : decode runtimeBytecode ⟨6106⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨38, by decide⟩
theorem decode_6107 : decode runtimeBytecode ⟨6107⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨39, by decide⟩
theorem decode_6108 : decode runtimeBytecode ⟨6108⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨40, by decide⟩
theorem decode_6109 : decode runtimeBytecode ⟨6109⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨41, by decide⟩
theorem decode_6110 : decode runtimeBytecode ⟨6110⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨42, by decide⟩
theorem decode_6112 : decode runtimeBytecode ⟨6112⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨43, by decide⟩
theorem decode_6113 : decode runtimeBytecode ⟨6113⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨44, by decide⟩
theorem decode_6114 : decode runtimeBytecode ⟨6114⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨45, by decide⟩
theorem decode_6115 : decode runtimeBytecode ⟨6115⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨46, by decide⟩
theorem decode_6116 : decode runtimeBytecode ⟨6116⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨47, by decide⟩
theorem decode_6117 : decode runtimeBytecode ⟨6117⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨48, by decide⟩
theorem decode_6120 : decode runtimeBytecode ⟨6120⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨49, by decide⟩
theorem decode_6121 : decode runtimeBytecode ⟨6121⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨50, by decide⟩
theorem decode_6122 : decode runtimeBytecode ⟨6122⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨51, by decide⟩
theorem decode_6123 : decode runtimeBytecode ⟨6123⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨52, by decide⟩
theorem decode_6124 : decode runtimeBytecode ⟨6124⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨53, by decide⟩
theorem decode_6125 : decode runtimeBytecode ⟨6125⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨54, by decide⟩
theorem decode_6126 : decode runtimeBytecode ⟨6126⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨55, by decide⟩
theorem decode_6127 : decode runtimeBytecode ⟨6127⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨56, by decide⟩
theorem decode_6128 : decode runtimeBytecode ⟨6128⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨57, by decide⟩
theorem decode_6129 : decode runtimeBytecode ⟨6129⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨58, by decide⟩
theorem decode_6131 : decode runtimeBytecode ⟨6131⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨59, by decide⟩
theorem decode_6132 : decode runtimeBytecode ⟨6132⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨60, by decide⟩
theorem decode_6133 : decode runtimeBytecode ⟨6133⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨61, by decide⟩
theorem decode_6134 : decode runtimeBytecode ⟨6134⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨62, by decide⟩
theorem decode_6135 : decode runtimeBytecode ⟨6135⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨63, by decide⟩
theorem decode_6136 : decode runtimeBytecode ⟨6136⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨64, by decide⟩
theorem decode_6139 : decode runtimeBytecode ⟨6139⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨65, by decide⟩
theorem decode_6140 : decode runtimeBytecode ⟨6140⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨66, by decide⟩
theorem decode_6141 : decode runtimeBytecode ⟨6141⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨67, by decide⟩
theorem decode_6142 : decode runtimeBytecode ⟨6142⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨68, by decide⟩
theorem decode_6144 : decode runtimeBytecode ⟨6144⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨69, by decide⟩
theorem decode_6145 : decode runtimeBytecode ⟨6145⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨70, by decide⟩
theorem decode_6146 : decode runtimeBytecode ⟨6146⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨71, by decide⟩
theorem decode_6147 : decode runtimeBytecode ⟨6147⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨72, by decide⟩
theorem decode_6148 : decode runtimeBytecode ⟨6148⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨73, by decide⟩
theorem decode_6149 : decode runtimeBytecode ⟨6149⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨74, by decide⟩
theorem decode_6150 : decode runtimeBytecode ⟨6150⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨75, by decide⟩
theorem decode_6151 : decode runtimeBytecode ⟨6151⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨76, by decide⟩
theorem decode_6152 : decode runtimeBytecode ⟨6152⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6567⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨77, by decide⟩
theorem decode_6155 : decode runtimeBytecode ⟨6155⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨78, by decide⟩
theorem decode_6156 : decode runtimeBytecode ⟨6156⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨79, by decide⟩
theorem decode_6157 : decode runtimeBytecode ⟨6157⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨80, by decide⟩
theorem decode_6159 : decode runtimeBytecode ⟨6159⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨81, by decide⟩
theorem decode_6160 : decode runtimeBytecode ⟨6160⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6548⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨82, by decide⟩
theorem decode_6163 : decode runtimeBytecode ⟨6163⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨83, by decide⟩
theorem decode_6164 : decode runtimeBytecode ⟨6164⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨84, by decide⟩
theorem decode_6165 : decode runtimeBytecode ⟨6165⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨85, by decide⟩
theorem decode_6167 : decode runtimeBytecode ⟨6167⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨86, by decide⟩
theorem decode_6168 : decode runtimeBytecode ⟨6168⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6529⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨87, by decide⟩
theorem decode_6171 : decode runtimeBytecode ⟨6171⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨88, by decide⟩
theorem decode_6172 : decode runtimeBytecode ⟨6172⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨89, by decide⟩
theorem decode_6173 : decode runtimeBytecode ⟨6173⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨90, by decide⟩
theorem decode_6175 : decode runtimeBytecode ⟨6175⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨91, by decide⟩
theorem decode_6176 : decode runtimeBytecode ⟨6176⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6510⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨92, by decide⟩
theorem decode_6179 : decode runtimeBytecode ⟨6179⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨93, by decide⟩
theorem decode_6180 : decode runtimeBytecode ⟨6180⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨94, by decide⟩
theorem decode_6181 : decode runtimeBytecode ⟨6181⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨95, by decide⟩
theorem decode_6183 : decode runtimeBytecode ⟨6183⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨96, by decide⟩
theorem decode_6184 : decode runtimeBytecode ⟨6184⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6491⟩, 2)) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨97, by decide⟩
theorem decode_6187 : decode runtimeBytecode ⟨6187⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨98, by decide⟩
theorem decode_6188 : decode runtimeBytecode ⟨6188⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes44] using generatedDecodes44_correct ⟨99, by decide⟩

end Ripemd160Old
