import Examples.Ripemd160Old.DecodeGenerated.Chunk35

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes36 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5047⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5049⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5050⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5051⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5052⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5053⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5054⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5057⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5058⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5059⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5060⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5061⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5062⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5063⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5064⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5065⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5066⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨5068⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5069⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5070⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5071⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5072⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5073⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5076⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5077⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5078⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5079⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5080⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5081⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5082⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5083⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5084⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5085⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5087⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5088⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5089⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5090⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5091⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5092⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5095⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5096⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5097⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5098⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5099⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5100⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5101⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5102⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5103⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5104⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5106⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5107⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5108⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5109⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5110⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5111⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5114⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5115⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5116⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5117⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5118⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5119⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5120⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5121⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5122⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5123⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5125⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5126⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5127⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5128⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5129⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5130⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5133⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5134⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5135⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5136⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5137⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5138⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5139⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5140⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5141⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5142⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5144⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5145⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5146⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5147⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5148⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5149⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5152⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5153⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5154⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5155⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5156⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5157⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5158⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5159⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5160⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5161⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨5163⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5164⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5165⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none))
]

private theorem generatedDecodes36_correct : ∀ i : Fin generatedDecodes36.size,
    decode runtimeBytecode generatedDecodes36[i].1 = generatedDecodes36[i].2 := by
  native_decide

theorem decode_5047 : decode runtimeBytecode ⟨5047⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨0, by decide⟩
theorem decode_5049 : decode runtimeBytecode ⟨5049⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨1, by decide⟩
theorem decode_5050 : decode runtimeBytecode ⟨5050⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨2, by decide⟩
theorem decode_5051 : decode runtimeBytecode ⟨5051⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨3, by decide⟩
theorem decode_5052 : decode runtimeBytecode ⟨5052⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨4, by decide⟩
theorem decode_5053 : decode runtimeBytecode ⟨5053⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨5, by decide⟩
theorem decode_5054 : decode runtimeBytecode ⟨5054⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨6, by decide⟩
theorem decode_5057 : decode runtimeBytecode ⟨5057⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨7, by decide⟩
theorem decode_5058 : decode runtimeBytecode ⟨5058⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨8, by decide⟩
theorem decode_5059 : decode runtimeBytecode ⟨5059⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨9, by decide⟩
theorem decode_5060 : decode runtimeBytecode ⟨5060⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨10, by decide⟩
theorem decode_5061 : decode runtimeBytecode ⟨5061⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨11, by decide⟩
theorem decode_5062 : decode runtimeBytecode ⟨5062⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨12, by decide⟩
theorem decode_5063 : decode runtimeBytecode ⟨5063⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨13, by decide⟩
theorem decode_5064 : decode runtimeBytecode ⟨5064⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨14, by decide⟩
theorem decode_5065 : decode runtimeBytecode ⟨5065⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨15, by decide⟩
theorem decode_5066 : decode runtimeBytecode ⟨5066⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨16, by decide⟩
theorem decode_5068 : decode runtimeBytecode ⟨5068⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨17, by decide⟩
theorem decode_5069 : decode runtimeBytecode ⟨5069⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨18, by decide⟩
theorem decode_5070 : decode runtimeBytecode ⟨5070⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨19, by decide⟩
theorem decode_5071 : decode runtimeBytecode ⟨5071⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨20, by decide⟩
theorem decode_5072 : decode runtimeBytecode ⟨5072⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨21, by decide⟩
theorem decode_5073 : decode runtimeBytecode ⟨5073⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨22, by decide⟩
theorem decode_5076 : decode runtimeBytecode ⟨5076⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨23, by decide⟩
theorem decode_5077 : decode runtimeBytecode ⟨5077⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨24, by decide⟩
theorem decode_5078 : decode runtimeBytecode ⟨5078⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨25, by decide⟩
theorem decode_5079 : decode runtimeBytecode ⟨5079⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨26, by decide⟩
theorem decode_5080 : decode runtimeBytecode ⟨5080⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨27, by decide⟩
theorem decode_5081 : decode runtimeBytecode ⟨5081⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨28, by decide⟩
theorem decode_5082 : decode runtimeBytecode ⟨5082⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨29, by decide⟩
theorem decode_5083 : decode runtimeBytecode ⟨5083⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨30, by decide⟩
theorem decode_5084 : decode runtimeBytecode ⟨5084⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨31, by decide⟩
theorem decode_5085 : decode runtimeBytecode ⟨5085⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨32, by decide⟩
theorem decode_5087 : decode runtimeBytecode ⟨5087⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨33, by decide⟩
theorem decode_5088 : decode runtimeBytecode ⟨5088⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨34, by decide⟩
theorem decode_5089 : decode runtimeBytecode ⟨5089⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨35, by decide⟩
theorem decode_5090 : decode runtimeBytecode ⟨5090⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨36, by decide⟩
theorem decode_5091 : decode runtimeBytecode ⟨5091⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨37, by decide⟩
theorem decode_5092 : decode runtimeBytecode ⟨5092⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨38, by decide⟩
theorem decode_5095 : decode runtimeBytecode ⟨5095⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨39, by decide⟩
theorem decode_5096 : decode runtimeBytecode ⟨5096⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨40, by decide⟩
theorem decode_5097 : decode runtimeBytecode ⟨5097⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨41, by decide⟩
theorem decode_5098 : decode runtimeBytecode ⟨5098⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨42, by decide⟩
theorem decode_5099 : decode runtimeBytecode ⟨5099⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨43, by decide⟩
theorem decode_5100 : decode runtimeBytecode ⟨5100⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨44, by decide⟩
theorem decode_5101 : decode runtimeBytecode ⟨5101⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨45, by decide⟩
theorem decode_5102 : decode runtimeBytecode ⟨5102⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨46, by decide⟩
theorem decode_5103 : decode runtimeBytecode ⟨5103⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨47, by decide⟩
theorem decode_5104 : decode runtimeBytecode ⟨5104⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨48, by decide⟩
theorem decode_5106 : decode runtimeBytecode ⟨5106⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨49, by decide⟩
theorem decode_5107 : decode runtimeBytecode ⟨5107⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨50, by decide⟩
theorem decode_5108 : decode runtimeBytecode ⟨5108⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨51, by decide⟩
theorem decode_5109 : decode runtimeBytecode ⟨5109⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨52, by decide⟩
theorem decode_5110 : decode runtimeBytecode ⟨5110⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨53, by decide⟩
theorem decode_5111 : decode runtimeBytecode ⟨5111⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨54, by decide⟩
theorem decode_5114 : decode runtimeBytecode ⟨5114⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨55, by decide⟩
theorem decode_5115 : decode runtimeBytecode ⟨5115⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨56, by decide⟩
theorem decode_5116 : decode runtimeBytecode ⟨5116⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨57, by decide⟩
theorem decode_5117 : decode runtimeBytecode ⟨5117⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨58, by decide⟩
theorem decode_5118 : decode runtimeBytecode ⟨5118⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨59, by decide⟩
theorem decode_5119 : decode runtimeBytecode ⟨5119⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨60, by decide⟩
theorem decode_5120 : decode runtimeBytecode ⟨5120⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨61, by decide⟩
theorem decode_5121 : decode runtimeBytecode ⟨5121⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨62, by decide⟩
theorem decode_5122 : decode runtimeBytecode ⟨5122⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨63, by decide⟩
theorem decode_5123 : decode runtimeBytecode ⟨5123⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨64, by decide⟩
theorem decode_5125 : decode runtimeBytecode ⟨5125⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨65, by decide⟩
theorem decode_5126 : decode runtimeBytecode ⟨5126⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨66, by decide⟩
theorem decode_5127 : decode runtimeBytecode ⟨5127⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨67, by decide⟩
theorem decode_5128 : decode runtimeBytecode ⟨5128⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨68, by decide⟩
theorem decode_5129 : decode runtimeBytecode ⟨5129⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨69, by decide⟩
theorem decode_5130 : decode runtimeBytecode ⟨5130⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨70, by decide⟩
theorem decode_5133 : decode runtimeBytecode ⟨5133⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨71, by decide⟩
theorem decode_5134 : decode runtimeBytecode ⟨5134⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨72, by decide⟩
theorem decode_5135 : decode runtimeBytecode ⟨5135⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨73, by decide⟩
theorem decode_5136 : decode runtimeBytecode ⟨5136⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨74, by decide⟩
theorem decode_5137 : decode runtimeBytecode ⟨5137⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨75, by decide⟩
theorem decode_5138 : decode runtimeBytecode ⟨5138⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨76, by decide⟩
theorem decode_5139 : decode runtimeBytecode ⟨5139⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨77, by decide⟩
theorem decode_5140 : decode runtimeBytecode ⟨5140⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨78, by decide⟩
theorem decode_5141 : decode runtimeBytecode ⟨5141⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨79, by decide⟩
theorem decode_5142 : decode runtimeBytecode ⟨5142⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨80, by decide⟩
theorem decode_5144 : decode runtimeBytecode ⟨5144⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨81, by decide⟩
theorem decode_5145 : decode runtimeBytecode ⟨5145⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨82, by decide⟩
theorem decode_5146 : decode runtimeBytecode ⟨5146⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨83, by decide⟩
theorem decode_5147 : decode runtimeBytecode ⟨5147⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨84, by decide⟩
theorem decode_5148 : decode runtimeBytecode ⟨5148⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨85, by decide⟩
theorem decode_5149 : decode runtimeBytecode ⟨5149⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨86, by decide⟩
theorem decode_5152 : decode runtimeBytecode ⟨5152⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨87, by decide⟩
theorem decode_5153 : decode runtimeBytecode ⟨5153⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨88, by decide⟩
theorem decode_5154 : decode runtimeBytecode ⟨5154⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨89, by decide⟩
theorem decode_5155 : decode runtimeBytecode ⟨5155⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨90, by decide⟩
theorem decode_5156 : decode runtimeBytecode ⟨5156⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨91, by decide⟩
theorem decode_5157 : decode runtimeBytecode ⟨5157⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨92, by decide⟩
theorem decode_5158 : decode runtimeBytecode ⟨5158⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨93, by decide⟩
theorem decode_5159 : decode runtimeBytecode ⟨5159⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨94, by decide⟩
theorem decode_5160 : decode runtimeBytecode ⟨5160⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨95, by decide⟩
theorem decode_5161 : decode runtimeBytecode ⟨5161⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨96, by decide⟩
theorem decode_5163 : decode runtimeBytecode ⟨5163⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨97, by decide⟩
theorem decode_5164 : decode runtimeBytecode ⟨5164⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨98, by decide⟩
theorem decode_5165 : decode runtimeBytecode ⟨5165⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes36] using generatedDecodes36_correct ⟨99, by decide⟩

end Ripemd160Old
