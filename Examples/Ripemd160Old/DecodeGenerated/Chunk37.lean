import Examples.Ripemd160Old.DecodeGenerated.Chunk36

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes37 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5166⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5167⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5168⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5171⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5172⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5173⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5174⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5175⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5176⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5177⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5178⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5179⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5180⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5182⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5183⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5184⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5185⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5186⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5187⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5190⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5191⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5192⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5193⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5194⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5195⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5196⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5197⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5198⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5199⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨5201⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5202⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5203⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5204⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5205⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5206⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5209⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5210⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5211⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5212⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5213⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5214⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5215⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5216⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5217⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5218⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨5220⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5221⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5222⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5223⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5224⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5225⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5228⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5229⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5230⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5231⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5232⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5233⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5234⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5235⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5236⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5237⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨5239⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5240⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5241⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5242⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5243⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5244⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5247⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5248⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5249⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5250⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨5252⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5253⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5254⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨5255⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5256⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨5257⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5258⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨5259⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5260⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5675⟩, 2))),
  (⟨5263⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5264⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5265⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨5267⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5268⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5656⟩, 2))),
  (⟨5271⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5272⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5273⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨5275⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5276⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5637⟩, 2))),
  (⟨5279⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5280⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5281⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨5283⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5284⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5618⟩, 2))),
  (⟨5287⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5288⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨5289⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨5291⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5292⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5599⟩, 2)))
]

private theorem generatedDecodes37_correct : ∀ i : Fin generatedDecodes37.size,
    decode runtimeBytecode generatedDecodes37[i].1 = generatedDecodes37[i].2 := by
  native_decide

theorem decode_5166 : decode runtimeBytecode ⟨5166⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨0, by decide⟩
theorem decode_5167 : decode runtimeBytecode ⟨5167⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨1, by decide⟩
theorem decode_5168 : decode runtimeBytecode ⟨5168⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨2, by decide⟩
theorem decode_5171 : decode runtimeBytecode ⟨5171⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨3, by decide⟩
theorem decode_5172 : decode runtimeBytecode ⟨5172⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨4, by decide⟩
theorem decode_5173 : decode runtimeBytecode ⟨5173⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨5, by decide⟩
theorem decode_5174 : decode runtimeBytecode ⟨5174⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨6, by decide⟩
theorem decode_5175 : decode runtimeBytecode ⟨5175⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨7, by decide⟩
theorem decode_5176 : decode runtimeBytecode ⟨5176⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨8, by decide⟩
theorem decode_5177 : decode runtimeBytecode ⟨5177⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨9, by decide⟩
theorem decode_5178 : decode runtimeBytecode ⟨5178⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨10, by decide⟩
theorem decode_5179 : decode runtimeBytecode ⟨5179⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨11, by decide⟩
theorem decode_5180 : decode runtimeBytecode ⟨5180⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨12, by decide⟩
theorem decode_5182 : decode runtimeBytecode ⟨5182⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨13, by decide⟩
theorem decode_5183 : decode runtimeBytecode ⟨5183⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨14, by decide⟩
theorem decode_5184 : decode runtimeBytecode ⟨5184⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨15, by decide⟩
theorem decode_5185 : decode runtimeBytecode ⟨5185⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨16, by decide⟩
theorem decode_5186 : decode runtimeBytecode ⟨5186⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨17, by decide⟩
theorem decode_5187 : decode runtimeBytecode ⟨5187⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨18, by decide⟩
theorem decode_5190 : decode runtimeBytecode ⟨5190⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨19, by decide⟩
theorem decode_5191 : decode runtimeBytecode ⟨5191⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨20, by decide⟩
theorem decode_5192 : decode runtimeBytecode ⟨5192⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨21, by decide⟩
theorem decode_5193 : decode runtimeBytecode ⟨5193⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨22, by decide⟩
theorem decode_5194 : decode runtimeBytecode ⟨5194⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨23, by decide⟩
theorem decode_5195 : decode runtimeBytecode ⟨5195⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨24, by decide⟩
theorem decode_5196 : decode runtimeBytecode ⟨5196⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨25, by decide⟩
theorem decode_5197 : decode runtimeBytecode ⟨5197⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨26, by decide⟩
theorem decode_5198 : decode runtimeBytecode ⟨5198⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨27, by decide⟩
theorem decode_5199 : decode runtimeBytecode ⟨5199⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨28, by decide⟩
theorem decode_5201 : decode runtimeBytecode ⟨5201⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨29, by decide⟩
theorem decode_5202 : decode runtimeBytecode ⟨5202⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨30, by decide⟩
theorem decode_5203 : decode runtimeBytecode ⟨5203⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨31, by decide⟩
theorem decode_5204 : decode runtimeBytecode ⟨5204⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨32, by decide⟩
theorem decode_5205 : decode runtimeBytecode ⟨5205⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨33, by decide⟩
theorem decode_5206 : decode runtimeBytecode ⟨5206⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨34, by decide⟩
theorem decode_5209 : decode runtimeBytecode ⟨5209⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨35, by decide⟩
theorem decode_5210 : decode runtimeBytecode ⟨5210⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨36, by decide⟩
theorem decode_5211 : decode runtimeBytecode ⟨5211⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨37, by decide⟩
theorem decode_5212 : decode runtimeBytecode ⟨5212⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨38, by decide⟩
theorem decode_5213 : decode runtimeBytecode ⟨5213⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨39, by decide⟩
theorem decode_5214 : decode runtimeBytecode ⟨5214⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨40, by decide⟩
theorem decode_5215 : decode runtimeBytecode ⟨5215⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨41, by decide⟩
theorem decode_5216 : decode runtimeBytecode ⟨5216⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨42, by decide⟩
theorem decode_5217 : decode runtimeBytecode ⟨5217⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨43, by decide⟩
theorem decode_5218 : decode runtimeBytecode ⟨5218⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨44, by decide⟩
theorem decode_5220 : decode runtimeBytecode ⟨5220⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨45, by decide⟩
theorem decode_5221 : decode runtimeBytecode ⟨5221⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨46, by decide⟩
theorem decode_5222 : decode runtimeBytecode ⟨5222⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨47, by decide⟩
theorem decode_5223 : decode runtimeBytecode ⟨5223⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨48, by decide⟩
theorem decode_5224 : decode runtimeBytecode ⟨5224⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨49, by decide⟩
theorem decode_5225 : decode runtimeBytecode ⟨5225⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨50, by decide⟩
theorem decode_5228 : decode runtimeBytecode ⟨5228⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨51, by decide⟩
theorem decode_5229 : decode runtimeBytecode ⟨5229⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨52, by decide⟩
theorem decode_5230 : decode runtimeBytecode ⟨5230⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨53, by decide⟩
theorem decode_5231 : decode runtimeBytecode ⟨5231⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨54, by decide⟩
theorem decode_5232 : decode runtimeBytecode ⟨5232⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨55, by decide⟩
theorem decode_5233 : decode runtimeBytecode ⟨5233⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨56, by decide⟩
theorem decode_5234 : decode runtimeBytecode ⟨5234⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨57, by decide⟩
theorem decode_5235 : decode runtimeBytecode ⟨5235⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨58, by decide⟩
theorem decode_5236 : decode runtimeBytecode ⟨5236⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨59, by decide⟩
theorem decode_5237 : decode runtimeBytecode ⟨5237⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨60, by decide⟩
theorem decode_5239 : decode runtimeBytecode ⟨5239⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨61, by decide⟩
theorem decode_5240 : decode runtimeBytecode ⟨5240⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨62, by decide⟩
theorem decode_5241 : decode runtimeBytecode ⟨5241⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨63, by decide⟩
theorem decode_5242 : decode runtimeBytecode ⟨5242⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨64, by decide⟩
theorem decode_5243 : decode runtimeBytecode ⟨5243⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨65, by decide⟩
theorem decode_5244 : decode runtimeBytecode ⟨5244⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨66, by decide⟩
theorem decode_5247 : decode runtimeBytecode ⟨5247⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨67, by decide⟩
theorem decode_5248 : decode runtimeBytecode ⟨5248⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨68, by decide⟩
theorem decode_5249 : decode runtimeBytecode ⟨5249⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨69, by decide⟩
theorem decode_5250 : decode runtimeBytecode ⟨5250⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨70, by decide⟩
theorem decode_5252 : decode runtimeBytecode ⟨5252⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨71, by decide⟩
theorem decode_5253 : decode runtimeBytecode ⟨5253⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨72, by decide⟩
theorem decode_5254 : decode runtimeBytecode ⟨5254⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨73, by decide⟩
theorem decode_5255 : decode runtimeBytecode ⟨5255⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨74, by decide⟩
theorem decode_5256 : decode runtimeBytecode ⟨5256⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨75, by decide⟩
theorem decode_5257 : decode runtimeBytecode ⟨5257⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨76, by decide⟩
theorem decode_5258 : decode runtimeBytecode ⟨5258⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨77, by decide⟩
theorem decode_5259 : decode runtimeBytecode ⟨5259⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨78, by decide⟩
theorem decode_5260 : decode runtimeBytecode ⟨5260⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5675⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨79, by decide⟩
theorem decode_5263 : decode runtimeBytecode ⟨5263⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨80, by decide⟩
theorem decode_5264 : decode runtimeBytecode ⟨5264⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨81, by decide⟩
theorem decode_5265 : decode runtimeBytecode ⟨5265⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨82, by decide⟩
theorem decode_5267 : decode runtimeBytecode ⟨5267⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨83, by decide⟩
theorem decode_5268 : decode runtimeBytecode ⟨5268⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5656⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨84, by decide⟩
theorem decode_5271 : decode runtimeBytecode ⟨5271⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨85, by decide⟩
theorem decode_5272 : decode runtimeBytecode ⟨5272⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨86, by decide⟩
theorem decode_5273 : decode runtimeBytecode ⟨5273⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨87, by decide⟩
theorem decode_5275 : decode runtimeBytecode ⟨5275⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨88, by decide⟩
theorem decode_5276 : decode runtimeBytecode ⟨5276⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5637⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨89, by decide⟩
theorem decode_5279 : decode runtimeBytecode ⟨5279⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨90, by decide⟩
theorem decode_5280 : decode runtimeBytecode ⟨5280⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨91, by decide⟩
theorem decode_5281 : decode runtimeBytecode ⟨5281⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨92, by decide⟩
theorem decode_5283 : decode runtimeBytecode ⟨5283⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨93, by decide⟩
theorem decode_5284 : decode runtimeBytecode ⟨5284⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5618⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨94, by decide⟩
theorem decode_5287 : decode runtimeBytecode ⟨5287⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨95, by decide⟩
theorem decode_5288 : decode runtimeBytecode ⟨5288⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨96, by decide⟩
theorem decode_5289 : decode runtimeBytecode ⟨5289⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨97, by decide⟩
theorem decode_5291 : decode runtimeBytecode ⟨5291⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨98, by decide⟩
theorem decode_5292 : decode runtimeBytecode ⟨5292⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5599⟩, 2)) := by
  simpa [generatedDecodes37] using generatedDecodes37_correct ⟨99, by decide⟩

end Ripemd160Old
