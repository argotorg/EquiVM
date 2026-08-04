import Examples.Ripemd160Old.DecodeGenerated.Chunk21

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes22 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3125⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3321⟩, 2))),
  (⟨3128⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3129⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3130⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3132⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3133⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3310⟩, 2))),
  (⟨3136⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3137⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3138⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3140⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3141⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3299⟩, 2))),
  (⟨3144⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3145⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3146⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3148⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3149⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3288⟩, 2))),
  (⟨3152⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3153⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3154⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3156⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3157⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3277⟩, 2))),
  (⟨3160⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3161⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨3162⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3163⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3164⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3266⟩, 2))),
  (⟨3167⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3168⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3169⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3171⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3172⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3255⟩, 2))),
  (⟨3175⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3176⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3177⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3179⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3180⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3244⟩, 2))),
  (⟨3183⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3184⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3185⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3187⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3188⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3233⟩, 2))),
  (⟨3191⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3192⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3193⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨3195⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3196⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3222⟩, 2))),
  (⟨3199⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3200⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3202⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3203⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3212⟩, 2))),
  (⟨3206⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3207⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3208⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨444⟩, 2))),
  (⟨3211⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3212⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3213⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3214⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3215⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3217⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3218⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3221⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3222⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3223⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3224⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3225⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3226⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3228⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3229⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3232⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3233⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3234⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3235⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3236⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3237⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3239⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3240⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3243⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3244⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3245⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3246⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3247⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3248⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨3250⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3251⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3254⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3255⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3256⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3257⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3258⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3259⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3261⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3262⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3265⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3266⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3267⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3268⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3269⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3270⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3272⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3273⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)))
]

private theorem generatedDecodes22_correct : ∀ i : Fin generatedDecodes22.size,
    decode runtimeBytecode generatedDecodes22[i].1 = generatedDecodes22[i].2 := by
  native_decide

theorem decode_3125 : decode runtimeBytecode ⟨3125⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3321⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨0, by decide⟩
theorem decode_3128 : decode runtimeBytecode ⟨3128⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨1, by decide⟩
theorem decode_3129 : decode runtimeBytecode ⟨3129⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨2, by decide⟩
theorem decode_3130 : decode runtimeBytecode ⟨3130⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨3, by decide⟩
theorem decode_3132 : decode runtimeBytecode ⟨3132⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨4, by decide⟩
theorem decode_3133 : decode runtimeBytecode ⟨3133⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3310⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨5, by decide⟩
theorem decode_3136 : decode runtimeBytecode ⟨3136⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨6, by decide⟩
theorem decode_3137 : decode runtimeBytecode ⟨3137⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨7, by decide⟩
theorem decode_3138 : decode runtimeBytecode ⟨3138⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨8, by decide⟩
theorem decode_3140 : decode runtimeBytecode ⟨3140⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨9, by decide⟩
theorem decode_3141 : decode runtimeBytecode ⟨3141⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3299⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨10, by decide⟩
theorem decode_3144 : decode runtimeBytecode ⟨3144⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨11, by decide⟩
theorem decode_3145 : decode runtimeBytecode ⟨3145⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨12, by decide⟩
theorem decode_3146 : decode runtimeBytecode ⟨3146⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨13, by decide⟩
theorem decode_3148 : decode runtimeBytecode ⟨3148⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨14, by decide⟩
theorem decode_3149 : decode runtimeBytecode ⟨3149⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3288⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨15, by decide⟩
theorem decode_3152 : decode runtimeBytecode ⟨3152⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨16, by decide⟩
theorem decode_3153 : decode runtimeBytecode ⟨3153⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨17, by decide⟩
theorem decode_3154 : decode runtimeBytecode ⟨3154⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨18, by decide⟩
theorem decode_3156 : decode runtimeBytecode ⟨3156⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨19, by decide⟩
theorem decode_3157 : decode runtimeBytecode ⟨3157⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3277⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨20, by decide⟩
theorem decode_3160 : decode runtimeBytecode ⟨3160⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨21, by decide⟩
theorem decode_3161 : decode runtimeBytecode ⟨3161⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨22, by decide⟩
theorem decode_3162 : decode runtimeBytecode ⟨3162⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨23, by decide⟩
theorem decode_3163 : decode runtimeBytecode ⟨3163⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨24, by decide⟩
theorem decode_3164 : decode runtimeBytecode ⟨3164⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3266⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨25, by decide⟩
theorem decode_3167 : decode runtimeBytecode ⟨3167⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨26, by decide⟩
theorem decode_3168 : decode runtimeBytecode ⟨3168⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨27, by decide⟩
theorem decode_3169 : decode runtimeBytecode ⟨3169⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨28, by decide⟩
theorem decode_3171 : decode runtimeBytecode ⟨3171⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨29, by decide⟩
theorem decode_3172 : decode runtimeBytecode ⟨3172⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3255⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨30, by decide⟩
theorem decode_3175 : decode runtimeBytecode ⟨3175⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨31, by decide⟩
theorem decode_3176 : decode runtimeBytecode ⟨3176⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨32, by decide⟩
theorem decode_3177 : decode runtimeBytecode ⟨3177⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨33, by decide⟩
theorem decode_3179 : decode runtimeBytecode ⟨3179⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨34, by decide⟩
theorem decode_3180 : decode runtimeBytecode ⟨3180⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3244⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨35, by decide⟩
theorem decode_3183 : decode runtimeBytecode ⟨3183⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨36, by decide⟩
theorem decode_3184 : decode runtimeBytecode ⟨3184⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨37, by decide⟩
theorem decode_3185 : decode runtimeBytecode ⟨3185⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨38, by decide⟩
theorem decode_3187 : decode runtimeBytecode ⟨3187⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨39, by decide⟩
theorem decode_3188 : decode runtimeBytecode ⟨3188⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3233⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨40, by decide⟩
theorem decode_3191 : decode runtimeBytecode ⟨3191⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨41, by decide⟩
theorem decode_3192 : decode runtimeBytecode ⟨3192⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨42, by decide⟩
theorem decode_3193 : decode runtimeBytecode ⟨3193⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨43, by decide⟩
theorem decode_3195 : decode runtimeBytecode ⟨3195⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨44, by decide⟩
theorem decode_3196 : decode runtimeBytecode ⟨3196⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3222⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨45, by decide⟩
theorem decode_3199 : decode runtimeBytecode ⟨3199⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨46, by decide⟩
theorem decode_3200 : decode runtimeBytecode ⟨3200⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨47, by decide⟩
theorem decode_3202 : decode runtimeBytecode ⟨3202⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨48, by decide⟩
theorem decode_3203 : decode runtimeBytecode ⟨3203⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3212⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨49, by decide⟩
theorem decode_3206 : decode runtimeBytecode ⟨3206⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨50, by decide⟩
theorem decode_3207 : decode runtimeBytecode ⟨3207⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨51, by decide⟩
theorem decode_3208 : decode runtimeBytecode ⟨3208⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨444⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨52, by decide⟩
theorem decode_3211 : decode runtimeBytecode ⟨3211⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨53, by decide⟩
theorem decode_3212 : decode runtimeBytecode ⟨3212⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨54, by decide⟩
theorem decode_3213 : decode runtimeBytecode ⟨3213⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨55, by decide⟩
theorem decode_3214 : decode runtimeBytecode ⟨3214⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨56, by decide⟩
theorem decode_3215 : decode runtimeBytecode ⟨3215⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨57, by decide⟩
theorem decode_3217 : decode runtimeBytecode ⟨3217⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨58, by decide⟩
theorem decode_3218 : decode runtimeBytecode ⟨3218⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨59, by decide⟩
theorem decode_3221 : decode runtimeBytecode ⟨3221⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨60, by decide⟩
theorem decode_3222 : decode runtimeBytecode ⟨3222⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨61, by decide⟩
theorem decode_3223 : decode runtimeBytecode ⟨3223⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨62, by decide⟩
theorem decode_3224 : decode runtimeBytecode ⟨3224⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨63, by decide⟩
theorem decode_3225 : decode runtimeBytecode ⟨3225⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨64, by decide⟩
theorem decode_3226 : decode runtimeBytecode ⟨3226⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨65, by decide⟩
theorem decode_3228 : decode runtimeBytecode ⟨3228⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨66, by decide⟩
theorem decode_3229 : decode runtimeBytecode ⟨3229⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨67, by decide⟩
theorem decode_3232 : decode runtimeBytecode ⟨3232⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨68, by decide⟩
theorem decode_3233 : decode runtimeBytecode ⟨3233⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨69, by decide⟩
theorem decode_3234 : decode runtimeBytecode ⟨3234⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨70, by decide⟩
theorem decode_3235 : decode runtimeBytecode ⟨3235⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨71, by decide⟩
theorem decode_3236 : decode runtimeBytecode ⟨3236⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨72, by decide⟩
theorem decode_3237 : decode runtimeBytecode ⟨3237⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨73, by decide⟩
theorem decode_3239 : decode runtimeBytecode ⟨3239⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨74, by decide⟩
theorem decode_3240 : decode runtimeBytecode ⟨3240⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨75, by decide⟩
theorem decode_3243 : decode runtimeBytecode ⟨3243⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨76, by decide⟩
theorem decode_3244 : decode runtimeBytecode ⟨3244⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨77, by decide⟩
theorem decode_3245 : decode runtimeBytecode ⟨3245⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨78, by decide⟩
theorem decode_3246 : decode runtimeBytecode ⟨3246⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨79, by decide⟩
theorem decode_3247 : decode runtimeBytecode ⟨3247⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨80, by decide⟩
theorem decode_3248 : decode runtimeBytecode ⟨3248⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨81, by decide⟩
theorem decode_3250 : decode runtimeBytecode ⟨3250⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨82, by decide⟩
theorem decode_3251 : decode runtimeBytecode ⟨3251⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨83, by decide⟩
theorem decode_3254 : decode runtimeBytecode ⟨3254⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨84, by decide⟩
theorem decode_3255 : decode runtimeBytecode ⟨3255⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨85, by decide⟩
theorem decode_3256 : decode runtimeBytecode ⟨3256⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨86, by decide⟩
theorem decode_3257 : decode runtimeBytecode ⟨3257⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨87, by decide⟩
theorem decode_3258 : decode runtimeBytecode ⟨3258⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨88, by decide⟩
theorem decode_3259 : decode runtimeBytecode ⟨3259⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨89, by decide⟩
theorem decode_3261 : decode runtimeBytecode ⟨3261⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨90, by decide⟩
theorem decode_3262 : decode runtimeBytecode ⟨3262⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨91, by decide⟩
theorem decode_3265 : decode runtimeBytecode ⟨3265⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨92, by decide⟩
theorem decode_3266 : decode runtimeBytecode ⟨3266⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨93, by decide⟩
theorem decode_3267 : decode runtimeBytecode ⟨3267⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨94, by decide⟩
theorem decode_3268 : decode runtimeBytecode ⟨3268⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨95, by decide⟩
theorem decode_3269 : decode runtimeBytecode ⟨3269⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨96, by decide⟩
theorem decode_3270 : decode runtimeBytecode ⟨3270⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨97, by decide⟩
theorem decode_3272 : decode runtimeBytecode ⟨3272⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨98, by decide⟩
theorem decode_3273 : decode runtimeBytecode ⟨3273⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes22] using generatedDecodes22_correct ⟨99, by decide⟩

end Ripemd160Old
