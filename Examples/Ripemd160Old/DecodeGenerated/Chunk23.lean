import Examples.Ripemd160Old.DecodeGenerated.Chunk22

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes23 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3276⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3277⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3278⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3279⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3280⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3281⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3283⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3284⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3287⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3288⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3289⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3290⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3291⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3292⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3294⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3295⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3298⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3299⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3300⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3301⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3302⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3303⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3305⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3306⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3309⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3310⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3311⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3312⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3313⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3314⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3316⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3317⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3320⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3321⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3322⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3323⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3324⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3325⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3327⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3328⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3331⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3332⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3333⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3334⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3335⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3336⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3337⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3338⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3341⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3342⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3343⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3344⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3345⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3346⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨3347⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3348⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3351⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3352⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3353⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3354⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3355⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3356⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3358⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3359⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3362⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3363⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3364⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3365⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3366⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3367⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3369⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3370⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3373⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3374⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3375⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3376⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3377⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3378⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3380⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3381⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2))),
  (⟨3384⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3385⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3386⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨3388⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3389⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨3390⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3391⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3392⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3393⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3682⟩, 2))),
  (⟨3396⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3397⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3398⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3400⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3401⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3672⟩, 2))),
  (⟨3404⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3405⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3406⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3408⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3409⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3661⟩, 2))),
  (⟨3412⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none))
]

private theorem generatedDecodes23_correct : ∀ i : Fin generatedDecodes23.size,
    decode runtimeBytecode generatedDecodes23[i].1 = generatedDecodes23[i].2 := by
  native_decide

theorem decode_3276 : decode runtimeBytecode ⟨3276⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨0, by decide⟩
theorem decode_3277 : decode runtimeBytecode ⟨3277⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨1, by decide⟩
theorem decode_3278 : decode runtimeBytecode ⟨3278⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨2, by decide⟩
theorem decode_3279 : decode runtimeBytecode ⟨3279⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨3, by decide⟩
theorem decode_3280 : decode runtimeBytecode ⟨3280⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨4, by decide⟩
theorem decode_3281 : decode runtimeBytecode ⟨3281⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨5, by decide⟩
theorem decode_3283 : decode runtimeBytecode ⟨3283⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨6, by decide⟩
theorem decode_3284 : decode runtimeBytecode ⟨3284⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨7, by decide⟩
theorem decode_3287 : decode runtimeBytecode ⟨3287⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨8, by decide⟩
theorem decode_3288 : decode runtimeBytecode ⟨3288⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨9, by decide⟩
theorem decode_3289 : decode runtimeBytecode ⟨3289⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨10, by decide⟩
theorem decode_3290 : decode runtimeBytecode ⟨3290⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨11, by decide⟩
theorem decode_3291 : decode runtimeBytecode ⟨3291⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨12, by decide⟩
theorem decode_3292 : decode runtimeBytecode ⟨3292⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨13, by decide⟩
theorem decode_3294 : decode runtimeBytecode ⟨3294⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨14, by decide⟩
theorem decode_3295 : decode runtimeBytecode ⟨3295⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨15, by decide⟩
theorem decode_3298 : decode runtimeBytecode ⟨3298⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨16, by decide⟩
theorem decode_3299 : decode runtimeBytecode ⟨3299⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨17, by decide⟩
theorem decode_3300 : decode runtimeBytecode ⟨3300⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨18, by decide⟩
theorem decode_3301 : decode runtimeBytecode ⟨3301⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨19, by decide⟩
theorem decode_3302 : decode runtimeBytecode ⟨3302⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨20, by decide⟩
theorem decode_3303 : decode runtimeBytecode ⟨3303⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨21, by decide⟩
theorem decode_3305 : decode runtimeBytecode ⟨3305⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨22, by decide⟩
theorem decode_3306 : decode runtimeBytecode ⟨3306⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨23, by decide⟩
theorem decode_3309 : decode runtimeBytecode ⟨3309⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨24, by decide⟩
theorem decode_3310 : decode runtimeBytecode ⟨3310⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨25, by decide⟩
theorem decode_3311 : decode runtimeBytecode ⟨3311⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨26, by decide⟩
theorem decode_3312 : decode runtimeBytecode ⟨3312⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨27, by decide⟩
theorem decode_3313 : decode runtimeBytecode ⟨3313⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨28, by decide⟩
theorem decode_3314 : decode runtimeBytecode ⟨3314⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨29, by decide⟩
theorem decode_3316 : decode runtimeBytecode ⟨3316⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨30, by decide⟩
theorem decode_3317 : decode runtimeBytecode ⟨3317⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨31, by decide⟩
theorem decode_3320 : decode runtimeBytecode ⟨3320⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨32, by decide⟩
theorem decode_3321 : decode runtimeBytecode ⟨3321⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨33, by decide⟩
theorem decode_3322 : decode runtimeBytecode ⟨3322⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨34, by decide⟩
theorem decode_3323 : decode runtimeBytecode ⟨3323⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨35, by decide⟩
theorem decode_3324 : decode runtimeBytecode ⟨3324⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨36, by decide⟩
theorem decode_3325 : decode runtimeBytecode ⟨3325⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨37, by decide⟩
theorem decode_3327 : decode runtimeBytecode ⟨3327⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨38, by decide⟩
theorem decode_3328 : decode runtimeBytecode ⟨3328⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨39, by decide⟩
theorem decode_3331 : decode runtimeBytecode ⟨3331⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨40, by decide⟩
theorem decode_3332 : decode runtimeBytecode ⟨3332⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨41, by decide⟩
theorem decode_3333 : decode runtimeBytecode ⟨3333⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨42, by decide⟩
theorem decode_3334 : decode runtimeBytecode ⟨3334⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨43, by decide⟩
theorem decode_3335 : decode runtimeBytecode ⟨3335⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨44, by decide⟩
theorem decode_3336 : decode runtimeBytecode ⟨3336⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨45, by decide⟩
theorem decode_3337 : decode runtimeBytecode ⟨3337⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨46, by decide⟩
theorem decode_3338 : decode runtimeBytecode ⟨3338⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨47, by decide⟩
theorem decode_3341 : decode runtimeBytecode ⟨3341⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨48, by decide⟩
theorem decode_3342 : decode runtimeBytecode ⟨3342⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨49, by decide⟩
theorem decode_3343 : decode runtimeBytecode ⟨3343⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨50, by decide⟩
theorem decode_3344 : decode runtimeBytecode ⟨3344⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨51, by decide⟩
theorem decode_3345 : decode runtimeBytecode ⟨3345⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨52, by decide⟩
theorem decode_3346 : decode runtimeBytecode ⟨3346⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨53, by decide⟩
theorem decode_3347 : decode runtimeBytecode ⟨3347⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨54, by decide⟩
theorem decode_3348 : decode runtimeBytecode ⟨3348⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨55, by decide⟩
theorem decode_3351 : decode runtimeBytecode ⟨3351⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨56, by decide⟩
theorem decode_3352 : decode runtimeBytecode ⟨3352⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨57, by decide⟩
theorem decode_3353 : decode runtimeBytecode ⟨3353⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨58, by decide⟩
theorem decode_3354 : decode runtimeBytecode ⟨3354⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨59, by decide⟩
theorem decode_3355 : decode runtimeBytecode ⟨3355⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨60, by decide⟩
theorem decode_3356 : decode runtimeBytecode ⟨3356⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨61, by decide⟩
theorem decode_3358 : decode runtimeBytecode ⟨3358⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨62, by decide⟩
theorem decode_3359 : decode runtimeBytecode ⟨3359⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨63, by decide⟩
theorem decode_3362 : decode runtimeBytecode ⟨3362⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨64, by decide⟩
theorem decode_3363 : decode runtimeBytecode ⟨3363⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨65, by decide⟩
theorem decode_3364 : decode runtimeBytecode ⟨3364⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨66, by decide⟩
theorem decode_3365 : decode runtimeBytecode ⟨3365⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨67, by decide⟩
theorem decode_3366 : decode runtimeBytecode ⟨3366⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨68, by decide⟩
theorem decode_3367 : decode runtimeBytecode ⟨3367⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨69, by decide⟩
theorem decode_3369 : decode runtimeBytecode ⟨3369⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨70, by decide⟩
theorem decode_3370 : decode runtimeBytecode ⟨3370⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨71, by decide⟩
theorem decode_3373 : decode runtimeBytecode ⟨3373⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨72, by decide⟩
theorem decode_3374 : decode runtimeBytecode ⟨3374⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨73, by decide⟩
theorem decode_3375 : decode runtimeBytecode ⟨3375⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨74, by decide⟩
theorem decode_3376 : decode runtimeBytecode ⟨3376⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨75, by decide⟩
theorem decode_3377 : decode runtimeBytecode ⟨3377⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨76, by decide⟩
theorem decode_3378 : decode runtimeBytecode ⟨3378⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨77, by decide⟩
theorem decode_3380 : decode runtimeBytecode ⟨3380⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨78, by decide⟩
theorem decode_3381 : decode runtimeBytecode ⟨3381⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3207⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨79, by decide⟩
theorem decode_3384 : decode runtimeBytecode ⟨3384⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨80, by decide⟩
theorem decode_3385 : decode runtimeBytecode ⟨3385⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨81, by decide⟩
theorem decode_3386 : decode runtimeBytecode ⟨3386⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨82, by decide⟩
theorem decode_3388 : decode runtimeBytecode ⟨3388⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨83, by decide⟩
theorem decode_3389 : decode runtimeBytecode ⟨3389⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨84, by decide⟩
theorem decode_3390 : decode runtimeBytecode ⟨3390⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨85, by decide⟩
theorem decode_3391 : decode runtimeBytecode ⟨3391⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨86, by decide⟩
theorem decode_3392 : decode runtimeBytecode ⟨3392⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨87, by decide⟩
theorem decode_3393 : decode runtimeBytecode ⟨3393⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3682⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨88, by decide⟩
theorem decode_3396 : decode runtimeBytecode ⟨3396⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨89, by decide⟩
theorem decode_3397 : decode runtimeBytecode ⟨3397⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨90, by decide⟩
theorem decode_3398 : decode runtimeBytecode ⟨3398⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨91, by decide⟩
theorem decode_3400 : decode runtimeBytecode ⟨3400⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨92, by decide⟩
theorem decode_3401 : decode runtimeBytecode ⟨3401⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3672⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨93, by decide⟩
theorem decode_3404 : decode runtimeBytecode ⟨3404⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨94, by decide⟩
theorem decode_3405 : decode runtimeBytecode ⟨3405⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨95, by decide⟩
theorem decode_3406 : decode runtimeBytecode ⟨3406⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨96, by decide⟩
theorem decode_3408 : decode runtimeBytecode ⟨3408⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨97, by decide⟩
theorem decode_3409 : decode runtimeBytecode ⟨3409⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3661⟩, 2)) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨98, by decide⟩
theorem decode_3412 : decode runtimeBytecode ⟨3412⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes23] using generatedDecodes23_correct ⟨99, by decide⟩

end Ripemd160Old
