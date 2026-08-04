import Examples.Ripemd160Old.DecodeGenerated.Chunk23

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes24 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3413⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3414⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3416⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3417⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3650⟩, 2))),
  (⟨3420⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3421⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3422⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3424⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3425⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3639⟩, 2))),
  (⟨3428⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3429⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3430⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3432⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3433⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3628⟩, 2))),
  (⟨3436⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3437⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3438⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3440⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3441⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3617⟩, 2))),
  (⟨3444⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3445⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3446⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3448⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3449⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3606⟩, 2))),
  (⟨3452⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3453⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3454⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3456⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3457⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3595⟩, 2))),
  (⟨3460⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3461⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3462⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3464⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3465⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3584⟩, 2))),
  (⟨3468⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3469⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨3470⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3471⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3472⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3574⟩, 2))),
  (⟨3475⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3476⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3477⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3479⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3480⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3563⟩, 2))),
  (⟨3483⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3484⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3485⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3487⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3488⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3552⟩, 2))),
  (⟨3491⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3492⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3493⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3495⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3496⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3541⟩, 2))),
  (⟨3499⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3500⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3501⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨3503⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3504⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3530⟩, 2))),
  (⟨3507⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3508⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3510⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3511⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3520⟩, 2))),
  (⟨3514⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3515⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3516⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨430⟩, 2))),
  (⟨3519⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3520⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3521⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3522⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3523⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3525⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3526⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3529⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3530⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3531⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3532⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3533⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3534⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3536⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3537⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3540⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3541⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3542⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3543⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3544⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3545⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3547⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3548⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3551⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3552⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3553⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3554⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3555⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3556⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3558⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3559⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3562⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3563⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3564⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes24_correct : ∀ i : Fin generatedDecodes24.size,
    decode runtimeBytecode generatedDecodes24[i].1 = generatedDecodes24[i].2 := by
  native_decide

theorem decode_3413 : decode runtimeBytecode ⟨3413⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨0, by decide⟩
theorem decode_3414 : decode runtimeBytecode ⟨3414⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨1, by decide⟩
theorem decode_3416 : decode runtimeBytecode ⟨3416⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨2, by decide⟩
theorem decode_3417 : decode runtimeBytecode ⟨3417⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3650⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨3, by decide⟩
theorem decode_3420 : decode runtimeBytecode ⟨3420⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨4, by decide⟩
theorem decode_3421 : decode runtimeBytecode ⟨3421⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨5, by decide⟩
theorem decode_3422 : decode runtimeBytecode ⟨3422⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨6, by decide⟩
theorem decode_3424 : decode runtimeBytecode ⟨3424⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨7, by decide⟩
theorem decode_3425 : decode runtimeBytecode ⟨3425⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3639⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨8, by decide⟩
theorem decode_3428 : decode runtimeBytecode ⟨3428⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨9, by decide⟩
theorem decode_3429 : decode runtimeBytecode ⟨3429⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨10, by decide⟩
theorem decode_3430 : decode runtimeBytecode ⟨3430⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨11, by decide⟩
theorem decode_3432 : decode runtimeBytecode ⟨3432⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨12, by decide⟩
theorem decode_3433 : decode runtimeBytecode ⟨3433⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3628⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨13, by decide⟩
theorem decode_3436 : decode runtimeBytecode ⟨3436⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨14, by decide⟩
theorem decode_3437 : decode runtimeBytecode ⟨3437⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨15, by decide⟩
theorem decode_3438 : decode runtimeBytecode ⟨3438⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨16, by decide⟩
theorem decode_3440 : decode runtimeBytecode ⟨3440⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨17, by decide⟩
theorem decode_3441 : decode runtimeBytecode ⟨3441⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3617⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨18, by decide⟩
theorem decode_3444 : decode runtimeBytecode ⟨3444⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨19, by decide⟩
theorem decode_3445 : decode runtimeBytecode ⟨3445⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨20, by decide⟩
theorem decode_3446 : decode runtimeBytecode ⟨3446⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨21, by decide⟩
theorem decode_3448 : decode runtimeBytecode ⟨3448⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨22, by decide⟩
theorem decode_3449 : decode runtimeBytecode ⟨3449⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3606⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨23, by decide⟩
theorem decode_3452 : decode runtimeBytecode ⟨3452⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨24, by decide⟩
theorem decode_3453 : decode runtimeBytecode ⟨3453⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨25, by decide⟩
theorem decode_3454 : decode runtimeBytecode ⟨3454⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨26, by decide⟩
theorem decode_3456 : decode runtimeBytecode ⟨3456⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨27, by decide⟩
theorem decode_3457 : decode runtimeBytecode ⟨3457⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3595⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨28, by decide⟩
theorem decode_3460 : decode runtimeBytecode ⟨3460⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨29, by decide⟩
theorem decode_3461 : decode runtimeBytecode ⟨3461⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨30, by decide⟩
theorem decode_3462 : decode runtimeBytecode ⟨3462⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨31, by decide⟩
theorem decode_3464 : decode runtimeBytecode ⟨3464⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨32, by decide⟩
theorem decode_3465 : decode runtimeBytecode ⟨3465⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3584⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨33, by decide⟩
theorem decode_3468 : decode runtimeBytecode ⟨3468⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨34, by decide⟩
theorem decode_3469 : decode runtimeBytecode ⟨3469⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨35, by decide⟩
theorem decode_3470 : decode runtimeBytecode ⟨3470⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨36, by decide⟩
theorem decode_3471 : decode runtimeBytecode ⟨3471⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨37, by decide⟩
theorem decode_3472 : decode runtimeBytecode ⟨3472⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3574⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨38, by decide⟩
theorem decode_3475 : decode runtimeBytecode ⟨3475⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨39, by decide⟩
theorem decode_3476 : decode runtimeBytecode ⟨3476⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨40, by decide⟩
theorem decode_3477 : decode runtimeBytecode ⟨3477⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨41, by decide⟩
theorem decode_3479 : decode runtimeBytecode ⟨3479⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨42, by decide⟩
theorem decode_3480 : decode runtimeBytecode ⟨3480⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3563⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨43, by decide⟩
theorem decode_3483 : decode runtimeBytecode ⟨3483⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨44, by decide⟩
theorem decode_3484 : decode runtimeBytecode ⟨3484⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨45, by decide⟩
theorem decode_3485 : decode runtimeBytecode ⟨3485⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨46, by decide⟩
theorem decode_3487 : decode runtimeBytecode ⟨3487⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨47, by decide⟩
theorem decode_3488 : decode runtimeBytecode ⟨3488⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3552⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨48, by decide⟩
theorem decode_3491 : decode runtimeBytecode ⟨3491⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨49, by decide⟩
theorem decode_3492 : decode runtimeBytecode ⟨3492⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨50, by decide⟩
theorem decode_3493 : decode runtimeBytecode ⟨3493⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨51, by decide⟩
theorem decode_3495 : decode runtimeBytecode ⟨3495⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨52, by decide⟩
theorem decode_3496 : decode runtimeBytecode ⟨3496⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3541⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨53, by decide⟩
theorem decode_3499 : decode runtimeBytecode ⟨3499⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨54, by decide⟩
theorem decode_3500 : decode runtimeBytecode ⟨3500⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨55, by decide⟩
theorem decode_3501 : decode runtimeBytecode ⟨3501⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨56, by decide⟩
theorem decode_3503 : decode runtimeBytecode ⟨3503⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨57, by decide⟩
theorem decode_3504 : decode runtimeBytecode ⟨3504⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3530⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨58, by decide⟩
theorem decode_3507 : decode runtimeBytecode ⟨3507⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨59, by decide⟩
theorem decode_3508 : decode runtimeBytecode ⟨3508⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨60, by decide⟩
theorem decode_3510 : decode runtimeBytecode ⟨3510⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨61, by decide⟩
theorem decode_3511 : decode runtimeBytecode ⟨3511⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3520⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨62, by decide⟩
theorem decode_3514 : decode runtimeBytecode ⟨3514⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨63, by decide⟩
theorem decode_3515 : decode runtimeBytecode ⟨3515⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨64, by decide⟩
theorem decode_3516 : decode runtimeBytecode ⟨3516⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨430⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨65, by decide⟩
theorem decode_3519 : decode runtimeBytecode ⟨3519⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨66, by decide⟩
theorem decode_3520 : decode runtimeBytecode ⟨3520⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨67, by decide⟩
theorem decode_3521 : decode runtimeBytecode ⟨3521⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨68, by decide⟩
theorem decode_3522 : decode runtimeBytecode ⟨3522⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨69, by decide⟩
theorem decode_3523 : decode runtimeBytecode ⟨3523⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨70, by decide⟩
theorem decode_3525 : decode runtimeBytecode ⟨3525⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨71, by decide⟩
theorem decode_3526 : decode runtimeBytecode ⟨3526⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨72, by decide⟩
theorem decode_3529 : decode runtimeBytecode ⟨3529⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨73, by decide⟩
theorem decode_3530 : decode runtimeBytecode ⟨3530⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨74, by decide⟩
theorem decode_3531 : decode runtimeBytecode ⟨3531⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨75, by decide⟩
theorem decode_3532 : decode runtimeBytecode ⟨3532⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨76, by decide⟩
theorem decode_3533 : decode runtimeBytecode ⟨3533⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨77, by decide⟩
theorem decode_3534 : decode runtimeBytecode ⟨3534⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨78, by decide⟩
theorem decode_3536 : decode runtimeBytecode ⟨3536⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨79, by decide⟩
theorem decode_3537 : decode runtimeBytecode ⟨3537⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨80, by decide⟩
theorem decode_3540 : decode runtimeBytecode ⟨3540⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨81, by decide⟩
theorem decode_3541 : decode runtimeBytecode ⟨3541⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨82, by decide⟩
theorem decode_3542 : decode runtimeBytecode ⟨3542⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨83, by decide⟩
theorem decode_3543 : decode runtimeBytecode ⟨3543⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨84, by decide⟩
theorem decode_3544 : decode runtimeBytecode ⟨3544⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨85, by decide⟩
theorem decode_3545 : decode runtimeBytecode ⟨3545⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨86, by decide⟩
theorem decode_3547 : decode runtimeBytecode ⟨3547⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨87, by decide⟩
theorem decode_3548 : decode runtimeBytecode ⟨3548⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨88, by decide⟩
theorem decode_3551 : decode runtimeBytecode ⟨3551⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨89, by decide⟩
theorem decode_3552 : decode runtimeBytecode ⟨3552⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨90, by decide⟩
theorem decode_3553 : decode runtimeBytecode ⟨3553⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨91, by decide⟩
theorem decode_3554 : decode runtimeBytecode ⟨3554⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨92, by decide⟩
theorem decode_3555 : decode runtimeBytecode ⟨3555⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨93, by decide⟩
theorem decode_3556 : decode runtimeBytecode ⟨3556⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨94, by decide⟩
theorem decode_3558 : decode runtimeBytecode ⟨3558⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨95, by decide⟩
theorem decode_3559 : decode runtimeBytecode ⟨3559⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨96, by decide⟩
theorem decode_3562 : decode runtimeBytecode ⟨3562⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨97, by decide⟩
theorem decode_3563 : decode runtimeBytecode ⟨3563⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨98, by decide⟩
theorem decode_3564 : decode runtimeBytecode ⟨3564⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes24] using generatedDecodes24_correct ⟨99, by decide⟩

end Ripemd160Old
