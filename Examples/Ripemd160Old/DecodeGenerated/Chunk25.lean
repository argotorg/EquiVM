import Examples.Ripemd160Old.DecodeGenerated.Chunk24

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes25 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3565⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3566⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3567⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3569⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3570⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3573⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3575⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3576⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3577⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3578⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3579⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3580⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3583⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3584⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3585⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3586⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3587⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3588⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3590⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3591⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3594⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3595⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3596⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3597⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3598⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3599⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3601⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3602⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3605⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3606⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3607⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3608⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3609⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3610⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3612⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3613⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3616⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3617⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3618⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3619⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3620⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3621⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3623⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3624⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3627⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3628⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3629⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3630⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3631⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3632⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3634⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3635⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3638⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3639⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3640⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3641⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3642⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3643⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3645⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3646⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3649⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3651⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3652⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3653⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3654⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3656⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3657⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3660⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3661⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3662⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3663⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3664⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3665⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨3667⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3668⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3671⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3672⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3673⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3674⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3675⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3676⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨3677⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3678⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3681⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3682⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3683⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3684⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3685⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3686⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3688⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3689⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2))),
  (⟨3692⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3693⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3694⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨3696⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3697⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨3698⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3699⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none))
]

private theorem generatedDecodes25_correct : ∀ i : Fin generatedDecodes25.size,
    decode runtimeBytecode generatedDecodes25[i].1 = generatedDecodes25[i].2 := by
  native_decide

theorem decode_3565 : decode runtimeBytecode ⟨3565⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨0, by decide⟩
theorem decode_3566 : decode runtimeBytecode ⟨3566⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨1, by decide⟩
theorem decode_3567 : decode runtimeBytecode ⟨3567⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨2, by decide⟩
theorem decode_3569 : decode runtimeBytecode ⟨3569⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨3, by decide⟩
theorem decode_3570 : decode runtimeBytecode ⟨3570⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨4, by decide⟩
theorem decode_3573 : decode runtimeBytecode ⟨3573⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨5, by decide⟩
theorem decode_3574 : decode runtimeBytecode ⟨3574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨6, by decide⟩
theorem decode_3575 : decode runtimeBytecode ⟨3575⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨7, by decide⟩
theorem decode_3576 : decode runtimeBytecode ⟨3576⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨8, by decide⟩
theorem decode_3577 : decode runtimeBytecode ⟨3577⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨9, by decide⟩
theorem decode_3578 : decode runtimeBytecode ⟨3578⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨10, by decide⟩
theorem decode_3579 : decode runtimeBytecode ⟨3579⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨11, by decide⟩
theorem decode_3580 : decode runtimeBytecode ⟨3580⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨12, by decide⟩
theorem decode_3583 : decode runtimeBytecode ⟨3583⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨13, by decide⟩
theorem decode_3584 : decode runtimeBytecode ⟨3584⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨14, by decide⟩
theorem decode_3585 : decode runtimeBytecode ⟨3585⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨15, by decide⟩
theorem decode_3586 : decode runtimeBytecode ⟨3586⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨16, by decide⟩
theorem decode_3587 : decode runtimeBytecode ⟨3587⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨17, by decide⟩
theorem decode_3588 : decode runtimeBytecode ⟨3588⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨18, by decide⟩
theorem decode_3590 : decode runtimeBytecode ⟨3590⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨19, by decide⟩
theorem decode_3591 : decode runtimeBytecode ⟨3591⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨20, by decide⟩
theorem decode_3594 : decode runtimeBytecode ⟨3594⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨21, by decide⟩
theorem decode_3595 : decode runtimeBytecode ⟨3595⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨22, by decide⟩
theorem decode_3596 : decode runtimeBytecode ⟨3596⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨23, by decide⟩
theorem decode_3597 : decode runtimeBytecode ⟨3597⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨24, by decide⟩
theorem decode_3598 : decode runtimeBytecode ⟨3598⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨25, by decide⟩
theorem decode_3599 : decode runtimeBytecode ⟨3599⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨26, by decide⟩
theorem decode_3601 : decode runtimeBytecode ⟨3601⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨27, by decide⟩
theorem decode_3602 : decode runtimeBytecode ⟨3602⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨28, by decide⟩
theorem decode_3605 : decode runtimeBytecode ⟨3605⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨29, by decide⟩
theorem decode_3606 : decode runtimeBytecode ⟨3606⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨30, by decide⟩
theorem decode_3607 : decode runtimeBytecode ⟨3607⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨31, by decide⟩
theorem decode_3608 : decode runtimeBytecode ⟨3608⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨32, by decide⟩
theorem decode_3609 : decode runtimeBytecode ⟨3609⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨33, by decide⟩
theorem decode_3610 : decode runtimeBytecode ⟨3610⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨34, by decide⟩
theorem decode_3612 : decode runtimeBytecode ⟨3612⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨35, by decide⟩
theorem decode_3613 : decode runtimeBytecode ⟨3613⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨36, by decide⟩
theorem decode_3616 : decode runtimeBytecode ⟨3616⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨37, by decide⟩
theorem decode_3617 : decode runtimeBytecode ⟨3617⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨38, by decide⟩
theorem decode_3618 : decode runtimeBytecode ⟨3618⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨39, by decide⟩
theorem decode_3619 : decode runtimeBytecode ⟨3619⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨40, by decide⟩
theorem decode_3620 : decode runtimeBytecode ⟨3620⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨41, by decide⟩
theorem decode_3621 : decode runtimeBytecode ⟨3621⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨42, by decide⟩
theorem decode_3623 : decode runtimeBytecode ⟨3623⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨43, by decide⟩
theorem decode_3624 : decode runtimeBytecode ⟨3624⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨44, by decide⟩
theorem decode_3627 : decode runtimeBytecode ⟨3627⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨45, by decide⟩
theorem decode_3628 : decode runtimeBytecode ⟨3628⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨46, by decide⟩
theorem decode_3629 : decode runtimeBytecode ⟨3629⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨47, by decide⟩
theorem decode_3630 : decode runtimeBytecode ⟨3630⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨48, by decide⟩
theorem decode_3631 : decode runtimeBytecode ⟨3631⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨49, by decide⟩
theorem decode_3632 : decode runtimeBytecode ⟨3632⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨50, by decide⟩
theorem decode_3634 : decode runtimeBytecode ⟨3634⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨51, by decide⟩
theorem decode_3635 : decode runtimeBytecode ⟨3635⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨52, by decide⟩
theorem decode_3638 : decode runtimeBytecode ⟨3638⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨53, by decide⟩
theorem decode_3639 : decode runtimeBytecode ⟨3639⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨54, by decide⟩
theorem decode_3640 : decode runtimeBytecode ⟨3640⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨55, by decide⟩
theorem decode_3641 : decode runtimeBytecode ⟨3641⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨56, by decide⟩
theorem decode_3642 : decode runtimeBytecode ⟨3642⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨57, by decide⟩
theorem decode_3643 : decode runtimeBytecode ⟨3643⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨58, by decide⟩
theorem decode_3645 : decode runtimeBytecode ⟨3645⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨59, by decide⟩
theorem decode_3646 : decode runtimeBytecode ⟨3646⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨60, by decide⟩
theorem decode_3649 : decode runtimeBytecode ⟨3649⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨61, by decide⟩
theorem decode_3650 : decode runtimeBytecode ⟨3650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨62, by decide⟩
theorem decode_3651 : decode runtimeBytecode ⟨3651⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨63, by decide⟩
theorem decode_3652 : decode runtimeBytecode ⟨3652⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨64, by decide⟩
theorem decode_3653 : decode runtimeBytecode ⟨3653⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨65, by decide⟩
theorem decode_3654 : decode runtimeBytecode ⟨3654⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨66, by decide⟩
theorem decode_3656 : decode runtimeBytecode ⟨3656⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨67, by decide⟩
theorem decode_3657 : decode runtimeBytecode ⟨3657⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨68, by decide⟩
theorem decode_3660 : decode runtimeBytecode ⟨3660⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨69, by decide⟩
theorem decode_3661 : decode runtimeBytecode ⟨3661⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨70, by decide⟩
theorem decode_3662 : decode runtimeBytecode ⟨3662⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨71, by decide⟩
theorem decode_3663 : decode runtimeBytecode ⟨3663⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨72, by decide⟩
theorem decode_3664 : decode runtimeBytecode ⟨3664⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨73, by decide⟩
theorem decode_3665 : decode runtimeBytecode ⟨3665⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨74, by decide⟩
theorem decode_3667 : decode runtimeBytecode ⟨3667⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨75, by decide⟩
theorem decode_3668 : decode runtimeBytecode ⟨3668⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨76, by decide⟩
theorem decode_3671 : decode runtimeBytecode ⟨3671⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨77, by decide⟩
theorem decode_3672 : decode runtimeBytecode ⟨3672⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨78, by decide⟩
theorem decode_3673 : decode runtimeBytecode ⟨3673⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨79, by decide⟩
theorem decode_3674 : decode runtimeBytecode ⟨3674⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨80, by decide⟩
theorem decode_3675 : decode runtimeBytecode ⟨3675⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨81, by decide⟩
theorem decode_3676 : decode runtimeBytecode ⟨3676⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨82, by decide⟩
theorem decode_3677 : decode runtimeBytecode ⟨3677⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨83, by decide⟩
theorem decode_3678 : decode runtimeBytecode ⟨3678⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨84, by decide⟩
theorem decode_3681 : decode runtimeBytecode ⟨3681⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨85, by decide⟩
theorem decode_3682 : decode runtimeBytecode ⟨3682⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨86, by decide⟩
theorem decode_3683 : decode runtimeBytecode ⟨3683⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨87, by decide⟩
theorem decode_3684 : decode runtimeBytecode ⟨3684⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨88, by decide⟩
theorem decode_3685 : decode runtimeBytecode ⟨3685⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨89, by decide⟩
theorem decode_3686 : decode runtimeBytecode ⟨3686⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨90, by decide⟩
theorem decode_3688 : decode runtimeBytecode ⟨3688⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨91, by decide⟩
theorem decode_3689 : decode runtimeBytecode ⟨3689⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3515⟩, 2)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨92, by decide⟩
theorem decode_3692 : decode runtimeBytecode ⟨3692⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨93, by decide⟩
theorem decode_3693 : decode runtimeBytecode ⟨3693⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨94, by decide⟩
theorem decode_3694 : decode runtimeBytecode ⟨3694⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨95, by decide⟩
theorem decode_3696 : decode runtimeBytecode ⟨3696⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨96, by decide⟩
theorem decode_3697 : decode runtimeBytecode ⟨3697⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨97, by decide⟩
theorem decode_3698 : decode runtimeBytecode ⟨3698⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨98, by decide⟩
theorem decode_3699 : decode runtimeBytecode ⟨3699⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes25] using generatedDecodes25_correct ⟨99, by decide⟩

end Ripemd160Old
