import Examples.Ripemd160Old.DecodeGenerated.Chunk26

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes27 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3855⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3856⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3859⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3860⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3861⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3862⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3863⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3864⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3866⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3867⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3870⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3871⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3872⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3873⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3874⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3875⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3877⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3878⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3881⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3882⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3883⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3884⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3885⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3886⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3888⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3889⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3892⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3893⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3894⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3895⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3896⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3897⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3898⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3899⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3902⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3903⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3904⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3905⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3906⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3907⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3909⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3910⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3913⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3914⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3915⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3916⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3917⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3918⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3920⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3921⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3924⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3925⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3926⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3927⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3928⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3929⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3931⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3932⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3935⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3936⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3937⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3938⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3939⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3940⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3942⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3943⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3946⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3947⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3948⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3949⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3950⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3951⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨3952⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3953⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3956⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3957⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3958⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3959⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3960⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3961⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3963⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3964⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3967⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3968⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3969⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3970⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3971⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3972⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3974⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3975⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3978⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3979⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3980⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3981⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3982⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3983⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3985⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3986⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3989⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3990⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none))
]

private theorem generatedDecodes27_correct : ∀ i : Fin generatedDecodes27.size,
    decode runtimeBytecode generatedDecodes27[i].1 = generatedDecodes27[i].2 := by
  native_decide

theorem decode_3855 : decode runtimeBytecode ⟨3855⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨0, by decide⟩
theorem decode_3856 : decode runtimeBytecode ⟨3856⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨1, by decide⟩
theorem decode_3859 : decode runtimeBytecode ⟨3859⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨2, by decide⟩
theorem decode_3860 : decode runtimeBytecode ⟨3860⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨3, by decide⟩
theorem decode_3861 : decode runtimeBytecode ⟨3861⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨4, by decide⟩
theorem decode_3862 : decode runtimeBytecode ⟨3862⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨5, by decide⟩
theorem decode_3863 : decode runtimeBytecode ⟨3863⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨6, by decide⟩
theorem decode_3864 : decode runtimeBytecode ⟨3864⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨7, by decide⟩
theorem decode_3866 : decode runtimeBytecode ⟨3866⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨8, by decide⟩
theorem decode_3867 : decode runtimeBytecode ⟨3867⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨9, by decide⟩
theorem decode_3870 : decode runtimeBytecode ⟨3870⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨10, by decide⟩
theorem decode_3871 : decode runtimeBytecode ⟨3871⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨11, by decide⟩
theorem decode_3872 : decode runtimeBytecode ⟨3872⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨12, by decide⟩
theorem decode_3873 : decode runtimeBytecode ⟨3873⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨13, by decide⟩
theorem decode_3874 : decode runtimeBytecode ⟨3874⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨14, by decide⟩
theorem decode_3875 : decode runtimeBytecode ⟨3875⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨15, by decide⟩
theorem decode_3877 : decode runtimeBytecode ⟨3877⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨16, by decide⟩
theorem decode_3878 : decode runtimeBytecode ⟨3878⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨17, by decide⟩
theorem decode_3881 : decode runtimeBytecode ⟨3881⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨18, by decide⟩
theorem decode_3882 : decode runtimeBytecode ⟨3882⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨19, by decide⟩
theorem decode_3883 : decode runtimeBytecode ⟨3883⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨20, by decide⟩
theorem decode_3884 : decode runtimeBytecode ⟨3884⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨21, by decide⟩
theorem decode_3885 : decode runtimeBytecode ⟨3885⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨22, by decide⟩
theorem decode_3886 : decode runtimeBytecode ⟨3886⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨23, by decide⟩
theorem decode_3888 : decode runtimeBytecode ⟨3888⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨24, by decide⟩
theorem decode_3889 : decode runtimeBytecode ⟨3889⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨25, by decide⟩
theorem decode_3892 : decode runtimeBytecode ⟨3892⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨26, by decide⟩
theorem decode_3893 : decode runtimeBytecode ⟨3893⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨27, by decide⟩
theorem decode_3894 : decode runtimeBytecode ⟨3894⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨28, by decide⟩
theorem decode_3895 : decode runtimeBytecode ⟨3895⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨29, by decide⟩
theorem decode_3896 : decode runtimeBytecode ⟨3896⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨30, by decide⟩
theorem decode_3897 : decode runtimeBytecode ⟨3897⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨31, by decide⟩
theorem decode_3898 : decode runtimeBytecode ⟨3898⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨32, by decide⟩
theorem decode_3899 : decode runtimeBytecode ⟨3899⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨33, by decide⟩
theorem decode_3902 : decode runtimeBytecode ⟨3902⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨34, by decide⟩
theorem decode_3903 : decode runtimeBytecode ⟨3903⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨35, by decide⟩
theorem decode_3904 : decode runtimeBytecode ⟨3904⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨36, by decide⟩
theorem decode_3905 : decode runtimeBytecode ⟨3905⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨37, by decide⟩
theorem decode_3906 : decode runtimeBytecode ⟨3906⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨38, by decide⟩
theorem decode_3907 : decode runtimeBytecode ⟨3907⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨39, by decide⟩
theorem decode_3909 : decode runtimeBytecode ⟨3909⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨40, by decide⟩
theorem decode_3910 : decode runtimeBytecode ⟨3910⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨41, by decide⟩
theorem decode_3913 : decode runtimeBytecode ⟨3913⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨42, by decide⟩
theorem decode_3914 : decode runtimeBytecode ⟨3914⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨43, by decide⟩
theorem decode_3915 : decode runtimeBytecode ⟨3915⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨44, by decide⟩
theorem decode_3916 : decode runtimeBytecode ⟨3916⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨45, by decide⟩
theorem decode_3917 : decode runtimeBytecode ⟨3917⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨46, by decide⟩
theorem decode_3918 : decode runtimeBytecode ⟨3918⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨47, by decide⟩
theorem decode_3920 : decode runtimeBytecode ⟨3920⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨48, by decide⟩
theorem decode_3921 : decode runtimeBytecode ⟨3921⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨49, by decide⟩
theorem decode_3924 : decode runtimeBytecode ⟨3924⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨50, by decide⟩
theorem decode_3925 : decode runtimeBytecode ⟨3925⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨51, by decide⟩
theorem decode_3926 : decode runtimeBytecode ⟨3926⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨52, by decide⟩
theorem decode_3927 : decode runtimeBytecode ⟨3927⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨53, by decide⟩
theorem decode_3928 : decode runtimeBytecode ⟨3928⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨54, by decide⟩
theorem decode_3929 : decode runtimeBytecode ⟨3929⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨55, by decide⟩
theorem decode_3931 : decode runtimeBytecode ⟨3931⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨56, by decide⟩
theorem decode_3932 : decode runtimeBytecode ⟨3932⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨57, by decide⟩
theorem decode_3935 : decode runtimeBytecode ⟨3935⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨58, by decide⟩
theorem decode_3936 : decode runtimeBytecode ⟨3936⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨59, by decide⟩
theorem decode_3937 : decode runtimeBytecode ⟨3937⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨60, by decide⟩
theorem decode_3938 : decode runtimeBytecode ⟨3938⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨61, by decide⟩
theorem decode_3939 : decode runtimeBytecode ⟨3939⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨62, by decide⟩
theorem decode_3940 : decode runtimeBytecode ⟨3940⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨63, by decide⟩
theorem decode_3942 : decode runtimeBytecode ⟨3942⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨64, by decide⟩
theorem decode_3943 : decode runtimeBytecode ⟨3943⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨65, by decide⟩
theorem decode_3946 : decode runtimeBytecode ⟨3946⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨66, by decide⟩
theorem decode_3947 : decode runtimeBytecode ⟨3947⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨67, by decide⟩
theorem decode_3948 : decode runtimeBytecode ⟨3948⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨68, by decide⟩
theorem decode_3949 : decode runtimeBytecode ⟨3949⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨69, by decide⟩
theorem decode_3950 : decode runtimeBytecode ⟨3950⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨70, by decide⟩
theorem decode_3951 : decode runtimeBytecode ⟨3951⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨71, by decide⟩
theorem decode_3952 : decode runtimeBytecode ⟨3952⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨72, by decide⟩
theorem decode_3953 : decode runtimeBytecode ⟨3953⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨73, by decide⟩
theorem decode_3956 : decode runtimeBytecode ⟨3956⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨74, by decide⟩
theorem decode_3957 : decode runtimeBytecode ⟨3957⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨75, by decide⟩
theorem decode_3958 : decode runtimeBytecode ⟨3958⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨76, by decide⟩
theorem decode_3959 : decode runtimeBytecode ⟨3959⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨77, by decide⟩
theorem decode_3960 : decode runtimeBytecode ⟨3960⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨78, by decide⟩
theorem decode_3961 : decode runtimeBytecode ⟨3961⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨79, by decide⟩
theorem decode_3963 : decode runtimeBytecode ⟨3963⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨80, by decide⟩
theorem decode_3964 : decode runtimeBytecode ⟨3964⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨81, by decide⟩
theorem decode_3967 : decode runtimeBytecode ⟨3967⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨82, by decide⟩
theorem decode_3968 : decode runtimeBytecode ⟨3968⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨83, by decide⟩
theorem decode_3969 : decode runtimeBytecode ⟨3969⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨84, by decide⟩
theorem decode_3970 : decode runtimeBytecode ⟨3970⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨85, by decide⟩
theorem decode_3971 : decode runtimeBytecode ⟨3971⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨86, by decide⟩
theorem decode_3972 : decode runtimeBytecode ⟨3972⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨87, by decide⟩
theorem decode_3974 : decode runtimeBytecode ⟨3974⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨88, by decide⟩
theorem decode_3975 : decode runtimeBytecode ⟨3975⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨89, by decide⟩
theorem decode_3978 : decode runtimeBytecode ⟨3978⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨90, by decide⟩
theorem decode_3979 : decode runtimeBytecode ⟨3979⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨91, by decide⟩
theorem decode_3980 : decode runtimeBytecode ⟨3980⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨92, by decide⟩
theorem decode_3981 : decode runtimeBytecode ⟨3981⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨93, by decide⟩
theorem decode_3982 : decode runtimeBytecode ⟨3982⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨94, by decide⟩
theorem decode_3983 : decode runtimeBytecode ⟨3983⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨95, by decide⟩
theorem decode_3985 : decode runtimeBytecode ⟨3985⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨96, by decide⟩
theorem decode_3986 : decode runtimeBytecode ⟨3986⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨97, by decide⟩
theorem decode_3989 : decode runtimeBytecode ⟨3989⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨98, by decide⟩
theorem decode_3990 : decode runtimeBytecode ⟨3990⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes27] using generatedDecodes27_correct ⟨99, by decide⟩

end Ripemd160Old
