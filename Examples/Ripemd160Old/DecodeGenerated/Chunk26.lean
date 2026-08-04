import Examples.Ripemd160Old.DecodeGenerated.Chunk25

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes26 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨3700⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3701⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3990⟩, 2))),
  (⟨3704⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3705⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3706⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3708⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3709⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3979⟩, 2))),
  (⟨3712⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3713⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3714⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3716⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3717⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3968⟩, 2))),
  (⟨3720⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3721⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3722⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3724⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3725⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3957⟩, 2))),
  (⟨3728⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3729⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3730⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3732⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3733⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3947⟩, 2))),
  (⟨3736⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3737⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3738⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3740⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3741⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3936⟩, 2))),
  (⟨3744⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3745⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3746⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨3748⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3749⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3925⟩, 2))),
  (⟨3752⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3753⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3754⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3756⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3757⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3914⟩, 2))),
  (⟨3760⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3761⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3762⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3764⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3765⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3903⟩, 2))),
  (⟨3768⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3769⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3770⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3772⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3773⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3893⟩, 2))),
  (⟨3776⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3777⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨3778⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3779⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3780⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3882⟩, 2))),
  (⟨3783⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3784⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3785⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3787⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3788⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3871⟩, 2))),
  (⟨3791⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3792⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3793⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3795⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3796⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3860⟩, 2))),
  (⟨3799⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3800⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3801⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨3803⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3804⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3849⟩, 2))),
  (⟨3807⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3808⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3809⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨3811⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3812⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3838⟩, 2))),
  (⟨3815⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3816⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨3818⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3819⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3828⟩, 2))),
  (⟨3822⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3823⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3824⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨416⟩, 2))),
  (⟨3827⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3828⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3829⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3830⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3831⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨3833⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3834⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3837⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3838⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3839⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3840⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3841⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3842⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨3844⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3845⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2))),
  (⟨3848⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3849⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3850⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3851⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3852⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3853⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)))
]

private theorem generatedDecodes26_correct : ∀ i : Fin generatedDecodes26.size,
    decode runtimeBytecode generatedDecodes26[i].1 = generatedDecodes26[i].2 := by
  native_decide

theorem decode_3700 : decode runtimeBytecode ⟨3700⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨0, by decide⟩
theorem decode_3701 : decode runtimeBytecode ⟨3701⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3990⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨1, by decide⟩
theorem decode_3704 : decode runtimeBytecode ⟨3704⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨2, by decide⟩
theorem decode_3705 : decode runtimeBytecode ⟨3705⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨3, by decide⟩
theorem decode_3706 : decode runtimeBytecode ⟨3706⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨4, by decide⟩
theorem decode_3708 : decode runtimeBytecode ⟨3708⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨5, by decide⟩
theorem decode_3709 : decode runtimeBytecode ⟨3709⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3979⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨6, by decide⟩
theorem decode_3712 : decode runtimeBytecode ⟨3712⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨7, by decide⟩
theorem decode_3713 : decode runtimeBytecode ⟨3713⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨8, by decide⟩
theorem decode_3714 : decode runtimeBytecode ⟨3714⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨9, by decide⟩
theorem decode_3716 : decode runtimeBytecode ⟨3716⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨10, by decide⟩
theorem decode_3717 : decode runtimeBytecode ⟨3717⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3968⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨11, by decide⟩
theorem decode_3720 : decode runtimeBytecode ⟨3720⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨12, by decide⟩
theorem decode_3721 : decode runtimeBytecode ⟨3721⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨13, by decide⟩
theorem decode_3722 : decode runtimeBytecode ⟨3722⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨14, by decide⟩
theorem decode_3724 : decode runtimeBytecode ⟨3724⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨15, by decide⟩
theorem decode_3725 : decode runtimeBytecode ⟨3725⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3957⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨16, by decide⟩
theorem decode_3728 : decode runtimeBytecode ⟨3728⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨17, by decide⟩
theorem decode_3729 : decode runtimeBytecode ⟨3729⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨18, by decide⟩
theorem decode_3730 : decode runtimeBytecode ⟨3730⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨19, by decide⟩
theorem decode_3732 : decode runtimeBytecode ⟨3732⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨20, by decide⟩
theorem decode_3733 : decode runtimeBytecode ⟨3733⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3947⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨21, by decide⟩
theorem decode_3736 : decode runtimeBytecode ⟨3736⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨22, by decide⟩
theorem decode_3737 : decode runtimeBytecode ⟨3737⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨23, by decide⟩
theorem decode_3738 : decode runtimeBytecode ⟨3738⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨24, by decide⟩
theorem decode_3740 : decode runtimeBytecode ⟨3740⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨25, by decide⟩
theorem decode_3741 : decode runtimeBytecode ⟨3741⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3936⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨26, by decide⟩
theorem decode_3744 : decode runtimeBytecode ⟨3744⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨27, by decide⟩
theorem decode_3745 : decode runtimeBytecode ⟨3745⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨28, by decide⟩
theorem decode_3746 : decode runtimeBytecode ⟨3746⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨29, by decide⟩
theorem decode_3748 : decode runtimeBytecode ⟨3748⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨30, by decide⟩
theorem decode_3749 : decode runtimeBytecode ⟨3749⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3925⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨31, by decide⟩
theorem decode_3752 : decode runtimeBytecode ⟨3752⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨32, by decide⟩
theorem decode_3753 : decode runtimeBytecode ⟨3753⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨33, by decide⟩
theorem decode_3754 : decode runtimeBytecode ⟨3754⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨34, by decide⟩
theorem decode_3756 : decode runtimeBytecode ⟨3756⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨35, by decide⟩
theorem decode_3757 : decode runtimeBytecode ⟨3757⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3914⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨36, by decide⟩
theorem decode_3760 : decode runtimeBytecode ⟨3760⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨37, by decide⟩
theorem decode_3761 : decode runtimeBytecode ⟨3761⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨38, by decide⟩
theorem decode_3762 : decode runtimeBytecode ⟨3762⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨39, by decide⟩
theorem decode_3764 : decode runtimeBytecode ⟨3764⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨40, by decide⟩
theorem decode_3765 : decode runtimeBytecode ⟨3765⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3903⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨41, by decide⟩
theorem decode_3768 : decode runtimeBytecode ⟨3768⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨42, by decide⟩
theorem decode_3769 : decode runtimeBytecode ⟨3769⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨43, by decide⟩
theorem decode_3770 : decode runtimeBytecode ⟨3770⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨44, by decide⟩
theorem decode_3772 : decode runtimeBytecode ⟨3772⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨45, by decide⟩
theorem decode_3773 : decode runtimeBytecode ⟨3773⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3893⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨46, by decide⟩
theorem decode_3776 : decode runtimeBytecode ⟨3776⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨47, by decide⟩
theorem decode_3777 : decode runtimeBytecode ⟨3777⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨48, by decide⟩
theorem decode_3778 : decode runtimeBytecode ⟨3778⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨49, by decide⟩
theorem decode_3779 : decode runtimeBytecode ⟨3779⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨50, by decide⟩
theorem decode_3780 : decode runtimeBytecode ⟨3780⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3882⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨51, by decide⟩
theorem decode_3783 : decode runtimeBytecode ⟨3783⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨52, by decide⟩
theorem decode_3784 : decode runtimeBytecode ⟨3784⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨53, by decide⟩
theorem decode_3785 : decode runtimeBytecode ⟨3785⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨54, by decide⟩
theorem decode_3787 : decode runtimeBytecode ⟨3787⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨55, by decide⟩
theorem decode_3788 : decode runtimeBytecode ⟨3788⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3871⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨56, by decide⟩
theorem decode_3791 : decode runtimeBytecode ⟨3791⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨57, by decide⟩
theorem decode_3792 : decode runtimeBytecode ⟨3792⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨58, by decide⟩
theorem decode_3793 : decode runtimeBytecode ⟨3793⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨59, by decide⟩
theorem decode_3795 : decode runtimeBytecode ⟨3795⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨60, by decide⟩
theorem decode_3796 : decode runtimeBytecode ⟨3796⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3860⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨61, by decide⟩
theorem decode_3799 : decode runtimeBytecode ⟨3799⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨62, by decide⟩
theorem decode_3800 : decode runtimeBytecode ⟨3800⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨63, by decide⟩
theorem decode_3801 : decode runtimeBytecode ⟨3801⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨64, by decide⟩
theorem decode_3803 : decode runtimeBytecode ⟨3803⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨65, by decide⟩
theorem decode_3804 : decode runtimeBytecode ⟨3804⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3849⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨66, by decide⟩
theorem decode_3807 : decode runtimeBytecode ⟨3807⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨67, by decide⟩
theorem decode_3808 : decode runtimeBytecode ⟨3808⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨68, by decide⟩
theorem decode_3809 : decode runtimeBytecode ⟨3809⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨69, by decide⟩
theorem decode_3811 : decode runtimeBytecode ⟨3811⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨70, by decide⟩
theorem decode_3812 : decode runtimeBytecode ⟨3812⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3838⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨71, by decide⟩
theorem decode_3815 : decode runtimeBytecode ⟨3815⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨72, by decide⟩
theorem decode_3816 : decode runtimeBytecode ⟨3816⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨73, by decide⟩
theorem decode_3818 : decode runtimeBytecode ⟨3818⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨74, by decide⟩
theorem decode_3819 : decode runtimeBytecode ⟨3819⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3828⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨75, by decide⟩
theorem decode_3822 : decode runtimeBytecode ⟨3822⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨76, by decide⟩
theorem decode_3823 : decode runtimeBytecode ⟨3823⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨77, by decide⟩
theorem decode_3824 : decode runtimeBytecode ⟨3824⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨416⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨78, by decide⟩
theorem decode_3827 : decode runtimeBytecode ⟨3827⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨79, by decide⟩
theorem decode_3828 : decode runtimeBytecode ⟨3828⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨80, by decide⟩
theorem decode_3829 : decode runtimeBytecode ⟨3829⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨81, by decide⟩
theorem decode_3830 : decode runtimeBytecode ⟨3830⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨82, by decide⟩
theorem decode_3831 : decode runtimeBytecode ⟨3831⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨83, by decide⟩
theorem decode_3833 : decode runtimeBytecode ⟨3833⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨84, by decide⟩
theorem decode_3834 : decode runtimeBytecode ⟨3834⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨85, by decide⟩
theorem decode_3837 : decode runtimeBytecode ⟨3837⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨86, by decide⟩
theorem decode_3838 : decode runtimeBytecode ⟨3838⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨87, by decide⟩
theorem decode_3839 : decode runtimeBytecode ⟨3839⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨88, by decide⟩
theorem decode_3840 : decode runtimeBytecode ⟨3840⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨89, by decide⟩
theorem decode_3841 : decode runtimeBytecode ⟨3841⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨90, by decide⟩
theorem decode_3842 : decode runtimeBytecode ⟨3842⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨91, by decide⟩
theorem decode_3844 : decode runtimeBytecode ⟨3844⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨92, by decide⟩
theorem decode_3845 : decode runtimeBytecode ⟨3845⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3823⟩, 2)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨93, by decide⟩
theorem decode_3848 : decode runtimeBytecode ⟨3848⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨94, by decide⟩
theorem decode_3849 : decode runtimeBytecode ⟨3849⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨95, by decide⟩
theorem decode_3850 : decode runtimeBytecode ⟨3850⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨96, by decide⟩
theorem decode_3851 : decode runtimeBytecode ⟨3851⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨97, by decide⟩
theorem decode_3852 : decode runtimeBytecode ⟨3852⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨98, by decide⟩
theorem decode_3853 : decode runtimeBytecode ⟨3853⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes26] using generatedDecodes26_correct ⟨99, by decide⟩

end Ripemd160Old
