import Examples.Ripemd160Old.DecodeGenerated.Chunk49

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes50 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨6855⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨6857⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6858⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2))),
  (⟨6861⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6862⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6863⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6864⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6865⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6866⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨6867⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6868⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2))),
  (⟨6871⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6872⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6873⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6874⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6875⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6876⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨6878⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6879⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2))),
  (⟨6882⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6883⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6884⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6885⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6886⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6887⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨6889⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6890⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2))),
  (⟨6893⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6894⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6895⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6896⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨6898⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨6899⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨6900⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6901⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨6902⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6903⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7192⟩, 2))),
  (⟨6906⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6907⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6908⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨6910⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6911⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7181⟩, 2))),
  (⟨6914⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6915⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6916⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨6918⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6919⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7170⟩, 2))),
  (⟨6922⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6923⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6924⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨6926⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6927⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7159⟩, 2))),
  (⟨6930⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6931⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6932⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨6934⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6935⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7148⟩, 2))),
  (⟨6938⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6939⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6940⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨6942⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6943⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7137⟩, 2))),
  (⟨6946⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6947⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6948⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨6950⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6951⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7126⟩, 2))),
  (⟨6954⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6955⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6956⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨6958⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6959⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7116⟩, 2))),
  (⟨6962⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6963⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6964⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨6966⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6967⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7105⟩, 2))),
  (⟨6970⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6971⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6972⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨6974⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6975⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7094⟩, 2))),
  (⟨6978⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6979⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6980⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨6981⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6982⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7083⟩, 2))),
  (⟨6985⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6986⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6987⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨6989⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6990⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7072⟩, 2))),
  (⟨6993⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨6994⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨6995⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨6997⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨6998⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7061⟩, 2))),
  (⟨7001⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7002⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7003⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)))
]

private theorem generatedDecodes50_correct : ∀ i : Fin generatedDecodes50.size,
    decode runtimeBytecode generatedDecodes50[i].1 = generatedDecodes50[i].2 := by
  native_decide

theorem decode_6855 : decode runtimeBytecode ⟨6855⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨0, by decide⟩
theorem decode_6857 : decode runtimeBytecode ⟨6857⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨1, by decide⟩
theorem decode_6858 : decode runtimeBytecode ⟨6858⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨2, by decide⟩
theorem decode_6861 : decode runtimeBytecode ⟨6861⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨3, by decide⟩
theorem decode_6862 : decode runtimeBytecode ⟨6862⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨4, by decide⟩
theorem decode_6863 : decode runtimeBytecode ⟨6863⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨5, by decide⟩
theorem decode_6864 : decode runtimeBytecode ⟨6864⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨6, by decide⟩
theorem decode_6865 : decode runtimeBytecode ⟨6865⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨7, by decide⟩
theorem decode_6866 : decode runtimeBytecode ⟨6866⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨8, by decide⟩
theorem decode_6867 : decode runtimeBytecode ⟨6867⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨9, by decide⟩
theorem decode_6868 : decode runtimeBytecode ⟨6868⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨10, by decide⟩
theorem decode_6871 : decode runtimeBytecode ⟨6871⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨11, by decide⟩
theorem decode_6872 : decode runtimeBytecode ⟨6872⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨12, by decide⟩
theorem decode_6873 : decode runtimeBytecode ⟨6873⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨13, by decide⟩
theorem decode_6874 : decode runtimeBytecode ⟨6874⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨14, by decide⟩
theorem decode_6875 : decode runtimeBytecode ⟨6875⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨15, by decide⟩
theorem decode_6876 : decode runtimeBytecode ⟨6876⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨16, by decide⟩
theorem decode_6878 : decode runtimeBytecode ⟨6878⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨17, by decide⟩
theorem decode_6879 : decode runtimeBytecode ⟨6879⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨18, by decide⟩
theorem decode_6882 : decode runtimeBytecode ⟨6882⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨19, by decide⟩
theorem decode_6883 : decode runtimeBytecode ⟨6883⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨20, by decide⟩
theorem decode_6884 : decode runtimeBytecode ⟨6884⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨21, by decide⟩
theorem decode_6885 : decode runtimeBytecode ⟨6885⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨22, by decide⟩
theorem decode_6886 : decode runtimeBytecode ⟨6886⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨23, by decide⟩
theorem decode_6887 : decode runtimeBytecode ⟨6887⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨24, by decide⟩
theorem decode_6889 : decode runtimeBytecode ⟨6889⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨25, by decide⟩
theorem decode_6890 : decode runtimeBytecode ⟨6890⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨6716⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨26, by decide⟩
theorem decode_6893 : decode runtimeBytecode ⟨6893⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨27, by decide⟩
theorem decode_6894 : decode runtimeBytecode ⟨6894⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨28, by decide⟩
theorem decode_6895 : decode runtimeBytecode ⟨6895⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨29, by decide⟩
theorem decode_6896 : decode runtimeBytecode ⟨6896⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨30, by decide⟩
theorem decode_6898 : decode runtimeBytecode ⟨6898⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨31, by decide⟩
theorem decode_6899 : decode runtimeBytecode ⟨6899⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨32, by decide⟩
theorem decode_6900 : decode runtimeBytecode ⟨6900⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨33, by decide⟩
theorem decode_6901 : decode runtimeBytecode ⟨6901⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨34, by decide⟩
theorem decode_6902 : decode runtimeBytecode ⟨6902⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨35, by decide⟩
theorem decode_6903 : decode runtimeBytecode ⟨6903⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7192⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨36, by decide⟩
theorem decode_6906 : decode runtimeBytecode ⟨6906⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨37, by decide⟩
theorem decode_6907 : decode runtimeBytecode ⟨6907⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨38, by decide⟩
theorem decode_6908 : decode runtimeBytecode ⟨6908⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨39, by decide⟩
theorem decode_6910 : decode runtimeBytecode ⟨6910⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨40, by decide⟩
theorem decode_6911 : decode runtimeBytecode ⟨6911⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7181⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨41, by decide⟩
theorem decode_6914 : decode runtimeBytecode ⟨6914⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨42, by decide⟩
theorem decode_6915 : decode runtimeBytecode ⟨6915⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨43, by decide⟩
theorem decode_6916 : decode runtimeBytecode ⟨6916⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨44, by decide⟩
theorem decode_6918 : decode runtimeBytecode ⟨6918⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨45, by decide⟩
theorem decode_6919 : decode runtimeBytecode ⟨6919⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7170⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨46, by decide⟩
theorem decode_6922 : decode runtimeBytecode ⟨6922⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨47, by decide⟩
theorem decode_6923 : decode runtimeBytecode ⟨6923⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨48, by decide⟩
theorem decode_6924 : decode runtimeBytecode ⟨6924⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨49, by decide⟩
theorem decode_6926 : decode runtimeBytecode ⟨6926⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨50, by decide⟩
theorem decode_6927 : decode runtimeBytecode ⟨6927⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7159⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨51, by decide⟩
theorem decode_6930 : decode runtimeBytecode ⟨6930⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨52, by decide⟩
theorem decode_6931 : decode runtimeBytecode ⟨6931⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨53, by decide⟩
theorem decode_6932 : decode runtimeBytecode ⟨6932⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨54, by decide⟩
theorem decode_6934 : decode runtimeBytecode ⟨6934⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨55, by decide⟩
theorem decode_6935 : decode runtimeBytecode ⟨6935⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7148⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨56, by decide⟩
theorem decode_6938 : decode runtimeBytecode ⟨6938⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨57, by decide⟩
theorem decode_6939 : decode runtimeBytecode ⟨6939⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨58, by decide⟩
theorem decode_6940 : decode runtimeBytecode ⟨6940⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨59, by decide⟩
theorem decode_6942 : decode runtimeBytecode ⟨6942⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨60, by decide⟩
theorem decode_6943 : decode runtimeBytecode ⟨6943⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7137⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨61, by decide⟩
theorem decode_6946 : decode runtimeBytecode ⟨6946⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨62, by decide⟩
theorem decode_6947 : decode runtimeBytecode ⟨6947⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨63, by decide⟩
theorem decode_6948 : decode runtimeBytecode ⟨6948⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨64, by decide⟩
theorem decode_6950 : decode runtimeBytecode ⟨6950⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨65, by decide⟩
theorem decode_6951 : decode runtimeBytecode ⟨6951⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7126⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨66, by decide⟩
theorem decode_6954 : decode runtimeBytecode ⟨6954⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨67, by decide⟩
theorem decode_6955 : decode runtimeBytecode ⟨6955⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨68, by decide⟩
theorem decode_6956 : decode runtimeBytecode ⟨6956⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨69, by decide⟩
theorem decode_6958 : decode runtimeBytecode ⟨6958⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨70, by decide⟩
theorem decode_6959 : decode runtimeBytecode ⟨6959⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7116⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨71, by decide⟩
theorem decode_6962 : decode runtimeBytecode ⟨6962⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨72, by decide⟩
theorem decode_6963 : decode runtimeBytecode ⟨6963⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨73, by decide⟩
theorem decode_6964 : decode runtimeBytecode ⟨6964⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨74, by decide⟩
theorem decode_6966 : decode runtimeBytecode ⟨6966⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨75, by decide⟩
theorem decode_6967 : decode runtimeBytecode ⟨6967⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7105⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨76, by decide⟩
theorem decode_6970 : decode runtimeBytecode ⟨6970⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨77, by decide⟩
theorem decode_6971 : decode runtimeBytecode ⟨6971⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨78, by decide⟩
theorem decode_6972 : decode runtimeBytecode ⟨6972⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨79, by decide⟩
theorem decode_6974 : decode runtimeBytecode ⟨6974⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨80, by decide⟩
theorem decode_6975 : decode runtimeBytecode ⟨6975⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7094⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨81, by decide⟩
theorem decode_6978 : decode runtimeBytecode ⟨6978⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨82, by decide⟩
theorem decode_6979 : decode runtimeBytecode ⟨6979⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨83, by decide⟩
theorem decode_6980 : decode runtimeBytecode ⟨6980⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨84, by decide⟩
theorem decode_6981 : decode runtimeBytecode ⟨6981⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨85, by decide⟩
theorem decode_6982 : decode runtimeBytecode ⟨6982⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7083⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨86, by decide⟩
theorem decode_6985 : decode runtimeBytecode ⟨6985⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨87, by decide⟩
theorem decode_6986 : decode runtimeBytecode ⟨6986⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨88, by decide⟩
theorem decode_6987 : decode runtimeBytecode ⟨6987⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨89, by decide⟩
theorem decode_6989 : decode runtimeBytecode ⟨6989⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨90, by decide⟩
theorem decode_6990 : decode runtimeBytecode ⟨6990⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7072⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨91, by decide⟩
theorem decode_6993 : decode runtimeBytecode ⟨6993⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨92, by decide⟩
theorem decode_6994 : decode runtimeBytecode ⟨6994⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨93, by decide⟩
theorem decode_6995 : decode runtimeBytecode ⟨6995⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨94, by decide⟩
theorem decode_6997 : decode runtimeBytecode ⟨6997⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨95, by decide⟩
theorem decode_6998 : decode runtimeBytecode ⟨6998⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7061⟩, 2)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨96, by decide⟩
theorem decode_7001 : decode runtimeBytecode ⟨7001⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨97, by decide⟩
theorem decode_7002 : decode runtimeBytecode ⟨7002⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨98, by decide⟩
theorem decode_7003 : decode runtimeBytecode ⟨7003⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes50] using generatedDecodes50_correct ⟨99, by decide⟩

end Ripemd160Old
