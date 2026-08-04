import Examples.Ripemd160Old.DecodeGenerated.Chunk56

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes57 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7866⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7867⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7869⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7870⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8065⟩, 2))),
  (⟨7873⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7874⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7875⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7877⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7878⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8054⟩, 2))),
  (⟨7881⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7882⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7883⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7885⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7886⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8043⟩, 2))),
  (⟨7889⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7890⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7891⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7893⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7894⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8032⟩, 2))),
  (⟨7897⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7898⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7899⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7901⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7902⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8021⟩, 2))),
  (⟨7905⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7906⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨7907⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7908⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7909⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8010⟩, 2))),
  (⟨7912⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7913⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7914⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7916⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7917⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7999⟩, 2))),
  (⟨7920⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7921⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7922⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7924⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7925⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7988⟩, 2))),
  (⟨7928⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7929⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7930⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7932⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7933⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7978⟩, 2))),
  (⟨7936⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7937⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7938⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7940⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7941⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7967⟩, 2))),
  (⟨7944⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7945⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7947⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7948⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7957⟩, 2))),
  (⟨7951⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7952⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7953⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2))),
  (⟨7956⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7957⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7958⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7959⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7960⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7962⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7963⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨7966⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7967⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7968⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7969⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7970⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7971⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7973⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7974⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨7977⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7978⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7979⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7980⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7981⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7982⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨7983⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7984⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨7987⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7988⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7989⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7990⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7991⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7992⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7994⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7995⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨7998⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7999⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8000⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8001⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8002⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8003⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8005⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8006⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2))),
  (⟨8009⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8010⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8011⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8012⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8013⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes57_correct : ∀ i : Fin generatedDecodes57.size,
    decode runtimeBytecode generatedDecodes57[i].1 = generatedDecodes57[i].2 := by
  native_decide

theorem decode_7866 : decode runtimeBytecode ⟨7866⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨0, by decide⟩
theorem decode_7867 : decode runtimeBytecode ⟨7867⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨1, by decide⟩
theorem decode_7869 : decode runtimeBytecode ⟨7869⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨2, by decide⟩
theorem decode_7870 : decode runtimeBytecode ⟨7870⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8065⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨3, by decide⟩
theorem decode_7873 : decode runtimeBytecode ⟨7873⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨4, by decide⟩
theorem decode_7874 : decode runtimeBytecode ⟨7874⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨5, by decide⟩
theorem decode_7875 : decode runtimeBytecode ⟨7875⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨6, by decide⟩
theorem decode_7877 : decode runtimeBytecode ⟨7877⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨7, by decide⟩
theorem decode_7878 : decode runtimeBytecode ⟨7878⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8054⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨8, by decide⟩
theorem decode_7881 : decode runtimeBytecode ⟨7881⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨9, by decide⟩
theorem decode_7882 : decode runtimeBytecode ⟨7882⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨10, by decide⟩
theorem decode_7883 : decode runtimeBytecode ⟨7883⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨11, by decide⟩
theorem decode_7885 : decode runtimeBytecode ⟨7885⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨12, by decide⟩
theorem decode_7886 : decode runtimeBytecode ⟨7886⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8043⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨13, by decide⟩
theorem decode_7889 : decode runtimeBytecode ⟨7889⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨14, by decide⟩
theorem decode_7890 : decode runtimeBytecode ⟨7890⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨15, by decide⟩
theorem decode_7891 : decode runtimeBytecode ⟨7891⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨16, by decide⟩
theorem decode_7893 : decode runtimeBytecode ⟨7893⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨17, by decide⟩
theorem decode_7894 : decode runtimeBytecode ⟨7894⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8032⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨18, by decide⟩
theorem decode_7897 : decode runtimeBytecode ⟨7897⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨19, by decide⟩
theorem decode_7898 : decode runtimeBytecode ⟨7898⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨20, by decide⟩
theorem decode_7899 : decode runtimeBytecode ⟨7899⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨21, by decide⟩
theorem decode_7901 : decode runtimeBytecode ⟨7901⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨22, by decide⟩
theorem decode_7902 : decode runtimeBytecode ⟨7902⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8021⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨23, by decide⟩
theorem decode_7905 : decode runtimeBytecode ⟨7905⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨24, by decide⟩
theorem decode_7906 : decode runtimeBytecode ⟨7906⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨25, by decide⟩
theorem decode_7907 : decode runtimeBytecode ⟨7907⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨26, by decide⟩
theorem decode_7908 : decode runtimeBytecode ⟨7908⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨27, by decide⟩
theorem decode_7909 : decode runtimeBytecode ⟨7909⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8010⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨28, by decide⟩
theorem decode_7912 : decode runtimeBytecode ⟨7912⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨29, by decide⟩
theorem decode_7913 : decode runtimeBytecode ⟨7913⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨30, by decide⟩
theorem decode_7914 : decode runtimeBytecode ⟨7914⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨31, by decide⟩
theorem decode_7916 : decode runtimeBytecode ⟨7916⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨32, by decide⟩
theorem decode_7917 : decode runtimeBytecode ⟨7917⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7999⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨33, by decide⟩
theorem decode_7920 : decode runtimeBytecode ⟨7920⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨34, by decide⟩
theorem decode_7921 : decode runtimeBytecode ⟨7921⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨35, by decide⟩
theorem decode_7922 : decode runtimeBytecode ⟨7922⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨36, by decide⟩
theorem decode_7924 : decode runtimeBytecode ⟨7924⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨37, by decide⟩
theorem decode_7925 : decode runtimeBytecode ⟨7925⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7988⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨38, by decide⟩
theorem decode_7928 : decode runtimeBytecode ⟨7928⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨39, by decide⟩
theorem decode_7929 : decode runtimeBytecode ⟨7929⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨40, by decide⟩
theorem decode_7930 : decode runtimeBytecode ⟨7930⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨41, by decide⟩
theorem decode_7932 : decode runtimeBytecode ⟨7932⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨42, by decide⟩
theorem decode_7933 : decode runtimeBytecode ⟨7933⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7978⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨43, by decide⟩
theorem decode_7936 : decode runtimeBytecode ⟨7936⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨44, by decide⟩
theorem decode_7937 : decode runtimeBytecode ⟨7937⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨45, by decide⟩
theorem decode_7938 : decode runtimeBytecode ⟨7938⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨46, by decide⟩
theorem decode_7940 : decode runtimeBytecode ⟨7940⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨47, by decide⟩
theorem decode_7941 : decode runtimeBytecode ⟨7941⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7967⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨48, by decide⟩
theorem decode_7944 : decode runtimeBytecode ⟨7944⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨49, by decide⟩
theorem decode_7945 : decode runtimeBytecode ⟨7945⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨50, by decide⟩
theorem decode_7947 : decode runtimeBytecode ⟨7947⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨51, by decide⟩
theorem decode_7948 : decode runtimeBytecode ⟨7948⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7957⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨52, by decide⟩
theorem decode_7951 : decode runtimeBytecode ⟨7951⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨53, by decide⟩
theorem decode_7952 : decode runtimeBytecode ⟨7952⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨54, by decide⟩
theorem decode_7953 : decode runtimeBytecode ⟨7953⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨55, by decide⟩
theorem decode_7956 : decode runtimeBytecode ⟨7956⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨56, by decide⟩
theorem decode_7957 : decode runtimeBytecode ⟨7957⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨57, by decide⟩
theorem decode_7958 : decode runtimeBytecode ⟨7958⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨58, by decide⟩
theorem decode_7959 : decode runtimeBytecode ⟨7959⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨59, by decide⟩
theorem decode_7960 : decode runtimeBytecode ⟨7960⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨60, by decide⟩
theorem decode_7962 : decode runtimeBytecode ⟨7962⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨61, by decide⟩
theorem decode_7963 : decode runtimeBytecode ⟨7963⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨62, by decide⟩
theorem decode_7966 : decode runtimeBytecode ⟨7966⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨63, by decide⟩
theorem decode_7967 : decode runtimeBytecode ⟨7967⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨64, by decide⟩
theorem decode_7968 : decode runtimeBytecode ⟨7968⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨65, by decide⟩
theorem decode_7969 : decode runtimeBytecode ⟨7969⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨66, by decide⟩
theorem decode_7970 : decode runtimeBytecode ⟨7970⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨67, by decide⟩
theorem decode_7971 : decode runtimeBytecode ⟨7971⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨68, by decide⟩
theorem decode_7973 : decode runtimeBytecode ⟨7973⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨69, by decide⟩
theorem decode_7974 : decode runtimeBytecode ⟨7974⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨70, by decide⟩
theorem decode_7977 : decode runtimeBytecode ⟨7977⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨71, by decide⟩
theorem decode_7978 : decode runtimeBytecode ⟨7978⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨72, by decide⟩
theorem decode_7979 : decode runtimeBytecode ⟨7979⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨73, by decide⟩
theorem decode_7980 : decode runtimeBytecode ⟨7980⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨74, by decide⟩
theorem decode_7981 : decode runtimeBytecode ⟨7981⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨75, by decide⟩
theorem decode_7982 : decode runtimeBytecode ⟨7982⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨76, by decide⟩
theorem decode_7983 : decode runtimeBytecode ⟨7983⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨77, by decide⟩
theorem decode_7984 : decode runtimeBytecode ⟨7984⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨78, by decide⟩
theorem decode_7987 : decode runtimeBytecode ⟨7987⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨79, by decide⟩
theorem decode_7988 : decode runtimeBytecode ⟨7988⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨80, by decide⟩
theorem decode_7989 : decode runtimeBytecode ⟨7989⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨81, by decide⟩
theorem decode_7990 : decode runtimeBytecode ⟨7990⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨82, by decide⟩
theorem decode_7991 : decode runtimeBytecode ⟨7991⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨83, by decide⟩
theorem decode_7992 : decode runtimeBytecode ⟨7992⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨84, by decide⟩
theorem decode_7994 : decode runtimeBytecode ⟨7994⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨85, by decide⟩
theorem decode_7995 : decode runtimeBytecode ⟨7995⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨86, by decide⟩
theorem decode_7998 : decode runtimeBytecode ⟨7998⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨87, by decide⟩
theorem decode_7999 : decode runtimeBytecode ⟨7999⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨88, by decide⟩
theorem decode_8000 : decode runtimeBytecode ⟨8000⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨89, by decide⟩
theorem decode_8001 : decode runtimeBytecode ⟨8001⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨90, by decide⟩
theorem decode_8002 : decode runtimeBytecode ⟨8002⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨91, by decide⟩
theorem decode_8003 : decode runtimeBytecode ⟨8003⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨92, by decide⟩
theorem decode_8005 : decode runtimeBytecode ⟨8005⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨93, by decide⟩
theorem decode_8006 : decode runtimeBytecode ⟨8006⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7952⟩, 2)) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨94, by decide⟩
theorem decode_8009 : decode runtimeBytecode ⟨8009⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨95, by decide⟩
theorem decode_8010 : decode runtimeBytecode ⟨8010⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨96, by decide⟩
theorem decode_8011 : decode runtimeBytecode ⟨8011⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨97, by decide⟩
theorem decode_8012 : decode runtimeBytecode ⟨8012⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨98, by decide⟩
theorem decode_8013 : decode runtimeBytecode ⟨8013⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes57] using generatedDecodes57_correct ⟨99, by decide⟩

end Ripemd160Old
