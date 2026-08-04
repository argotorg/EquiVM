import Examples.Ripemd160Old.DecodeGenerated.Chunk42

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes43 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5942⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5943⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5944⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5945⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5946⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5949⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5950⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5951⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5952⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5953⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5954⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5955⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5956⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5957⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5958⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5960⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5961⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5962⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5963⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5964⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5965⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5968⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5969⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5970⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5971⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5972⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5973⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5974⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5975⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5976⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5977⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5979⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5980⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5981⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5982⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5983⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5984⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5987⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5988⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5989⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5990⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5991⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5992⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5993⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5994⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5995⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5996⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5998⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5999⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6000⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6001⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6002⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6003⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6006⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6007⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6008⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6009⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6010⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6011⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6012⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6013⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6014⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6015⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨6017⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6018⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6019⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6020⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6021⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6022⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6025⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6026⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6027⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6028⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6029⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6030⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6031⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6032⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6033⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6034⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨6036⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6037⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6038⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6039⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6040⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6041⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨6044⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨6045⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨6046⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6047⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨6048⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6049⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨6050⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨6051⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨6052⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6053⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨6055⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨6056⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨6057⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨6058⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨6059⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes43_correct : ∀ i : Fin generatedDecodes43.size,
    decode runtimeBytecode generatedDecodes43[i].1 = generatedDecodes43[i].2 := by
  native_decide

theorem decode_5942 : decode runtimeBytecode ⟨5942⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨0, by decide⟩
theorem decode_5943 : decode runtimeBytecode ⟨5943⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨1, by decide⟩
theorem decode_5944 : decode runtimeBytecode ⟨5944⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨2, by decide⟩
theorem decode_5945 : decode runtimeBytecode ⟨5945⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨3, by decide⟩
theorem decode_5946 : decode runtimeBytecode ⟨5946⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨4, by decide⟩
theorem decode_5949 : decode runtimeBytecode ⟨5949⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨5, by decide⟩
theorem decode_5950 : decode runtimeBytecode ⟨5950⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨6, by decide⟩
theorem decode_5951 : decode runtimeBytecode ⟨5951⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨7, by decide⟩
theorem decode_5952 : decode runtimeBytecode ⟨5952⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨8, by decide⟩
theorem decode_5953 : decode runtimeBytecode ⟨5953⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨9, by decide⟩
theorem decode_5954 : decode runtimeBytecode ⟨5954⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨10, by decide⟩
theorem decode_5955 : decode runtimeBytecode ⟨5955⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨11, by decide⟩
theorem decode_5956 : decode runtimeBytecode ⟨5956⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨12, by decide⟩
theorem decode_5957 : decode runtimeBytecode ⟨5957⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨13, by decide⟩
theorem decode_5958 : decode runtimeBytecode ⟨5958⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨14, by decide⟩
theorem decode_5960 : decode runtimeBytecode ⟨5960⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨15, by decide⟩
theorem decode_5961 : decode runtimeBytecode ⟨5961⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨16, by decide⟩
theorem decode_5962 : decode runtimeBytecode ⟨5962⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨17, by decide⟩
theorem decode_5963 : decode runtimeBytecode ⟨5963⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨18, by decide⟩
theorem decode_5964 : decode runtimeBytecode ⟨5964⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨19, by decide⟩
theorem decode_5965 : decode runtimeBytecode ⟨5965⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨20, by decide⟩
theorem decode_5968 : decode runtimeBytecode ⟨5968⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨21, by decide⟩
theorem decode_5969 : decode runtimeBytecode ⟨5969⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨22, by decide⟩
theorem decode_5970 : decode runtimeBytecode ⟨5970⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨23, by decide⟩
theorem decode_5971 : decode runtimeBytecode ⟨5971⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨24, by decide⟩
theorem decode_5972 : decode runtimeBytecode ⟨5972⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨25, by decide⟩
theorem decode_5973 : decode runtimeBytecode ⟨5973⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨26, by decide⟩
theorem decode_5974 : decode runtimeBytecode ⟨5974⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨27, by decide⟩
theorem decode_5975 : decode runtimeBytecode ⟨5975⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨28, by decide⟩
theorem decode_5976 : decode runtimeBytecode ⟨5976⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨29, by decide⟩
theorem decode_5977 : decode runtimeBytecode ⟨5977⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨30, by decide⟩
theorem decode_5979 : decode runtimeBytecode ⟨5979⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨31, by decide⟩
theorem decode_5980 : decode runtimeBytecode ⟨5980⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨32, by decide⟩
theorem decode_5981 : decode runtimeBytecode ⟨5981⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨33, by decide⟩
theorem decode_5982 : decode runtimeBytecode ⟨5982⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨34, by decide⟩
theorem decode_5983 : decode runtimeBytecode ⟨5983⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨35, by decide⟩
theorem decode_5984 : decode runtimeBytecode ⟨5984⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨36, by decide⟩
theorem decode_5987 : decode runtimeBytecode ⟨5987⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨37, by decide⟩
theorem decode_5988 : decode runtimeBytecode ⟨5988⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨38, by decide⟩
theorem decode_5989 : decode runtimeBytecode ⟨5989⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨39, by decide⟩
theorem decode_5990 : decode runtimeBytecode ⟨5990⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨40, by decide⟩
theorem decode_5991 : decode runtimeBytecode ⟨5991⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨41, by decide⟩
theorem decode_5992 : decode runtimeBytecode ⟨5992⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨42, by decide⟩
theorem decode_5993 : decode runtimeBytecode ⟨5993⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨43, by decide⟩
theorem decode_5994 : decode runtimeBytecode ⟨5994⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨44, by decide⟩
theorem decode_5995 : decode runtimeBytecode ⟨5995⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨45, by decide⟩
theorem decode_5996 : decode runtimeBytecode ⟨5996⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨46, by decide⟩
theorem decode_5998 : decode runtimeBytecode ⟨5998⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨47, by decide⟩
theorem decode_5999 : decode runtimeBytecode ⟨5999⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨48, by decide⟩
theorem decode_6000 : decode runtimeBytecode ⟨6000⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨49, by decide⟩
theorem decode_6001 : decode runtimeBytecode ⟨6001⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨50, by decide⟩
theorem decode_6002 : decode runtimeBytecode ⟨6002⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨51, by decide⟩
theorem decode_6003 : decode runtimeBytecode ⟨6003⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨52, by decide⟩
theorem decode_6006 : decode runtimeBytecode ⟨6006⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨53, by decide⟩
theorem decode_6007 : decode runtimeBytecode ⟨6007⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨54, by decide⟩
theorem decode_6008 : decode runtimeBytecode ⟨6008⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨55, by decide⟩
theorem decode_6009 : decode runtimeBytecode ⟨6009⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨56, by decide⟩
theorem decode_6010 : decode runtimeBytecode ⟨6010⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨57, by decide⟩
theorem decode_6011 : decode runtimeBytecode ⟨6011⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨58, by decide⟩
theorem decode_6012 : decode runtimeBytecode ⟨6012⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨59, by decide⟩
theorem decode_6013 : decode runtimeBytecode ⟨6013⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨60, by decide⟩
theorem decode_6014 : decode runtimeBytecode ⟨6014⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨61, by decide⟩
theorem decode_6015 : decode runtimeBytecode ⟨6015⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨62, by decide⟩
theorem decode_6017 : decode runtimeBytecode ⟨6017⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨63, by decide⟩
theorem decode_6018 : decode runtimeBytecode ⟨6018⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨64, by decide⟩
theorem decode_6019 : decode runtimeBytecode ⟨6019⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨65, by decide⟩
theorem decode_6020 : decode runtimeBytecode ⟨6020⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨66, by decide⟩
theorem decode_6021 : decode runtimeBytecode ⟨6021⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨67, by decide⟩
theorem decode_6022 : decode runtimeBytecode ⟨6022⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨68, by decide⟩
theorem decode_6025 : decode runtimeBytecode ⟨6025⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨69, by decide⟩
theorem decode_6026 : decode runtimeBytecode ⟨6026⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨70, by decide⟩
theorem decode_6027 : decode runtimeBytecode ⟨6027⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨71, by decide⟩
theorem decode_6028 : decode runtimeBytecode ⟨6028⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨72, by decide⟩
theorem decode_6029 : decode runtimeBytecode ⟨6029⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨73, by decide⟩
theorem decode_6030 : decode runtimeBytecode ⟨6030⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨74, by decide⟩
theorem decode_6031 : decode runtimeBytecode ⟨6031⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨75, by decide⟩
theorem decode_6032 : decode runtimeBytecode ⟨6032⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨76, by decide⟩
theorem decode_6033 : decode runtimeBytecode ⟨6033⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨77, by decide⟩
theorem decode_6034 : decode runtimeBytecode ⟨6034⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨78, by decide⟩
theorem decode_6036 : decode runtimeBytecode ⟨6036⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨79, by decide⟩
theorem decode_6037 : decode runtimeBytecode ⟨6037⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨80, by decide⟩
theorem decode_6038 : decode runtimeBytecode ⟨6038⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨81, by decide⟩
theorem decode_6039 : decode runtimeBytecode ⟨6039⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨82, by decide⟩
theorem decode_6040 : decode runtimeBytecode ⟨6040⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨83, by decide⟩
theorem decode_6041 : decode runtimeBytecode ⟨6041⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨84, by decide⟩
theorem decode_6044 : decode runtimeBytecode ⟨6044⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨85, by decide⟩
theorem decode_6045 : decode runtimeBytecode ⟨6045⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨86, by decide⟩
theorem decode_6046 : decode runtimeBytecode ⟨6046⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨87, by decide⟩
theorem decode_6047 : decode runtimeBytecode ⟨6047⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨88, by decide⟩
theorem decode_6048 : decode runtimeBytecode ⟨6048⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨89, by decide⟩
theorem decode_6049 : decode runtimeBytecode ⟨6049⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨90, by decide⟩
theorem decode_6050 : decode runtimeBytecode ⟨6050⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨91, by decide⟩
theorem decode_6051 : decode runtimeBytecode ⟨6051⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨92, by decide⟩
theorem decode_6052 : decode runtimeBytecode ⟨6052⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨93, by decide⟩
theorem decode_6053 : decode runtimeBytecode ⟨6053⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨94, by decide⟩
theorem decode_6055 : decode runtimeBytecode ⟨6055⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨95, by decide⟩
theorem decode_6056 : decode runtimeBytecode ⟨6056⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨96, by decide⟩
theorem decode_6057 : decode runtimeBytecode ⟨6057⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨97, by decide⟩
theorem decode_6058 : decode runtimeBytecode ⟨6058⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨98, by decide⟩
theorem decode_6059 : decode runtimeBytecode ⟨6059⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes43] using generatedDecodes43_correct ⟨99, by decide⟩

end Ripemd160Old
