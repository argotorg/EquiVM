import Examples.Ripemd160Old.DecodeGenerated.Chunk04

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes5 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨914⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨915⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨916⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨917⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨919⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨920⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨921⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨922⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨923⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨924⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨927⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨928⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨929⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨930⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨931⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨932⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨933⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨934⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨935⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨936⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨938⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨939⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨940⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨941⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨942⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨943⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨946⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨947⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨948⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨949⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨950⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨951⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨952⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨953⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨954⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨955⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨957⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨958⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨959⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨960⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨961⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨962⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨965⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨966⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨967⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨968⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨969⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨970⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨971⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨972⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨973⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨974⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨976⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨977⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨978⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨979⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨980⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨981⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨984⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨985⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨986⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨987⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨989⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨990⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨991⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨992⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨993⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨994⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨995⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨996⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨997⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1412⟩, 2))),
  (⟨1000⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1001⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1002⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨1004⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1005⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1393⟩, 2))),
  (⟨1008⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1009⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1010⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨1012⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1013⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1374⟩, 2))),
  (⟨1016⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1017⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1018⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨1020⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1021⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1355⟩, 2))),
  (⟨1024⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1025⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1026⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨1028⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1029⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1336⟩, 2))),
  (⟨1032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1033⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1034⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1036⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1037⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1317⟩, 2))),
  (⟨1040⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1041⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1042⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1044⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes5_correct : ∀ i : Fin generatedDecodes5.size,
    decode runtimeBytecode generatedDecodes5[i].1 = generatedDecodes5[i].2 := by
  native_decide

theorem decode_914 : decode runtimeBytecode ⟨914⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨0, by decide⟩
theorem decode_915 : decode runtimeBytecode ⟨915⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨1, by decide⟩
theorem decode_916 : decode runtimeBytecode ⟨916⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨2, by decide⟩
theorem decode_917 : decode runtimeBytecode ⟨917⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨3, by decide⟩
theorem decode_919 : decode runtimeBytecode ⟨919⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨4, by decide⟩
theorem decode_920 : decode runtimeBytecode ⟨920⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨5, by decide⟩
theorem decode_921 : decode runtimeBytecode ⟨921⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨6, by decide⟩
theorem decode_922 : decode runtimeBytecode ⟨922⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨7, by decide⟩
theorem decode_923 : decode runtimeBytecode ⟨923⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨8, by decide⟩
theorem decode_924 : decode runtimeBytecode ⟨924⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨9, by decide⟩
theorem decode_927 : decode runtimeBytecode ⟨927⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨10, by decide⟩
theorem decode_928 : decode runtimeBytecode ⟨928⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨11, by decide⟩
theorem decode_929 : decode runtimeBytecode ⟨929⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨12, by decide⟩
theorem decode_930 : decode runtimeBytecode ⟨930⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨13, by decide⟩
theorem decode_931 : decode runtimeBytecode ⟨931⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨14, by decide⟩
theorem decode_932 : decode runtimeBytecode ⟨932⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨15, by decide⟩
theorem decode_933 : decode runtimeBytecode ⟨933⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨16, by decide⟩
theorem decode_934 : decode runtimeBytecode ⟨934⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨17, by decide⟩
theorem decode_935 : decode runtimeBytecode ⟨935⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨18, by decide⟩
theorem decode_936 : decode runtimeBytecode ⟨936⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨19, by decide⟩
theorem decode_938 : decode runtimeBytecode ⟨938⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨20, by decide⟩
theorem decode_939 : decode runtimeBytecode ⟨939⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨21, by decide⟩
theorem decode_940 : decode runtimeBytecode ⟨940⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨22, by decide⟩
theorem decode_941 : decode runtimeBytecode ⟨941⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨23, by decide⟩
theorem decode_942 : decode runtimeBytecode ⟨942⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨24, by decide⟩
theorem decode_943 : decode runtimeBytecode ⟨943⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨25, by decide⟩
theorem decode_946 : decode runtimeBytecode ⟨946⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨26, by decide⟩
theorem decode_947 : decode runtimeBytecode ⟨947⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨27, by decide⟩
theorem decode_948 : decode runtimeBytecode ⟨948⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨28, by decide⟩
theorem decode_949 : decode runtimeBytecode ⟨949⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨29, by decide⟩
theorem decode_950 : decode runtimeBytecode ⟨950⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨30, by decide⟩
theorem decode_951 : decode runtimeBytecode ⟨951⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨31, by decide⟩
theorem decode_952 : decode runtimeBytecode ⟨952⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨32, by decide⟩
theorem decode_953 : decode runtimeBytecode ⟨953⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨33, by decide⟩
theorem decode_954 : decode runtimeBytecode ⟨954⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨34, by decide⟩
theorem decode_955 : decode runtimeBytecode ⟨955⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨35, by decide⟩
theorem decode_957 : decode runtimeBytecode ⟨957⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨36, by decide⟩
theorem decode_958 : decode runtimeBytecode ⟨958⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨37, by decide⟩
theorem decode_959 : decode runtimeBytecode ⟨959⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨38, by decide⟩
theorem decode_960 : decode runtimeBytecode ⟨960⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨39, by decide⟩
theorem decode_961 : decode runtimeBytecode ⟨961⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨40, by decide⟩
theorem decode_962 : decode runtimeBytecode ⟨962⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨41, by decide⟩
theorem decode_965 : decode runtimeBytecode ⟨965⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨42, by decide⟩
theorem decode_966 : decode runtimeBytecode ⟨966⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨43, by decide⟩
theorem decode_967 : decode runtimeBytecode ⟨967⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨44, by decide⟩
theorem decode_968 : decode runtimeBytecode ⟨968⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨45, by decide⟩
theorem decode_969 : decode runtimeBytecode ⟨969⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨46, by decide⟩
theorem decode_970 : decode runtimeBytecode ⟨970⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨47, by decide⟩
theorem decode_971 : decode runtimeBytecode ⟨971⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨48, by decide⟩
theorem decode_972 : decode runtimeBytecode ⟨972⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨49, by decide⟩
theorem decode_973 : decode runtimeBytecode ⟨973⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨50, by decide⟩
theorem decode_974 : decode runtimeBytecode ⟨974⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨51, by decide⟩
theorem decode_976 : decode runtimeBytecode ⟨976⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨52, by decide⟩
theorem decode_977 : decode runtimeBytecode ⟨977⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨53, by decide⟩
theorem decode_978 : decode runtimeBytecode ⟨978⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨54, by decide⟩
theorem decode_979 : decode runtimeBytecode ⟨979⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨55, by decide⟩
theorem decode_980 : decode runtimeBytecode ⟨980⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨56, by decide⟩
theorem decode_981 : decode runtimeBytecode ⟨981⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨57, by decide⟩
theorem decode_984 : decode runtimeBytecode ⟨984⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨58, by decide⟩
theorem decode_985 : decode runtimeBytecode ⟨985⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨59, by decide⟩
theorem decode_986 : decode runtimeBytecode ⟨986⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨60, by decide⟩
theorem decode_987 : decode runtimeBytecode ⟨987⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨61, by decide⟩
theorem decode_989 : decode runtimeBytecode ⟨989⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨62, by decide⟩
theorem decode_990 : decode runtimeBytecode ⟨990⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨63, by decide⟩
theorem decode_991 : decode runtimeBytecode ⟨991⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨64, by decide⟩
theorem decode_992 : decode runtimeBytecode ⟨992⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨65, by decide⟩
theorem decode_993 : decode runtimeBytecode ⟨993⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨66, by decide⟩
theorem decode_994 : decode runtimeBytecode ⟨994⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨67, by decide⟩
theorem decode_995 : decode runtimeBytecode ⟨995⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨68, by decide⟩
theorem decode_996 : decode runtimeBytecode ⟨996⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨69, by decide⟩
theorem decode_997 : decode runtimeBytecode ⟨997⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1412⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨70, by decide⟩
theorem decode_1000 : decode runtimeBytecode ⟨1000⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨71, by decide⟩
theorem decode_1001 : decode runtimeBytecode ⟨1001⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨72, by decide⟩
theorem decode_1002 : decode runtimeBytecode ⟨1002⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨73, by decide⟩
theorem decode_1004 : decode runtimeBytecode ⟨1004⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨74, by decide⟩
theorem decode_1005 : decode runtimeBytecode ⟨1005⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1393⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨75, by decide⟩
theorem decode_1008 : decode runtimeBytecode ⟨1008⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨76, by decide⟩
theorem decode_1009 : decode runtimeBytecode ⟨1009⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨77, by decide⟩
theorem decode_1010 : decode runtimeBytecode ⟨1010⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨78, by decide⟩
theorem decode_1012 : decode runtimeBytecode ⟨1012⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨79, by decide⟩
theorem decode_1013 : decode runtimeBytecode ⟨1013⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1374⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨80, by decide⟩
theorem decode_1016 : decode runtimeBytecode ⟨1016⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨81, by decide⟩
theorem decode_1017 : decode runtimeBytecode ⟨1017⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨82, by decide⟩
theorem decode_1018 : decode runtimeBytecode ⟨1018⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨83, by decide⟩
theorem decode_1020 : decode runtimeBytecode ⟨1020⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨84, by decide⟩
theorem decode_1021 : decode runtimeBytecode ⟨1021⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1355⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨85, by decide⟩
theorem decode_1024 : decode runtimeBytecode ⟨1024⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨86, by decide⟩
theorem decode_1025 : decode runtimeBytecode ⟨1025⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨87, by decide⟩
theorem decode_1026 : decode runtimeBytecode ⟨1026⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨88, by decide⟩
theorem decode_1028 : decode runtimeBytecode ⟨1028⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨89, by decide⟩
theorem decode_1029 : decode runtimeBytecode ⟨1029⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1336⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨90, by decide⟩
theorem decode_1032 : decode runtimeBytecode ⟨1032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨91, by decide⟩
theorem decode_1033 : decode runtimeBytecode ⟨1033⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨92, by decide⟩
theorem decode_1034 : decode runtimeBytecode ⟨1034⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨93, by decide⟩
theorem decode_1036 : decode runtimeBytecode ⟨1036⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨94, by decide⟩
theorem decode_1037 : decode runtimeBytecode ⟨1037⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1317⟩, 2)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨95, by decide⟩
theorem decode_1040 : decode runtimeBytecode ⟨1040⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨96, by decide⟩
theorem decode_1041 : decode runtimeBytecode ⟨1041⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨97, by decide⟩
theorem decode_1042 : decode runtimeBytecode ⟨1042⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨98, by decide⟩
theorem decode_1044 : decode runtimeBytecode ⟨1044⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes5] using generatedDecodes5_correct ⟨99, by decide⟩

end Ripemd160Old
