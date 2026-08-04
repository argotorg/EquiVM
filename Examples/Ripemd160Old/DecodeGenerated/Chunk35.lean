import Examples.Ripemd160Old.DecodeGenerated.Chunk34

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes35 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4925⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4963⟩, 2))),
  (⟨4928⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4929⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨4931⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4932⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4945⟩, 2))),
  (⟨4935⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4936⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4937⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4938⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4939⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4940⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4941⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2))),
  (⟨4944⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4945⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4946⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4947⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4948⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4949⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4950⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4951⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4952⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨4954⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4955⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4956⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4957⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4958⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4959⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨4962⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4963⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4964⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4965⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4966⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4967⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4968⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4969⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4970⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4971⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨4973⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4974⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4975⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4976⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4977⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4978⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨4981⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4982⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4983⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4984⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4985⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4986⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4987⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4988⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4989⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4990⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4992⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4993⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4994⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4995⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4996⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4997⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5000⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5001⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5002⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5003⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5004⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5005⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5006⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5007⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5008⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5009⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5011⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5012⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5013⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5014⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5015⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5016⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5019⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5020⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5021⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5022⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5023⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5024⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5025⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5026⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5027⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5028⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨5030⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5031⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5032⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5033⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5034⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5035⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2))),
  (⟨5038⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5039⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5040⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5041⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5042⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5043⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5044⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5045⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5046⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none))
]

private theorem generatedDecodes35_correct : ∀ i : Fin generatedDecodes35.size,
    decode runtimeBytecode generatedDecodes35[i].1 = generatedDecodes35[i].2 := by
  native_decide

theorem decode_4925 : decode runtimeBytecode ⟨4925⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4963⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨0, by decide⟩
theorem decode_4928 : decode runtimeBytecode ⟨4928⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨1, by decide⟩
theorem decode_4929 : decode runtimeBytecode ⟨4929⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨2, by decide⟩
theorem decode_4931 : decode runtimeBytecode ⟨4931⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨3, by decide⟩
theorem decode_4932 : decode runtimeBytecode ⟨4932⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4945⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨4, by decide⟩
theorem decode_4935 : decode runtimeBytecode ⟨4935⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨5, by decide⟩
theorem decode_4936 : decode runtimeBytecode ⟨4936⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨6, by decide⟩
theorem decode_4937 : decode runtimeBytecode ⟨4937⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨7, by decide⟩
theorem decode_4938 : decode runtimeBytecode ⟨4938⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨8, by decide⟩
theorem decode_4939 : decode runtimeBytecode ⟨4939⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨9, by decide⟩
theorem decode_4940 : decode runtimeBytecode ⟨4940⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨10, by decide⟩
theorem decode_4941 : decode runtimeBytecode ⟨4941⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨11, by decide⟩
theorem decode_4944 : decode runtimeBytecode ⟨4944⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨12, by decide⟩
theorem decode_4945 : decode runtimeBytecode ⟨4945⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨13, by decide⟩
theorem decode_4946 : decode runtimeBytecode ⟨4946⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨14, by decide⟩
theorem decode_4947 : decode runtimeBytecode ⟨4947⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨15, by decide⟩
theorem decode_4948 : decode runtimeBytecode ⟨4948⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨16, by decide⟩
theorem decode_4949 : decode runtimeBytecode ⟨4949⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨17, by decide⟩
theorem decode_4950 : decode runtimeBytecode ⟨4950⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨18, by decide⟩
theorem decode_4951 : decode runtimeBytecode ⟨4951⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨19, by decide⟩
theorem decode_4952 : decode runtimeBytecode ⟨4952⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨20, by decide⟩
theorem decode_4954 : decode runtimeBytecode ⟨4954⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨21, by decide⟩
theorem decode_4955 : decode runtimeBytecode ⟨4955⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨22, by decide⟩
theorem decode_4956 : decode runtimeBytecode ⟨4956⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨23, by decide⟩
theorem decode_4957 : decode runtimeBytecode ⟨4957⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨24, by decide⟩
theorem decode_4958 : decode runtimeBytecode ⟨4958⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨25, by decide⟩
theorem decode_4959 : decode runtimeBytecode ⟨4959⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨26, by decide⟩
theorem decode_4962 : decode runtimeBytecode ⟨4962⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨27, by decide⟩
theorem decode_4963 : decode runtimeBytecode ⟨4963⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨28, by decide⟩
theorem decode_4964 : decode runtimeBytecode ⟨4964⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨29, by decide⟩
theorem decode_4965 : decode runtimeBytecode ⟨4965⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨30, by decide⟩
theorem decode_4966 : decode runtimeBytecode ⟨4966⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨31, by decide⟩
theorem decode_4967 : decode runtimeBytecode ⟨4967⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨32, by decide⟩
theorem decode_4968 : decode runtimeBytecode ⟨4968⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨33, by decide⟩
theorem decode_4969 : decode runtimeBytecode ⟨4969⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨34, by decide⟩
theorem decode_4970 : decode runtimeBytecode ⟨4970⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨35, by decide⟩
theorem decode_4971 : decode runtimeBytecode ⟨4971⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨36, by decide⟩
theorem decode_4973 : decode runtimeBytecode ⟨4973⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨37, by decide⟩
theorem decode_4974 : decode runtimeBytecode ⟨4974⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨38, by decide⟩
theorem decode_4975 : decode runtimeBytecode ⟨4975⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨39, by decide⟩
theorem decode_4976 : decode runtimeBytecode ⟨4976⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨40, by decide⟩
theorem decode_4977 : decode runtimeBytecode ⟨4977⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨41, by decide⟩
theorem decode_4978 : decode runtimeBytecode ⟨4978⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨42, by decide⟩
theorem decode_4981 : decode runtimeBytecode ⟨4981⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨43, by decide⟩
theorem decode_4982 : decode runtimeBytecode ⟨4982⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨44, by decide⟩
theorem decode_4983 : decode runtimeBytecode ⟨4983⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨45, by decide⟩
theorem decode_4984 : decode runtimeBytecode ⟨4984⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨46, by decide⟩
theorem decode_4985 : decode runtimeBytecode ⟨4985⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨47, by decide⟩
theorem decode_4986 : decode runtimeBytecode ⟨4986⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨48, by decide⟩
theorem decode_4987 : decode runtimeBytecode ⟨4987⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨49, by decide⟩
theorem decode_4988 : decode runtimeBytecode ⟨4988⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨50, by decide⟩
theorem decode_4989 : decode runtimeBytecode ⟨4989⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨51, by decide⟩
theorem decode_4990 : decode runtimeBytecode ⟨4990⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨52, by decide⟩
theorem decode_4992 : decode runtimeBytecode ⟨4992⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨53, by decide⟩
theorem decode_4993 : decode runtimeBytecode ⟨4993⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨54, by decide⟩
theorem decode_4994 : decode runtimeBytecode ⟨4994⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨55, by decide⟩
theorem decode_4995 : decode runtimeBytecode ⟨4995⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨56, by decide⟩
theorem decode_4996 : decode runtimeBytecode ⟨4996⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨57, by decide⟩
theorem decode_4997 : decode runtimeBytecode ⟨4997⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨58, by decide⟩
theorem decode_5000 : decode runtimeBytecode ⟨5000⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨59, by decide⟩
theorem decode_5001 : decode runtimeBytecode ⟨5001⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨60, by decide⟩
theorem decode_5002 : decode runtimeBytecode ⟨5002⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨61, by decide⟩
theorem decode_5003 : decode runtimeBytecode ⟨5003⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨62, by decide⟩
theorem decode_5004 : decode runtimeBytecode ⟨5004⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨63, by decide⟩
theorem decode_5005 : decode runtimeBytecode ⟨5005⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨64, by decide⟩
theorem decode_5006 : decode runtimeBytecode ⟨5006⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨65, by decide⟩
theorem decode_5007 : decode runtimeBytecode ⟨5007⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨66, by decide⟩
theorem decode_5008 : decode runtimeBytecode ⟨5008⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨67, by decide⟩
theorem decode_5009 : decode runtimeBytecode ⟨5009⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨68, by decide⟩
theorem decode_5011 : decode runtimeBytecode ⟨5011⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨69, by decide⟩
theorem decode_5012 : decode runtimeBytecode ⟨5012⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨70, by decide⟩
theorem decode_5013 : decode runtimeBytecode ⟨5013⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨71, by decide⟩
theorem decode_5014 : decode runtimeBytecode ⟨5014⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨72, by decide⟩
theorem decode_5015 : decode runtimeBytecode ⟨5015⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨73, by decide⟩
theorem decode_5016 : decode runtimeBytecode ⟨5016⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨74, by decide⟩
theorem decode_5019 : decode runtimeBytecode ⟨5019⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨75, by decide⟩
theorem decode_5020 : decode runtimeBytecode ⟨5020⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨76, by decide⟩
theorem decode_5021 : decode runtimeBytecode ⟨5021⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨77, by decide⟩
theorem decode_5022 : decode runtimeBytecode ⟨5022⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨78, by decide⟩
theorem decode_5023 : decode runtimeBytecode ⟨5023⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨79, by decide⟩
theorem decode_5024 : decode runtimeBytecode ⟨5024⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨80, by decide⟩
theorem decode_5025 : decode runtimeBytecode ⟨5025⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨81, by decide⟩
theorem decode_5026 : decode runtimeBytecode ⟨5026⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨82, by decide⟩
theorem decode_5027 : decode runtimeBytecode ⟨5027⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨83, by decide⟩
theorem decode_5028 : decode runtimeBytecode ⟨5028⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨84, by decide⟩
theorem decode_5030 : decode runtimeBytecode ⟨5030⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨85, by decide⟩
theorem decode_5031 : decode runtimeBytecode ⟨5031⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨86, by decide⟩
theorem decode_5032 : decode runtimeBytecode ⟨5032⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨87, by decide⟩
theorem decode_5033 : decode runtimeBytecode ⟨5033⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨88, by decide⟩
theorem decode_5034 : decode runtimeBytecode ⟨5034⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨89, by decide⟩
theorem decode_5035 : decode runtimeBytecode ⟨5035⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4936⟩, 2)) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨90, by decide⟩
theorem decode_5038 : decode runtimeBytecode ⟨5038⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨91, by decide⟩
theorem decode_5039 : decode runtimeBytecode ⟨5039⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨92, by decide⟩
theorem decode_5040 : decode runtimeBytecode ⟨5040⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨93, by decide⟩
theorem decode_5041 : decode runtimeBytecode ⟨5041⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨94, by decide⟩
theorem decode_5042 : decode runtimeBytecode ⟨5042⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨95, by decide⟩
theorem decode_5043 : decode runtimeBytecode ⟨5043⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨96, by decide⟩
theorem decode_5044 : decode runtimeBytecode ⟨5044⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨97, by decide⟩
theorem decode_5045 : decode runtimeBytecode ⟨5045⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨98, by decide⟩
theorem decode_5046 : decode runtimeBytecode ⟨5046⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes35] using generatedDecodes35_correct ⟨99, by decide⟩

end Ripemd160Old
