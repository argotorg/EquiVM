import Examples.Ripemd160Old.DecodeGenerated.Chunk41

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes42 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨5821⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨5823⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨5824⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5837⟩, 2))),
  (⟨5827⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨5828⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5829⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5830⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5831⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5832⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨5833⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2))),
  (⟨5836⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5837⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5838⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5839⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5840⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5841⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5842⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5843⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5844⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨5846⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5847⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5848⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5849⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5850⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5851⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5854⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5855⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5856⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5857⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5858⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5859⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5860⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5861⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5862⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5863⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨5865⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5866⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5867⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5868⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5869⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5870⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5873⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5874⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5875⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5876⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5877⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5878⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5879⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5880⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5881⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5882⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨5884⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5885⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5886⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5887⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5888⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5889⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5892⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5893⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5894⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5895⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5896⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5897⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5898⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5899⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5900⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5901⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨5903⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5904⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5905⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5906⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5907⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5908⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5911⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5912⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5913⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5914⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5915⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5916⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5917⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5918⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5919⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5920⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨5922⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨5923⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5924⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨5925⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5926⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5927⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2))),
  (⟨5930⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨5931⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨5932⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5933⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨5934⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨5935⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨5936⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨5937⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨5938⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨5939⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨5941⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none))
]

private theorem generatedDecodes42_correct : ∀ i : Fin generatedDecodes42.size,
    decode runtimeBytecode generatedDecodes42[i].1 = generatedDecodes42[i].2 := by
  native_decide

theorem decode_5821 : decode runtimeBytecode ⟨5821⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨0, by decide⟩
theorem decode_5823 : decode runtimeBytecode ⟨5823⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨1, by decide⟩
theorem decode_5824 : decode runtimeBytecode ⟨5824⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5837⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨2, by decide⟩
theorem decode_5827 : decode runtimeBytecode ⟨5827⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨3, by decide⟩
theorem decode_5828 : decode runtimeBytecode ⟨5828⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨4, by decide⟩
theorem decode_5829 : decode runtimeBytecode ⟨5829⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨5, by decide⟩
theorem decode_5830 : decode runtimeBytecode ⟨5830⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨6, by decide⟩
theorem decode_5831 : decode runtimeBytecode ⟨5831⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨7, by decide⟩
theorem decode_5832 : decode runtimeBytecode ⟨5832⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨8, by decide⟩
theorem decode_5833 : decode runtimeBytecode ⟨5833⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4311⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨9, by decide⟩
theorem decode_5836 : decode runtimeBytecode ⟨5836⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨10, by decide⟩
theorem decode_5837 : decode runtimeBytecode ⟨5837⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨11, by decide⟩
theorem decode_5838 : decode runtimeBytecode ⟨5838⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨12, by decide⟩
theorem decode_5839 : decode runtimeBytecode ⟨5839⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨13, by decide⟩
theorem decode_5840 : decode runtimeBytecode ⟨5840⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨14, by decide⟩
theorem decode_5841 : decode runtimeBytecode ⟨5841⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨15, by decide⟩
theorem decode_5842 : decode runtimeBytecode ⟨5842⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨16, by decide⟩
theorem decode_5843 : decode runtimeBytecode ⟨5843⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨17, by decide⟩
theorem decode_5844 : decode runtimeBytecode ⟨5844⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨18, by decide⟩
theorem decode_5846 : decode runtimeBytecode ⟨5846⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨19, by decide⟩
theorem decode_5847 : decode runtimeBytecode ⟨5847⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨20, by decide⟩
theorem decode_5848 : decode runtimeBytecode ⟨5848⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨21, by decide⟩
theorem decode_5849 : decode runtimeBytecode ⟨5849⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨22, by decide⟩
theorem decode_5850 : decode runtimeBytecode ⟨5850⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨23, by decide⟩
theorem decode_5851 : decode runtimeBytecode ⟨5851⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨24, by decide⟩
theorem decode_5854 : decode runtimeBytecode ⟨5854⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨25, by decide⟩
theorem decode_5855 : decode runtimeBytecode ⟨5855⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨26, by decide⟩
theorem decode_5856 : decode runtimeBytecode ⟨5856⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨27, by decide⟩
theorem decode_5857 : decode runtimeBytecode ⟨5857⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨28, by decide⟩
theorem decode_5858 : decode runtimeBytecode ⟨5858⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨29, by decide⟩
theorem decode_5859 : decode runtimeBytecode ⟨5859⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨30, by decide⟩
theorem decode_5860 : decode runtimeBytecode ⟨5860⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨31, by decide⟩
theorem decode_5861 : decode runtimeBytecode ⟨5861⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨32, by decide⟩
theorem decode_5862 : decode runtimeBytecode ⟨5862⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨33, by decide⟩
theorem decode_5863 : decode runtimeBytecode ⟨5863⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨34, by decide⟩
theorem decode_5865 : decode runtimeBytecode ⟨5865⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨35, by decide⟩
theorem decode_5866 : decode runtimeBytecode ⟨5866⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨36, by decide⟩
theorem decode_5867 : decode runtimeBytecode ⟨5867⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨37, by decide⟩
theorem decode_5868 : decode runtimeBytecode ⟨5868⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨38, by decide⟩
theorem decode_5869 : decode runtimeBytecode ⟨5869⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨39, by decide⟩
theorem decode_5870 : decode runtimeBytecode ⟨5870⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨40, by decide⟩
theorem decode_5873 : decode runtimeBytecode ⟨5873⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨41, by decide⟩
theorem decode_5874 : decode runtimeBytecode ⟨5874⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨42, by decide⟩
theorem decode_5875 : decode runtimeBytecode ⟨5875⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨43, by decide⟩
theorem decode_5876 : decode runtimeBytecode ⟨5876⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨44, by decide⟩
theorem decode_5877 : decode runtimeBytecode ⟨5877⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨45, by decide⟩
theorem decode_5878 : decode runtimeBytecode ⟨5878⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨46, by decide⟩
theorem decode_5879 : decode runtimeBytecode ⟨5879⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨47, by decide⟩
theorem decode_5880 : decode runtimeBytecode ⟨5880⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨48, by decide⟩
theorem decode_5881 : decode runtimeBytecode ⟨5881⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨49, by decide⟩
theorem decode_5882 : decode runtimeBytecode ⟨5882⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨50, by decide⟩
theorem decode_5884 : decode runtimeBytecode ⟨5884⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨51, by decide⟩
theorem decode_5885 : decode runtimeBytecode ⟨5885⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨52, by decide⟩
theorem decode_5886 : decode runtimeBytecode ⟨5886⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨53, by decide⟩
theorem decode_5887 : decode runtimeBytecode ⟨5887⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨54, by decide⟩
theorem decode_5888 : decode runtimeBytecode ⟨5888⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨55, by decide⟩
theorem decode_5889 : decode runtimeBytecode ⟨5889⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨56, by decide⟩
theorem decode_5892 : decode runtimeBytecode ⟨5892⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨57, by decide⟩
theorem decode_5893 : decode runtimeBytecode ⟨5893⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨58, by decide⟩
theorem decode_5894 : decode runtimeBytecode ⟨5894⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨59, by decide⟩
theorem decode_5895 : decode runtimeBytecode ⟨5895⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨60, by decide⟩
theorem decode_5896 : decode runtimeBytecode ⟨5896⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨61, by decide⟩
theorem decode_5897 : decode runtimeBytecode ⟨5897⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨62, by decide⟩
theorem decode_5898 : decode runtimeBytecode ⟨5898⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨63, by decide⟩
theorem decode_5899 : decode runtimeBytecode ⟨5899⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨64, by decide⟩
theorem decode_5900 : decode runtimeBytecode ⟨5900⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨65, by decide⟩
theorem decode_5901 : decode runtimeBytecode ⟨5901⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨66, by decide⟩
theorem decode_5903 : decode runtimeBytecode ⟨5903⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨67, by decide⟩
theorem decode_5904 : decode runtimeBytecode ⟨5904⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨68, by decide⟩
theorem decode_5905 : decode runtimeBytecode ⟨5905⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨69, by decide⟩
theorem decode_5906 : decode runtimeBytecode ⟨5906⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨70, by decide⟩
theorem decode_5907 : decode runtimeBytecode ⟨5907⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨71, by decide⟩
theorem decode_5908 : decode runtimeBytecode ⟨5908⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨72, by decide⟩
theorem decode_5911 : decode runtimeBytecode ⟨5911⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨73, by decide⟩
theorem decode_5912 : decode runtimeBytecode ⟨5912⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨74, by decide⟩
theorem decode_5913 : decode runtimeBytecode ⟨5913⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨75, by decide⟩
theorem decode_5914 : decode runtimeBytecode ⟨5914⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨76, by decide⟩
theorem decode_5915 : decode runtimeBytecode ⟨5915⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨77, by decide⟩
theorem decode_5916 : decode runtimeBytecode ⟨5916⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨78, by decide⟩
theorem decode_5917 : decode runtimeBytecode ⟨5917⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨79, by decide⟩
theorem decode_5918 : decode runtimeBytecode ⟨5918⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨80, by decide⟩
theorem decode_5919 : decode runtimeBytecode ⟨5919⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨81, by decide⟩
theorem decode_5920 : decode runtimeBytecode ⟨5920⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨82, by decide⟩
theorem decode_5922 : decode runtimeBytecode ⟨5922⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨83, by decide⟩
theorem decode_5923 : decode runtimeBytecode ⟨5923⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨84, by decide⟩
theorem decode_5924 : decode runtimeBytecode ⟨5924⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨85, by decide⟩
theorem decode_5925 : decode runtimeBytecode ⟨5925⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨86, by decide⟩
theorem decode_5926 : decode runtimeBytecode ⟨5926⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨87, by decide⟩
theorem decode_5927 : decode runtimeBytecode ⟨5927⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5828⟩, 2)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨88, by decide⟩
theorem decode_5930 : decode runtimeBytecode ⟨5930⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨89, by decide⟩
theorem decode_5931 : decode runtimeBytecode ⟨5931⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨90, by decide⟩
theorem decode_5932 : decode runtimeBytecode ⟨5932⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨91, by decide⟩
theorem decode_5933 : decode runtimeBytecode ⟨5933⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨92, by decide⟩
theorem decode_5934 : decode runtimeBytecode ⟨5934⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨93, by decide⟩
theorem decode_5935 : decode runtimeBytecode ⟨5935⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨94, by decide⟩
theorem decode_5936 : decode runtimeBytecode ⟨5936⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨95, by decide⟩
theorem decode_5937 : decode runtimeBytecode ⟨5937⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨96, by decide⟩
theorem decode_5938 : decode runtimeBytecode ⟨5938⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨97, by decide⟩
theorem decode_5939 : decode runtimeBytecode ⟨5939⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨98, by decide⟩
theorem decode_5941 : decode runtimeBytecode ⟨5941⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes42] using generatedDecodes42_correct ⟨99, by decide⟩

end Ripemd160Old
