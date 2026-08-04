import Examples.Ripemd160Old.DecodeGenerated.Chunk63

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes64 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8831⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8832⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8833⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8836⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none)),
  (⟨8837⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8838⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8840⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8841⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8843⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8844⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8845⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨8846⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8849⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP12), none)),
  (⟨8850⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8851⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8853⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8854⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8856⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8857⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8858⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨8859⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8862⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none)),
  (⟨8863⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8864⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8866⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8867⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8869⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8870⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8871⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8872⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8875⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨8876⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8877⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8879⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8880⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8882⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8883⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8884⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8885⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8886⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8887⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8892⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8893⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP13), none)),
  (⟨8894⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8895⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8896⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8901⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8902⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none)),
  (⟨8903⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8904⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8905⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8910⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8911⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP11), none)),
  (⟨8912⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8913⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8914⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8919⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8920⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨8921⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8922⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8923⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4))),
  (⟨8928⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8929⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none)),
  (⟨8930⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8931⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨8933⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8935⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8936⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8937⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨8938⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8939⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8940⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8941⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8942⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8533⟩, 2))),
  (⟨8945⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8946⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8947⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8948⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8967⟩, 2))),
  (⟨8951⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨8953⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8954⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8955⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8957⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8960⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8961⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8962⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8963⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4126⟩, 2))),
  (⟨8966⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8967⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8968⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8969⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8767⟩, 2))),
  (⟨8972⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8973⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8974⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8975⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8991⟩, 2))),
  (⟨8978⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨8980⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8981⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8982⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8985⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none))
]

private theorem generatedDecodes64_correct : ∀ i : Fin generatedDecodes64.size,
    decode runtimeBytecode generatedDecodes64[i].1 = generatedDecodes64[i].2 := by
  native_decide

theorem decode_8831 : decode runtimeBytecode ⟨8831⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨0, by decide⟩
theorem decode_8832 : decode runtimeBytecode ⟨8832⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨1, by decide⟩
theorem decode_8833 : decode runtimeBytecode ⟨8833⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨2, by decide⟩
theorem decode_8836 : decode runtimeBytecode ⟨8836⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP11), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨3, by decide⟩
theorem decode_8837 : decode runtimeBytecode ⟨8837⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨4, by decide⟩
theorem decode_8838 : decode runtimeBytecode ⟨8838⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨5, by decide⟩
theorem decode_8840 : decode runtimeBytecode ⟨8840⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨6, by decide⟩
theorem decode_8841 : decode runtimeBytecode ⟨8841⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨7, by decide⟩
theorem decode_8843 : decode runtimeBytecode ⟨8843⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨8, by decide⟩
theorem decode_8844 : decode runtimeBytecode ⟨8844⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨9, by decide⟩
theorem decode_8845 : decode runtimeBytecode ⟨8845⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨10, by decide⟩
theorem decode_8846 : decode runtimeBytecode ⟨8846⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨11, by decide⟩
theorem decode_8849 : decode runtimeBytecode ⟨8849⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP12), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨12, by decide⟩
theorem decode_8850 : decode runtimeBytecode ⟨8850⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨13, by decide⟩
theorem decode_8851 : decode runtimeBytecode ⟨8851⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨14, by decide⟩
theorem decode_8853 : decode runtimeBytecode ⟨8853⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨15, by decide⟩
theorem decode_8854 : decode runtimeBytecode ⟨8854⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨16, by decide⟩
theorem decode_8856 : decode runtimeBytecode ⟨8856⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨17, by decide⟩
theorem decode_8857 : decode runtimeBytecode ⟨8857⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨18, by decide⟩
theorem decode_8858 : decode runtimeBytecode ⟨8858⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨19, by decide⟩
theorem decode_8859 : decode runtimeBytecode ⟨8859⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨20, by decide⟩
theorem decode_8862 : decode runtimeBytecode ⟨8862⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP13), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨21, by decide⟩
theorem decode_8863 : decode runtimeBytecode ⟨8863⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨22, by decide⟩
theorem decode_8864 : decode runtimeBytecode ⟨8864⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨23, by decide⟩
theorem decode_8866 : decode runtimeBytecode ⟨8866⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨24, by decide⟩
theorem decode_8867 : decode runtimeBytecode ⟨8867⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨25, by decide⟩
theorem decode_8869 : decode runtimeBytecode ⟨8869⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨26, by decide⟩
theorem decode_8870 : decode runtimeBytecode ⟨8870⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨27, by decide⟩
theorem decode_8871 : decode runtimeBytecode ⟨8871⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨28, by decide⟩
theorem decode_8872 : decode runtimeBytecode ⟨8872⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨29, by decide⟩
theorem decode_8875 : decode runtimeBytecode ⟨8875⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨30, by decide⟩
theorem decode_8876 : decode runtimeBytecode ⟨8876⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨31, by decide⟩
theorem decode_8877 : decode runtimeBytecode ⟨8877⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨32, by decide⟩
theorem decode_8879 : decode runtimeBytecode ⟨8879⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨33, by decide⟩
theorem decode_8880 : decode runtimeBytecode ⟨8880⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨34, by decide⟩
theorem decode_8882 : decode runtimeBytecode ⟨8882⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨35, by decide⟩
theorem decode_8883 : decode runtimeBytecode ⟨8883⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨36, by decide⟩
theorem decode_8884 : decode runtimeBytecode ⟨8884⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨37, by decide⟩
theorem decode_8885 : decode runtimeBytecode ⟨8885⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨38, by decide⟩
theorem decode_8886 : decode runtimeBytecode ⟨8886⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨39, by decide⟩
theorem decode_8887 : decode runtimeBytecode ⟨8887⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨40, by decide⟩
theorem decode_8892 : decode runtimeBytecode ⟨8892⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨41, by decide⟩
theorem decode_8893 : decode runtimeBytecode ⟨8893⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP13), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨42, by decide⟩
theorem decode_8894 : decode runtimeBytecode ⟨8894⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨43, by decide⟩
theorem decode_8895 : decode runtimeBytecode ⟨8895⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨44, by decide⟩
theorem decode_8896 : decode runtimeBytecode ⟨8896⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨45, by decide⟩
theorem decode_8901 : decode runtimeBytecode ⟨8901⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨46, by decide⟩
theorem decode_8902 : decode runtimeBytecode ⟨8902⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP14), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨47, by decide⟩
theorem decode_8903 : decode runtimeBytecode ⟨8903⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨48, by decide⟩
theorem decode_8904 : decode runtimeBytecode ⟨8904⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨49, by decide⟩
theorem decode_8905 : decode runtimeBytecode ⟨8905⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨50, by decide⟩
theorem decode_8910 : decode runtimeBytecode ⟨8910⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨51, by decide⟩
theorem decode_8911 : decode runtimeBytecode ⟨8911⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP11), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨52, by decide⟩
theorem decode_8912 : decode runtimeBytecode ⟨8912⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨53, by decide⟩
theorem decode_8913 : decode runtimeBytecode ⟨8913⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨54, by decide⟩
theorem decode_8914 : decode runtimeBytecode ⟨8914⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨55, by decide⟩
theorem decode_8919 : decode runtimeBytecode ⟨8919⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨56, by decide⟩
theorem decode_8920 : decode runtimeBytecode ⟨8920⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨57, by decide⟩
theorem decode_8921 : decode runtimeBytecode ⟨8921⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨58, by decide⟩
theorem decode_8922 : decode runtimeBytecode ⟨8922⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨59, by decide⟩
theorem decode_8923 : decode runtimeBytecode ⟨8923⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4294967295⟩, 4)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨60, by decide⟩
theorem decode_8928 : decode runtimeBytecode ⟨8928⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨61, by decide⟩
theorem decode_8929 : decode runtimeBytecode ⟨8929⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP5), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨62, by decide⟩
theorem decode_8930 : decode runtimeBytecode ⟨8930⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨63, by decide⟩
theorem decode_8931 : decode runtimeBytecode ⟨8931⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨64, by decide⟩
theorem decode_8933 : decode runtimeBytecode ⟨8933⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨65, by decide⟩
theorem decode_8935 : decode runtimeBytecode ⟨8935⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨66, by decide⟩
theorem decode_8936 : decode runtimeBytecode ⟨8936⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨67, by decide⟩
theorem decode_8937 : decode runtimeBytecode ⟨8937⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨68, by decide⟩
theorem decode_8938 : decode runtimeBytecode ⟨8938⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨69, by decide⟩
theorem decode_8939 : decode runtimeBytecode ⟨8939⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨70, by decide⟩
theorem decode_8940 : decode runtimeBytecode ⟨8940⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨71, by decide⟩
theorem decode_8941 : decode runtimeBytecode ⟨8941⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨72, by decide⟩
theorem decode_8942 : decode runtimeBytecode ⟨8942⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8533⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨73, by decide⟩
theorem decode_8945 : decode runtimeBytecode ⟨8945⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨74, by decide⟩
theorem decode_8946 : decode runtimeBytecode ⟨8946⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨75, by decide⟩
theorem decode_8947 : decode runtimeBytecode ⟨8947⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨76, by decide⟩
theorem decode_8948 : decode runtimeBytecode ⟨8948⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8967⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨77, by decide⟩
theorem decode_8951 : decode runtimeBytecode ⟨8951⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨78, by decide⟩
theorem decode_8953 : decode runtimeBytecode ⟨8953⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨79, by decide⟩
theorem decode_8954 : decode runtimeBytecode ⟨8954⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨80, by decide⟩
theorem decode_8955 : decode runtimeBytecode ⟨8955⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨81, by decide⟩
theorem decode_8957 : decode runtimeBytecode ⟨8957⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨82, by decide⟩
theorem decode_8960 : decode runtimeBytecode ⟨8960⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨83, by decide⟩
theorem decode_8961 : decode runtimeBytecode ⟨8961⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨84, by decide⟩
theorem decode_8962 : decode runtimeBytecode ⟨8962⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨85, by decide⟩
theorem decode_8963 : decode runtimeBytecode ⟨8963⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4126⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨86, by decide⟩
theorem decode_8966 : decode runtimeBytecode ⟨8966⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨87, by decide⟩
theorem decode_8967 : decode runtimeBytecode ⟨8967⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨88, by decide⟩
theorem decode_8968 : decode runtimeBytecode ⟨8968⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨89, by decide⟩
theorem decode_8969 : decode runtimeBytecode ⟨8969⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8767⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨90, by decide⟩
theorem decode_8972 : decode runtimeBytecode ⟨8972⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨91, by decide⟩
theorem decode_8973 : decode runtimeBytecode ⟨8973⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨92, by decide⟩
theorem decode_8974 : decode runtimeBytecode ⟨8974⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨93, by decide⟩
theorem decode_8975 : decode runtimeBytecode ⟨8975⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8991⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨94, by decide⟩
theorem decode_8978 : decode runtimeBytecode ⟨8978⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨95, by decide⟩
theorem decode_8980 : decode runtimeBytecode ⟨8980⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨96, by decide⟩
theorem decode_8981 : decode runtimeBytecode ⟨8981⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨97, by decide⟩
theorem decode_8982 : decode runtimeBytecode ⟨8982⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨98, by decide⟩
theorem decode_8985 : decode runtimeBytecode ⟨8985⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes64] using generatedDecodes64_correct ⟨99, by decide⟩

end Ripemd160Old
