import Examples.Ripemd160Old.DecodeGenerated.Chunk33

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes34 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨4778⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4779⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4782⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4783⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4784⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4785⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨4786⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4787⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨4788⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨4789⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨4790⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4791⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨4793⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨4794⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4795⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4796⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4797⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4798⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2))),
  (⟨4801⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨4802⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨4803⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4804⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨4806⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨4807⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨4808⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨4809⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨4810⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨4811⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4812⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨4813⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4814⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5229⟩, 2))),
  (⟨4817⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4818⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4819⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨4821⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4822⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5210⟩, 2))),
  (⟨4825⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4826⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4827⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨4829⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4830⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5191⟩, 2))),
  (⟨4833⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4834⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4835⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨4837⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4838⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5172⟩, 2))),
  (⟨4841⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4842⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4843⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨4845⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4846⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5153⟩, 2))),
  (⟨4849⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4850⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4851⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨4853⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4854⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5134⟩, 2))),
  (⟨4857⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4858⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4859⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨4861⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4862⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5115⟩, 2))),
  (⟨4865⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4866⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4867⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨4869⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4870⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5096⟩, 2))),
  (⟨4873⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4874⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4875⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨4877⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4878⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5077⟩, 2))),
  (⟨4881⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4882⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4883⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨4885⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4886⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5058⟩, 2))),
  (⟨4889⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4890⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4891⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨4892⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4893⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5039⟩, 2))),
  (⟨4896⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4897⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4898⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨4900⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4901⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5020⟩, 2))),
  (⟨4904⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4905⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4906⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨4908⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4909⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5001⟩, 2))),
  (⟨4912⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4913⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4914⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨4916⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨4917⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4982⟩, 2))),
  (⟨4920⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨4921⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨4922⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨4924⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes34_correct : ∀ i : Fin generatedDecodes34.size,
    decode runtimeBytecode generatedDecodes34[i].1 = generatedDecodes34[i].2 := by
  native_decide

theorem decode_4778 : decode runtimeBytecode ⟨4778⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨0, by decide⟩
theorem decode_4779 : decode runtimeBytecode ⟨4779⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨1, by decide⟩
theorem decode_4782 : decode runtimeBytecode ⟨4782⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨2, by decide⟩
theorem decode_4783 : decode runtimeBytecode ⟨4783⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨3, by decide⟩
theorem decode_4784 : decode runtimeBytecode ⟨4784⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨4, by decide⟩
theorem decode_4785 : decode runtimeBytecode ⟨4785⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨5, by decide⟩
theorem decode_4786 : decode runtimeBytecode ⟨4786⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨6, by decide⟩
theorem decode_4787 : decode runtimeBytecode ⟨4787⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨7, by decide⟩
theorem decode_4788 : decode runtimeBytecode ⟨4788⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨8, by decide⟩
theorem decode_4789 : decode runtimeBytecode ⟨4789⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨9, by decide⟩
theorem decode_4790 : decode runtimeBytecode ⟨4790⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨10, by decide⟩
theorem decode_4791 : decode runtimeBytecode ⟨4791⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨11, by decide⟩
theorem decode_4793 : decode runtimeBytecode ⟨4793⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨12, by decide⟩
theorem decode_4794 : decode runtimeBytecode ⟨4794⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨13, by decide⟩
theorem decode_4795 : decode runtimeBytecode ⟨4795⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨14, by decide⟩
theorem decode_4796 : decode runtimeBytecode ⟨4796⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨15, by decide⟩
theorem decode_4797 : decode runtimeBytecode ⟨4797⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨16, by decide⟩
theorem decode_4798 : decode runtimeBytecode ⟨4798⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4490⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨17, by decide⟩
theorem decode_4801 : decode runtimeBytecode ⟨4801⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨18, by decide⟩
theorem decode_4802 : decode runtimeBytecode ⟨4802⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨19, by decide⟩
theorem decode_4803 : decode runtimeBytecode ⟨4803⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨20, by decide⟩
theorem decode_4804 : decode runtimeBytecode ⟨4804⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨21, by decide⟩
theorem decode_4806 : decode runtimeBytecode ⟨4806⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨22, by decide⟩
theorem decode_4807 : decode runtimeBytecode ⟨4807⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨23, by decide⟩
theorem decode_4808 : decode runtimeBytecode ⟨4808⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨24, by decide⟩
theorem decode_4809 : decode runtimeBytecode ⟨4809⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨25, by decide⟩
theorem decode_4810 : decode runtimeBytecode ⟨4810⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨26, by decide⟩
theorem decode_4811 : decode runtimeBytecode ⟨4811⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨27, by decide⟩
theorem decode_4812 : decode runtimeBytecode ⟨4812⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨28, by decide⟩
theorem decode_4813 : decode runtimeBytecode ⟨4813⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨29, by decide⟩
theorem decode_4814 : decode runtimeBytecode ⟨4814⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5229⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨30, by decide⟩
theorem decode_4817 : decode runtimeBytecode ⟨4817⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨31, by decide⟩
theorem decode_4818 : decode runtimeBytecode ⟨4818⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨32, by decide⟩
theorem decode_4819 : decode runtimeBytecode ⟨4819⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨33, by decide⟩
theorem decode_4821 : decode runtimeBytecode ⟨4821⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨34, by decide⟩
theorem decode_4822 : decode runtimeBytecode ⟨4822⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5210⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨35, by decide⟩
theorem decode_4825 : decode runtimeBytecode ⟨4825⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨36, by decide⟩
theorem decode_4826 : decode runtimeBytecode ⟨4826⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨37, by decide⟩
theorem decode_4827 : decode runtimeBytecode ⟨4827⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨38, by decide⟩
theorem decode_4829 : decode runtimeBytecode ⟨4829⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨39, by decide⟩
theorem decode_4830 : decode runtimeBytecode ⟨4830⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5191⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨40, by decide⟩
theorem decode_4833 : decode runtimeBytecode ⟨4833⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨41, by decide⟩
theorem decode_4834 : decode runtimeBytecode ⟨4834⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨42, by decide⟩
theorem decode_4835 : decode runtimeBytecode ⟨4835⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨43, by decide⟩
theorem decode_4837 : decode runtimeBytecode ⟨4837⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨44, by decide⟩
theorem decode_4838 : decode runtimeBytecode ⟨4838⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5172⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨45, by decide⟩
theorem decode_4841 : decode runtimeBytecode ⟨4841⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨46, by decide⟩
theorem decode_4842 : decode runtimeBytecode ⟨4842⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨47, by decide⟩
theorem decode_4843 : decode runtimeBytecode ⟨4843⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨48, by decide⟩
theorem decode_4845 : decode runtimeBytecode ⟨4845⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨49, by decide⟩
theorem decode_4846 : decode runtimeBytecode ⟨4846⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5153⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨50, by decide⟩
theorem decode_4849 : decode runtimeBytecode ⟨4849⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨51, by decide⟩
theorem decode_4850 : decode runtimeBytecode ⟨4850⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨52, by decide⟩
theorem decode_4851 : decode runtimeBytecode ⟨4851⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨53, by decide⟩
theorem decode_4853 : decode runtimeBytecode ⟨4853⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨54, by decide⟩
theorem decode_4854 : decode runtimeBytecode ⟨4854⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5134⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨55, by decide⟩
theorem decode_4857 : decode runtimeBytecode ⟨4857⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨56, by decide⟩
theorem decode_4858 : decode runtimeBytecode ⟨4858⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨57, by decide⟩
theorem decode_4859 : decode runtimeBytecode ⟨4859⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨58, by decide⟩
theorem decode_4861 : decode runtimeBytecode ⟨4861⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨59, by decide⟩
theorem decode_4862 : decode runtimeBytecode ⟨4862⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5115⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨60, by decide⟩
theorem decode_4865 : decode runtimeBytecode ⟨4865⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨61, by decide⟩
theorem decode_4866 : decode runtimeBytecode ⟨4866⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨62, by decide⟩
theorem decode_4867 : decode runtimeBytecode ⟨4867⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨63, by decide⟩
theorem decode_4869 : decode runtimeBytecode ⟨4869⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨64, by decide⟩
theorem decode_4870 : decode runtimeBytecode ⟨4870⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5096⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨65, by decide⟩
theorem decode_4873 : decode runtimeBytecode ⟨4873⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨66, by decide⟩
theorem decode_4874 : decode runtimeBytecode ⟨4874⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨67, by decide⟩
theorem decode_4875 : decode runtimeBytecode ⟨4875⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨68, by decide⟩
theorem decode_4877 : decode runtimeBytecode ⟨4877⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨69, by decide⟩
theorem decode_4878 : decode runtimeBytecode ⟨4878⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5077⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨70, by decide⟩
theorem decode_4881 : decode runtimeBytecode ⟨4881⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨71, by decide⟩
theorem decode_4882 : decode runtimeBytecode ⟨4882⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨72, by decide⟩
theorem decode_4883 : decode runtimeBytecode ⟨4883⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨73, by decide⟩
theorem decode_4885 : decode runtimeBytecode ⟨4885⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨74, by decide⟩
theorem decode_4886 : decode runtimeBytecode ⟨4886⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5058⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨75, by decide⟩
theorem decode_4889 : decode runtimeBytecode ⟨4889⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨76, by decide⟩
theorem decode_4890 : decode runtimeBytecode ⟨4890⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨77, by decide⟩
theorem decode_4891 : decode runtimeBytecode ⟨4891⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨78, by decide⟩
theorem decode_4892 : decode runtimeBytecode ⟨4892⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨79, by decide⟩
theorem decode_4893 : decode runtimeBytecode ⟨4893⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5039⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨80, by decide⟩
theorem decode_4896 : decode runtimeBytecode ⟨4896⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨81, by decide⟩
theorem decode_4897 : decode runtimeBytecode ⟨4897⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨82, by decide⟩
theorem decode_4898 : decode runtimeBytecode ⟨4898⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨83, by decide⟩
theorem decode_4900 : decode runtimeBytecode ⟨4900⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨84, by decide⟩
theorem decode_4901 : decode runtimeBytecode ⟨4901⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5020⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨85, by decide⟩
theorem decode_4904 : decode runtimeBytecode ⟨4904⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨86, by decide⟩
theorem decode_4905 : decode runtimeBytecode ⟨4905⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨87, by decide⟩
theorem decode_4906 : decode runtimeBytecode ⟨4906⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨88, by decide⟩
theorem decode_4908 : decode runtimeBytecode ⟨4908⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨89, by decide⟩
theorem decode_4909 : decode runtimeBytecode ⟨4909⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨5001⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨90, by decide⟩
theorem decode_4912 : decode runtimeBytecode ⟨4912⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨91, by decide⟩
theorem decode_4913 : decode runtimeBytecode ⟨4913⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨92, by decide⟩
theorem decode_4914 : decode runtimeBytecode ⟨4914⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨93, by decide⟩
theorem decode_4916 : decode runtimeBytecode ⟨4916⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨94, by decide⟩
theorem decode_4917 : decode runtimeBytecode ⟨4917⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4982⟩, 2)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨95, by decide⟩
theorem decode_4920 : decode runtimeBytecode ⟨4920⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨96, by decide⟩
theorem decode_4921 : decode runtimeBytecode ⟨4921⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨97, by decide⟩
theorem decode_4922 : decode runtimeBytecode ⟨4922⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨98, by decide⟩
theorem decode_4924 : decode runtimeBytecode ⟨4924⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes34] using generatedDecodes34_correct ⟨99, by decide⟩

end Ripemd160Old
