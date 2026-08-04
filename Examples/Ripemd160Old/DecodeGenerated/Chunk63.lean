import Examples.Ripemd160Old.DecodeGenerated.Chunk62

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes63 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8689⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8690⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8691⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8692⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8693⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8694⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8695⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨80⟩, 1))),
  (⟨8697⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8698⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8699⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8973⟩, 2))),
  (⟨8702⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8703⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8704⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8705⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8707⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8710⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8711⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8712⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8713⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8714⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8715⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8717⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8719⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8722⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8723⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8724⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8725⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8726⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8727⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8728⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8730⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8732⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8735⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8736⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8737⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8738⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8739⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8740⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none)),
  (⟨8741⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8743⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8745⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8748⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8749⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8750⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8751⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8752⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8753⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8754⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8756⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8758⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8761⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8762⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8763⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8764⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8765⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8766⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8767⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8768⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨80⟩, 1))),
  (⟨8770⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8771⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8772⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8946⟩, 2))),
  (⟨8775⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8776⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8777⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8780⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8781⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8782⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8783⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8784⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8787⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8788⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8789⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨8791⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8792⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8793⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8794⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8797⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8798⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8799⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8801⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8802⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8803⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8804⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8807⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8808⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8809⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨8811⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8812⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8813⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨8814⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8817⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none)),
  (⟨8818⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8819⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1))),
  (⟨8821⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8822⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8823⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8826⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none)),
  (⟨8827⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8828⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8830⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none))
]

private theorem generatedDecodes63_correct : ∀ i : Fin generatedDecodes63.size,
    decode runtimeBytecode generatedDecodes63[i].1 = generatedDecodes63[i].2 := by
  native_decide

theorem decode_8689 : decode runtimeBytecode ⟨8689⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨0, by decide⟩
theorem decode_8690 : decode runtimeBytecode ⟨8690⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨1, by decide⟩
theorem decode_8691 : decode runtimeBytecode ⟨8691⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨2, by decide⟩
theorem decode_8692 : decode runtimeBytecode ⟨8692⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨3, by decide⟩
theorem decode_8693 : decode runtimeBytecode ⟨8693⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨4, by decide⟩
theorem decode_8694 : decode runtimeBytecode ⟨8694⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨5, by decide⟩
theorem decode_8695 : decode runtimeBytecode ⟨8695⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨80⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨6, by decide⟩
theorem decode_8697 : decode runtimeBytecode ⟨8697⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨7, by decide⟩
theorem decode_8698 : decode runtimeBytecode ⟨8698⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨8, by decide⟩
theorem decode_8699 : decode runtimeBytecode ⟨8699⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8973⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨9, by decide⟩
theorem decode_8702 : decode runtimeBytecode ⟨8702⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨10, by decide⟩
theorem decode_8703 : decode runtimeBytecode ⟨8703⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨11, by decide⟩
theorem decode_8704 : decode runtimeBytecode ⟨8704⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨12, by decide⟩
theorem decode_8705 : decode runtimeBytecode ⟨8705⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨13, by decide⟩
theorem decode_8707 : decode runtimeBytecode ⟨8707⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨14, by decide⟩
theorem decode_8710 : decode runtimeBytecode ⟨8710⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨15, by decide⟩
theorem decode_8711 : decode runtimeBytecode ⟨8711⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨16, by decide⟩
theorem decode_8712 : decode runtimeBytecode ⟨8712⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨17, by decide⟩
theorem decode_8713 : decode runtimeBytecode ⟨8713⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨18, by decide⟩
theorem decode_8714 : decode runtimeBytecode ⟨8714⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨19, by decide⟩
theorem decode_8715 : decode runtimeBytecode ⟨8715⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨20, by decide⟩
theorem decode_8717 : decode runtimeBytecode ⟨8717⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨21, by decide⟩
theorem decode_8719 : decode runtimeBytecode ⟨8719⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨22, by decide⟩
theorem decode_8722 : decode runtimeBytecode ⟨8722⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨23, by decide⟩
theorem decode_8723 : decode runtimeBytecode ⟨8723⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨24, by decide⟩
theorem decode_8724 : decode runtimeBytecode ⟨8724⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨25, by decide⟩
theorem decode_8725 : decode runtimeBytecode ⟨8725⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨26, by decide⟩
theorem decode_8726 : decode runtimeBytecode ⟨8726⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨27, by decide⟩
theorem decode_8727 : decode runtimeBytecode ⟨8727⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨28, by decide⟩
theorem decode_8728 : decode runtimeBytecode ⟨8728⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨29, by decide⟩
theorem decode_8730 : decode runtimeBytecode ⟨8730⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨30, by decide⟩
theorem decode_8732 : decode runtimeBytecode ⟨8732⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨31, by decide⟩
theorem decode_8735 : decode runtimeBytecode ⟨8735⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨32, by decide⟩
theorem decode_8736 : decode runtimeBytecode ⟨8736⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨33, by decide⟩
theorem decode_8737 : decode runtimeBytecode ⟨8737⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨34, by decide⟩
theorem decode_8738 : decode runtimeBytecode ⟨8738⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨35, by decide⟩
theorem decode_8739 : decode runtimeBytecode ⟨8739⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨36, by decide⟩
theorem decode_8740 : decode runtimeBytecode ⟨8740⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨37, by decide⟩
theorem decode_8741 : decode runtimeBytecode ⟨8741⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨38, by decide⟩
theorem decode_8743 : decode runtimeBytecode ⟨8743⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨39, by decide⟩
theorem decode_8745 : decode runtimeBytecode ⟨8745⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨40, by decide⟩
theorem decode_8748 : decode runtimeBytecode ⟨8748⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨41, by decide⟩
theorem decode_8749 : decode runtimeBytecode ⟨8749⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨42, by decide⟩
theorem decode_8750 : decode runtimeBytecode ⟨8750⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨43, by decide⟩
theorem decode_8751 : decode runtimeBytecode ⟨8751⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨44, by decide⟩
theorem decode_8752 : decode runtimeBytecode ⟨8752⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨45, by decide⟩
theorem decode_8753 : decode runtimeBytecode ⟨8753⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨46, by decide⟩
theorem decode_8754 : decode runtimeBytecode ⟨8754⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨47, by decide⟩
theorem decode_8756 : decode runtimeBytecode ⟨8756⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨48, by decide⟩
theorem decode_8758 : decode runtimeBytecode ⟨8758⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨49, by decide⟩
theorem decode_8761 : decode runtimeBytecode ⟨8761⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨50, by decide⟩
theorem decode_8762 : decode runtimeBytecode ⟨8762⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨51, by decide⟩
theorem decode_8763 : decode runtimeBytecode ⟨8763⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨52, by decide⟩
theorem decode_8764 : decode runtimeBytecode ⟨8764⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨53, by decide⟩
theorem decode_8765 : decode runtimeBytecode ⟨8765⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨54, by decide⟩
theorem decode_8766 : decode runtimeBytecode ⟨8766⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨55, by decide⟩
theorem decode_8767 : decode runtimeBytecode ⟨8767⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨56, by decide⟩
theorem decode_8768 : decode runtimeBytecode ⟨8768⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨80⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨57, by decide⟩
theorem decode_8770 : decode runtimeBytecode ⟨8770⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨58, by decide⟩
theorem decode_8771 : decode runtimeBytecode ⟨8771⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨59, by decide⟩
theorem decode_8772 : decode runtimeBytecode ⟨8772⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8946⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨60, by decide⟩
theorem decode_8775 : decode runtimeBytecode ⟨8775⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨61, by decide⟩
theorem decode_8776 : decode runtimeBytecode ⟨8776⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨62, by decide⟩
theorem decode_8777 : decode runtimeBytecode ⟨8777⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨63, by decide⟩
theorem decode_8780 : decode runtimeBytecode ⟨8780⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨64, by decide⟩
theorem decode_8781 : decode runtimeBytecode ⟨8781⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨65, by decide⟩
theorem decode_8782 : decode runtimeBytecode ⟨8782⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨66, by decide⟩
theorem decode_8783 : decode runtimeBytecode ⟨8783⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨67, by decide⟩
theorem decode_8784 : decode runtimeBytecode ⟨8784⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨68, by decide⟩
theorem decode_8787 : decode runtimeBytecode ⟨8787⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨69, by decide⟩
theorem decode_8788 : decode runtimeBytecode ⟨8788⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨70, by decide⟩
theorem decode_8789 : decode runtimeBytecode ⟨8789⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨71, by decide⟩
theorem decode_8791 : decode runtimeBytecode ⟨8791⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨72, by decide⟩
theorem decode_8792 : decode runtimeBytecode ⟨8792⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨73, by decide⟩
theorem decode_8793 : decode runtimeBytecode ⟨8793⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨74, by decide⟩
theorem decode_8794 : decode runtimeBytecode ⟨8794⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨75, by decide⟩
theorem decode_8797 : decode runtimeBytecode ⟨8797⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨76, by decide⟩
theorem decode_8798 : decode runtimeBytecode ⟨8798⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨77, by decide⟩
theorem decode_8799 : decode runtimeBytecode ⟨8799⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨78, by decide⟩
theorem decode_8801 : decode runtimeBytecode ⟨8801⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨79, by decide⟩
theorem decode_8802 : decode runtimeBytecode ⟨8802⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨80, by decide⟩
theorem decode_8803 : decode runtimeBytecode ⟨8803⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨81, by decide⟩
theorem decode_8804 : decode runtimeBytecode ⟨8804⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨82, by decide⟩
theorem decode_8807 : decode runtimeBytecode ⟨8807⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨83, by decide⟩
theorem decode_8808 : decode runtimeBytecode ⟨8808⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨84, by decide⟩
theorem decode_8809 : decode runtimeBytecode ⟨8809⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨85, by decide⟩
theorem decode_8811 : decode runtimeBytecode ⟨8811⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨86, by decide⟩
theorem decode_8812 : decode runtimeBytecode ⟨8812⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨87, by decide⟩
theorem decode_8813 : decode runtimeBytecode ⟨8813⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨88, by decide⟩
theorem decode_8814 : decode runtimeBytecode ⟨8814⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨89, by decide⟩
theorem decode_8817 : decode runtimeBytecode ⟨8817⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨90, by decide⟩
theorem decode_8818 : decode runtimeBytecode ⟨8818⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨91, by decide⟩
theorem decode_8819 : decode runtimeBytecode ⟨8819⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨128⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨92, by decide⟩
theorem decode_8821 : decode runtimeBytecode ⟨8821⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨93, by decide⟩
theorem decode_8822 : decode runtimeBytecode ⟨8822⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨94, by decide⟩
theorem decode_8823 : decode runtimeBytecode ⟨8823⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨95, by decide⟩
theorem decode_8826 : decode runtimeBytecode ⟨8826⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP10), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨96, by decide⟩
theorem decode_8827 : decode runtimeBytecode ⟨8827⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨97, by decide⟩
theorem decode_8828 : decode runtimeBytecode ⟨8828⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨98, by decide⟩
theorem decode_8830 : decode runtimeBytecode ⟨8830⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes63] using generatedDecodes63_correct ⟨99, by decide⟩

end Ripemd160Old
