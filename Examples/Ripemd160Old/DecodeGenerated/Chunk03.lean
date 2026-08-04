import Examples.Ripemd160Old.DecodeGenerated.Chunk02

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes3 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨676⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨677⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨678⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2))),
  (⟨681⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨682⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨683⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨684⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨685⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨686⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨687⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨688⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨689⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨691⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨692⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨693⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨694⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨695⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨696⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨699⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨700⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨701⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨702⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨703⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨704⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨705⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨706⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨707⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨708⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨710⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨711⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨712⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨713⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨714⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨715⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨718⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨719⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨720⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨721⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨722⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨723⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨724⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨725⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨726⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨727⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨729⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨730⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨731⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨732⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨733⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨734⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨737⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨738⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨739⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨740⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨741⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨742⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨743⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨744⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨745⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨746⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨748⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨749⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨750⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨751⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨752⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨753⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨756⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨757⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨758⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨759⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨760⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨761⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨762⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨763⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨764⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨765⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨767⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨768⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨769⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨770⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨771⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨772⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨775⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨776⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨777⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨778⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨779⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨780⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨781⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨782⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨783⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨784⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨786⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨787⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨788⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨789⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨790⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨791⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨794⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨795⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none))
]

private theorem generatedDecodes3_correct : ∀ i : Fin generatedDecodes3.size,
    decode runtimeBytecode generatedDecodes3[i].1 = generatedDecodes3[i].2 := by
  native_decide

theorem decode_676 : decode runtimeBytecode ⟨676⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨0, by decide⟩
theorem decode_677 : decode runtimeBytecode ⟨677⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨1, by decide⟩
theorem decode_678 : decode runtimeBytecode ⟨678⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨2, by decide⟩
theorem decode_681 : decode runtimeBytecode ⟨681⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨3, by decide⟩
theorem decode_682 : decode runtimeBytecode ⟨682⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨4, by decide⟩
theorem decode_683 : decode runtimeBytecode ⟨683⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨5, by decide⟩
theorem decode_684 : decode runtimeBytecode ⟨684⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨6, by decide⟩
theorem decode_685 : decode runtimeBytecode ⟨685⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨7, by decide⟩
theorem decode_686 : decode runtimeBytecode ⟨686⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨8, by decide⟩
theorem decode_687 : decode runtimeBytecode ⟨687⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨9, by decide⟩
theorem decode_688 : decode runtimeBytecode ⟨688⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨10, by decide⟩
theorem decode_689 : decode runtimeBytecode ⟨689⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨11, by decide⟩
theorem decode_691 : decode runtimeBytecode ⟨691⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨12, by decide⟩
theorem decode_692 : decode runtimeBytecode ⟨692⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨13, by decide⟩
theorem decode_693 : decode runtimeBytecode ⟨693⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨14, by decide⟩
theorem decode_694 : decode runtimeBytecode ⟨694⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨15, by decide⟩
theorem decode_695 : decode runtimeBytecode ⟨695⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨16, by decide⟩
theorem decode_696 : decode runtimeBytecode ⟨696⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨17, by decide⟩
theorem decode_699 : decode runtimeBytecode ⟨699⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨18, by decide⟩
theorem decode_700 : decode runtimeBytecode ⟨700⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨19, by decide⟩
theorem decode_701 : decode runtimeBytecode ⟨701⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨20, by decide⟩
theorem decode_702 : decode runtimeBytecode ⟨702⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨21, by decide⟩
theorem decode_703 : decode runtimeBytecode ⟨703⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨22, by decide⟩
theorem decode_704 : decode runtimeBytecode ⟨704⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨23, by decide⟩
theorem decode_705 : decode runtimeBytecode ⟨705⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨24, by decide⟩
theorem decode_706 : decode runtimeBytecode ⟨706⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨25, by decide⟩
theorem decode_707 : decode runtimeBytecode ⟨707⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨26, by decide⟩
theorem decode_708 : decode runtimeBytecode ⟨708⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨27, by decide⟩
theorem decode_710 : decode runtimeBytecode ⟨710⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨28, by decide⟩
theorem decode_711 : decode runtimeBytecode ⟨711⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨29, by decide⟩
theorem decode_712 : decode runtimeBytecode ⟨712⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨30, by decide⟩
theorem decode_713 : decode runtimeBytecode ⟨713⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨31, by decide⟩
theorem decode_714 : decode runtimeBytecode ⟨714⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨32, by decide⟩
theorem decode_715 : decode runtimeBytecode ⟨715⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨33, by decide⟩
theorem decode_718 : decode runtimeBytecode ⟨718⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨34, by decide⟩
theorem decode_719 : decode runtimeBytecode ⟨719⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨35, by decide⟩
theorem decode_720 : decode runtimeBytecode ⟨720⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨36, by decide⟩
theorem decode_721 : decode runtimeBytecode ⟨721⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨37, by decide⟩
theorem decode_722 : decode runtimeBytecode ⟨722⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨38, by decide⟩
theorem decode_723 : decode runtimeBytecode ⟨723⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨39, by decide⟩
theorem decode_724 : decode runtimeBytecode ⟨724⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨40, by decide⟩
theorem decode_725 : decode runtimeBytecode ⟨725⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨41, by decide⟩
theorem decode_726 : decode runtimeBytecode ⟨726⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨42, by decide⟩
theorem decode_727 : decode runtimeBytecode ⟨727⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨43, by decide⟩
theorem decode_729 : decode runtimeBytecode ⟨729⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨44, by decide⟩
theorem decode_730 : decode runtimeBytecode ⟨730⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨45, by decide⟩
theorem decode_731 : decode runtimeBytecode ⟨731⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨46, by decide⟩
theorem decode_732 : decode runtimeBytecode ⟨732⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨47, by decide⟩
theorem decode_733 : decode runtimeBytecode ⟨733⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨48, by decide⟩
theorem decode_734 : decode runtimeBytecode ⟨734⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨49, by decide⟩
theorem decode_737 : decode runtimeBytecode ⟨737⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨50, by decide⟩
theorem decode_738 : decode runtimeBytecode ⟨738⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨51, by decide⟩
theorem decode_739 : decode runtimeBytecode ⟨739⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨52, by decide⟩
theorem decode_740 : decode runtimeBytecode ⟨740⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨53, by decide⟩
theorem decode_741 : decode runtimeBytecode ⟨741⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨54, by decide⟩
theorem decode_742 : decode runtimeBytecode ⟨742⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨55, by decide⟩
theorem decode_743 : decode runtimeBytecode ⟨743⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨56, by decide⟩
theorem decode_744 : decode runtimeBytecode ⟨744⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨57, by decide⟩
theorem decode_745 : decode runtimeBytecode ⟨745⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨58, by decide⟩
theorem decode_746 : decode runtimeBytecode ⟨746⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨59, by decide⟩
theorem decode_748 : decode runtimeBytecode ⟨748⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨60, by decide⟩
theorem decode_749 : decode runtimeBytecode ⟨749⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨61, by decide⟩
theorem decode_750 : decode runtimeBytecode ⟨750⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨62, by decide⟩
theorem decode_751 : decode runtimeBytecode ⟨751⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨63, by decide⟩
theorem decode_752 : decode runtimeBytecode ⟨752⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨64, by decide⟩
theorem decode_753 : decode runtimeBytecode ⟨753⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨65, by decide⟩
theorem decode_756 : decode runtimeBytecode ⟨756⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨66, by decide⟩
theorem decode_757 : decode runtimeBytecode ⟨757⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨67, by decide⟩
theorem decode_758 : decode runtimeBytecode ⟨758⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨68, by decide⟩
theorem decode_759 : decode runtimeBytecode ⟨759⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨69, by decide⟩
theorem decode_760 : decode runtimeBytecode ⟨760⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨70, by decide⟩
theorem decode_761 : decode runtimeBytecode ⟨761⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨71, by decide⟩
theorem decode_762 : decode runtimeBytecode ⟨762⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨72, by decide⟩
theorem decode_763 : decode runtimeBytecode ⟨763⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨73, by decide⟩
theorem decode_764 : decode runtimeBytecode ⟨764⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨74, by decide⟩
theorem decode_765 : decode runtimeBytecode ⟨765⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨75, by decide⟩
theorem decode_767 : decode runtimeBytecode ⟨767⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨76, by decide⟩
theorem decode_768 : decode runtimeBytecode ⟨768⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨77, by decide⟩
theorem decode_769 : decode runtimeBytecode ⟨769⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨78, by decide⟩
theorem decode_770 : decode runtimeBytecode ⟨770⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨79, by decide⟩
theorem decode_771 : decode runtimeBytecode ⟨771⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨80, by decide⟩
theorem decode_772 : decode runtimeBytecode ⟨772⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨81, by decide⟩
theorem decode_775 : decode runtimeBytecode ⟨775⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨82, by decide⟩
theorem decode_776 : decode runtimeBytecode ⟨776⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨83, by decide⟩
theorem decode_777 : decode runtimeBytecode ⟨777⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨84, by decide⟩
theorem decode_778 : decode runtimeBytecode ⟨778⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨85, by decide⟩
theorem decode_779 : decode runtimeBytecode ⟨779⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨86, by decide⟩
theorem decode_780 : decode runtimeBytecode ⟨780⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨87, by decide⟩
theorem decode_781 : decode runtimeBytecode ⟨781⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨88, by decide⟩
theorem decode_782 : decode runtimeBytecode ⟨782⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨89, by decide⟩
theorem decode_783 : decode runtimeBytecode ⟨783⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨90, by decide⟩
theorem decode_784 : decode runtimeBytecode ⟨784⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨91, by decide⟩
theorem decode_786 : decode runtimeBytecode ⟨786⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨92, by decide⟩
theorem decode_787 : decode runtimeBytecode ⟨787⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨93, by decide⟩
theorem decode_788 : decode runtimeBytecode ⟨788⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨94, by decide⟩
theorem decode_789 : decode runtimeBytecode ⟨789⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨95, by decide⟩
theorem decode_790 : decode runtimeBytecode ⟨790⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨96, by decide⟩
theorem decode_791 : decode runtimeBytecode ⟨791⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨97, by decide⟩
theorem decode_794 : decode runtimeBytecode ⟨794⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨98, by decide⟩
theorem decode_795 : decode runtimeBytecode ⟨795⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes3] using generatedDecodes3_correct ⟨99, by decide⟩

end Ripemd160Old
