import Examples.Ripemd160Old.DecodeGenerated.Chunk03

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes4 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨796⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨797⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨798⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨799⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨800⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨801⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨802⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨803⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨805⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨806⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨807⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨808⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨809⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨810⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨813⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨814⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨815⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨816⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨817⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨818⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨819⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨820⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨821⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨822⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨824⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨825⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨826⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨827⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨828⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨829⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨832⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨833⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨834⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨835⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨836⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨837⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨838⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨839⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨840⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨841⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨843⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨844⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨845⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨846⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨847⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨848⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨851⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨852⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨853⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨854⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨855⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨856⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨857⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨858⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨859⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨860⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨862⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨863⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨864⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨865⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨866⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨867⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨870⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨871⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨872⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨873⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨874⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨875⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨876⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨877⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨878⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨879⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨881⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨882⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨883⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨884⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨885⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨886⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨889⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨890⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨891⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨892⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨893⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨894⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨895⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨896⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨897⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨898⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨900⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨901⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨902⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨903⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨904⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨905⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2))),
  (⟨908⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨909⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨910⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨911⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨912⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨913⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none))
]

private theorem generatedDecodes4_correct : ∀ i : Fin generatedDecodes4.size,
    decode runtimeBytecode generatedDecodes4[i].1 = generatedDecodes4[i].2 := by
  native_decide

theorem decode_796 : decode runtimeBytecode ⟨796⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨0, by decide⟩
theorem decode_797 : decode runtimeBytecode ⟨797⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨1, by decide⟩
theorem decode_798 : decode runtimeBytecode ⟨798⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨2, by decide⟩
theorem decode_799 : decode runtimeBytecode ⟨799⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨3, by decide⟩
theorem decode_800 : decode runtimeBytecode ⟨800⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨4, by decide⟩
theorem decode_801 : decode runtimeBytecode ⟨801⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨5, by decide⟩
theorem decode_802 : decode runtimeBytecode ⟨802⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨6, by decide⟩
theorem decode_803 : decode runtimeBytecode ⟨803⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨7, by decide⟩
theorem decode_805 : decode runtimeBytecode ⟨805⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨8, by decide⟩
theorem decode_806 : decode runtimeBytecode ⟨806⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨9, by decide⟩
theorem decode_807 : decode runtimeBytecode ⟨807⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨10, by decide⟩
theorem decode_808 : decode runtimeBytecode ⟨808⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨11, by decide⟩
theorem decode_809 : decode runtimeBytecode ⟨809⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨12, by decide⟩
theorem decode_810 : decode runtimeBytecode ⟨810⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨13, by decide⟩
theorem decode_813 : decode runtimeBytecode ⟨813⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨14, by decide⟩
theorem decode_814 : decode runtimeBytecode ⟨814⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨15, by decide⟩
theorem decode_815 : decode runtimeBytecode ⟨815⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨16, by decide⟩
theorem decode_816 : decode runtimeBytecode ⟨816⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨17, by decide⟩
theorem decode_817 : decode runtimeBytecode ⟨817⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨18, by decide⟩
theorem decode_818 : decode runtimeBytecode ⟨818⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨19, by decide⟩
theorem decode_819 : decode runtimeBytecode ⟨819⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨20, by decide⟩
theorem decode_820 : decode runtimeBytecode ⟨820⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨21, by decide⟩
theorem decode_821 : decode runtimeBytecode ⟨821⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨22, by decide⟩
theorem decode_822 : decode runtimeBytecode ⟨822⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨23, by decide⟩
theorem decode_824 : decode runtimeBytecode ⟨824⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨24, by decide⟩
theorem decode_825 : decode runtimeBytecode ⟨825⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨25, by decide⟩
theorem decode_826 : decode runtimeBytecode ⟨826⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨26, by decide⟩
theorem decode_827 : decode runtimeBytecode ⟨827⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨27, by decide⟩
theorem decode_828 : decode runtimeBytecode ⟨828⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨28, by decide⟩
theorem decode_829 : decode runtimeBytecode ⟨829⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨29, by decide⟩
theorem decode_832 : decode runtimeBytecode ⟨832⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨30, by decide⟩
theorem decode_833 : decode runtimeBytecode ⟨833⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨31, by decide⟩
theorem decode_834 : decode runtimeBytecode ⟨834⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨32, by decide⟩
theorem decode_835 : decode runtimeBytecode ⟨835⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨33, by decide⟩
theorem decode_836 : decode runtimeBytecode ⟨836⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨34, by decide⟩
theorem decode_837 : decode runtimeBytecode ⟨837⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨35, by decide⟩
theorem decode_838 : decode runtimeBytecode ⟨838⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨36, by decide⟩
theorem decode_839 : decode runtimeBytecode ⟨839⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨37, by decide⟩
theorem decode_840 : decode runtimeBytecode ⟨840⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨38, by decide⟩
theorem decode_841 : decode runtimeBytecode ⟨841⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨39, by decide⟩
theorem decode_843 : decode runtimeBytecode ⟨843⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨40, by decide⟩
theorem decode_844 : decode runtimeBytecode ⟨844⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨41, by decide⟩
theorem decode_845 : decode runtimeBytecode ⟨845⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨42, by decide⟩
theorem decode_846 : decode runtimeBytecode ⟨846⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨43, by decide⟩
theorem decode_847 : decode runtimeBytecode ⟨847⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨44, by decide⟩
theorem decode_848 : decode runtimeBytecode ⟨848⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨45, by decide⟩
theorem decode_851 : decode runtimeBytecode ⟨851⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨46, by decide⟩
theorem decode_852 : decode runtimeBytecode ⟨852⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨47, by decide⟩
theorem decode_853 : decode runtimeBytecode ⟨853⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨48, by decide⟩
theorem decode_854 : decode runtimeBytecode ⟨854⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨49, by decide⟩
theorem decode_855 : decode runtimeBytecode ⟨855⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨50, by decide⟩
theorem decode_856 : decode runtimeBytecode ⟨856⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨51, by decide⟩
theorem decode_857 : decode runtimeBytecode ⟨857⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨52, by decide⟩
theorem decode_858 : decode runtimeBytecode ⟨858⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨53, by decide⟩
theorem decode_859 : decode runtimeBytecode ⟨859⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨54, by decide⟩
theorem decode_860 : decode runtimeBytecode ⟨860⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨55, by decide⟩
theorem decode_862 : decode runtimeBytecode ⟨862⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨56, by decide⟩
theorem decode_863 : decode runtimeBytecode ⟨863⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨57, by decide⟩
theorem decode_864 : decode runtimeBytecode ⟨864⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨58, by decide⟩
theorem decode_865 : decode runtimeBytecode ⟨865⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨59, by decide⟩
theorem decode_866 : decode runtimeBytecode ⟨866⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨60, by decide⟩
theorem decode_867 : decode runtimeBytecode ⟨867⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨61, by decide⟩
theorem decode_870 : decode runtimeBytecode ⟨870⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨62, by decide⟩
theorem decode_871 : decode runtimeBytecode ⟨871⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨63, by decide⟩
theorem decode_872 : decode runtimeBytecode ⟨872⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨64, by decide⟩
theorem decode_873 : decode runtimeBytecode ⟨873⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨65, by decide⟩
theorem decode_874 : decode runtimeBytecode ⟨874⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨66, by decide⟩
theorem decode_875 : decode runtimeBytecode ⟨875⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨67, by decide⟩
theorem decode_876 : decode runtimeBytecode ⟨876⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨68, by decide⟩
theorem decode_877 : decode runtimeBytecode ⟨877⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨69, by decide⟩
theorem decode_878 : decode runtimeBytecode ⟨878⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨70, by decide⟩
theorem decode_879 : decode runtimeBytecode ⟨879⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨71, by decide⟩
theorem decode_881 : decode runtimeBytecode ⟨881⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨72, by decide⟩
theorem decode_882 : decode runtimeBytecode ⟨882⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨73, by decide⟩
theorem decode_883 : decode runtimeBytecode ⟨883⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨74, by decide⟩
theorem decode_884 : decode runtimeBytecode ⟨884⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨75, by decide⟩
theorem decode_885 : decode runtimeBytecode ⟨885⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨76, by decide⟩
theorem decode_886 : decode runtimeBytecode ⟨886⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨77, by decide⟩
theorem decode_889 : decode runtimeBytecode ⟨889⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨78, by decide⟩
theorem decode_890 : decode runtimeBytecode ⟨890⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨79, by decide⟩
theorem decode_891 : decode runtimeBytecode ⟨891⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨80, by decide⟩
theorem decode_892 : decode runtimeBytecode ⟨892⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨81, by decide⟩
theorem decode_893 : decode runtimeBytecode ⟨893⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨82, by decide⟩
theorem decode_894 : decode runtimeBytecode ⟨894⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨83, by decide⟩
theorem decode_895 : decode runtimeBytecode ⟨895⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨84, by decide⟩
theorem decode_896 : decode runtimeBytecode ⟨896⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨85, by decide⟩
theorem decode_897 : decode runtimeBytecode ⟨897⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨86, by decide⟩
theorem decode_898 : decode runtimeBytecode ⟨898⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨87, by decide⟩
theorem decode_900 : decode runtimeBytecode ⟨900⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨88, by decide⟩
theorem decode_901 : decode runtimeBytecode ⟨901⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨89, by decide⟩
theorem decode_902 : decode runtimeBytecode ⟨902⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨90, by decide⟩
theorem decode_903 : decode runtimeBytecode ⟨903⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨91, by decide⟩
theorem decode_904 : decode runtimeBytecode ⟨904⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨92, by decide⟩
theorem decode_905 : decode runtimeBytecode ⟨905⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨673⟩, 2)) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨93, by decide⟩
theorem decode_908 : decode runtimeBytecode ⟨908⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨94, by decide⟩
theorem decode_909 : decode runtimeBytecode ⟨909⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨95, by decide⟩
theorem decode_910 : decode runtimeBytecode ⟨910⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨96, by decide⟩
theorem decode_911 : decode runtimeBytecode ⟨911⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨97, by decide⟩
theorem decode_912 : decode runtimeBytecode ⟨912⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨98, by decide⟩
theorem decode_913 : decode runtimeBytecode ⟨913⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes4] using generatedDecodes4_correct ⟨99, by decide⟩

end Ripemd160Old
