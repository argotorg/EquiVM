import Examples.Ripemd160Old.DecodeGenerated.Chunk55

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes56 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7726⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7727⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7728⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7730⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7731⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7734⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7735⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7736⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7737⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7738⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7739⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨7740⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7741⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7744⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7745⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7746⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7747⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7748⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7749⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨7751⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7752⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7755⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7756⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7757⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7758⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7759⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7760⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7762⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7763⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7766⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7767⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7768⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7769⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7770⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7771⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7772⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7773⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7776⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7777⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7778⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7779⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7780⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7781⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨7783⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7784⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7787⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7788⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7789⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7790⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7791⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7792⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7794⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7795⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7798⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7799⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7800⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7801⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7802⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7803⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7805⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7806⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7809⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7810⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7811⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7812⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7813⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7814⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨7816⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7817⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2))),
  (⟨7820⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7821⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7822⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7823⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨7825⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨7826⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨7827⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7828⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7829⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7830⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8119⟩, 2))),
  (⟨7833⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7834⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7835⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨7837⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7838⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8108⟩, 2))),
  (⟨7841⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7842⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7843⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7845⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7846⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8097⟩, 2))),
  (⟨7849⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7850⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7851⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨7853⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7854⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8087⟩, 2))),
  (⟨7857⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7858⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7859⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7861⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7862⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8076⟩, 2))),
  (⟨7865⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none))
]

private theorem generatedDecodes56_correct : ∀ i : Fin generatedDecodes56.size,
    decode runtimeBytecode generatedDecodes56[i].1 = generatedDecodes56[i].2 := by
  native_decide

theorem decode_7726 : decode runtimeBytecode ⟨7726⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨0, by decide⟩
theorem decode_7727 : decode runtimeBytecode ⟨7727⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨1, by decide⟩
theorem decode_7728 : decode runtimeBytecode ⟨7728⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨2, by decide⟩
theorem decode_7730 : decode runtimeBytecode ⟨7730⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨3, by decide⟩
theorem decode_7731 : decode runtimeBytecode ⟨7731⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨4, by decide⟩
theorem decode_7734 : decode runtimeBytecode ⟨7734⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨5, by decide⟩
theorem decode_7735 : decode runtimeBytecode ⟨7735⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨6, by decide⟩
theorem decode_7736 : decode runtimeBytecode ⟨7736⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨7, by decide⟩
theorem decode_7737 : decode runtimeBytecode ⟨7737⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨8, by decide⟩
theorem decode_7738 : decode runtimeBytecode ⟨7738⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨9, by decide⟩
theorem decode_7739 : decode runtimeBytecode ⟨7739⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨10, by decide⟩
theorem decode_7740 : decode runtimeBytecode ⟨7740⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨11, by decide⟩
theorem decode_7741 : decode runtimeBytecode ⟨7741⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨12, by decide⟩
theorem decode_7744 : decode runtimeBytecode ⟨7744⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨13, by decide⟩
theorem decode_7745 : decode runtimeBytecode ⟨7745⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨14, by decide⟩
theorem decode_7746 : decode runtimeBytecode ⟨7746⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨15, by decide⟩
theorem decode_7747 : decode runtimeBytecode ⟨7747⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨16, by decide⟩
theorem decode_7748 : decode runtimeBytecode ⟨7748⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨17, by decide⟩
theorem decode_7749 : decode runtimeBytecode ⟨7749⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨18, by decide⟩
theorem decode_7751 : decode runtimeBytecode ⟨7751⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨19, by decide⟩
theorem decode_7752 : decode runtimeBytecode ⟨7752⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨20, by decide⟩
theorem decode_7755 : decode runtimeBytecode ⟨7755⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨21, by decide⟩
theorem decode_7756 : decode runtimeBytecode ⟨7756⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨22, by decide⟩
theorem decode_7757 : decode runtimeBytecode ⟨7757⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨23, by decide⟩
theorem decode_7758 : decode runtimeBytecode ⟨7758⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨24, by decide⟩
theorem decode_7759 : decode runtimeBytecode ⟨7759⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨25, by decide⟩
theorem decode_7760 : decode runtimeBytecode ⟨7760⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨26, by decide⟩
theorem decode_7762 : decode runtimeBytecode ⟨7762⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨27, by decide⟩
theorem decode_7763 : decode runtimeBytecode ⟨7763⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨28, by decide⟩
theorem decode_7766 : decode runtimeBytecode ⟨7766⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨29, by decide⟩
theorem decode_7767 : decode runtimeBytecode ⟨7767⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨30, by decide⟩
theorem decode_7768 : decode runtimeBytecode ⟨7768⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨31, by decide⟩
theorem decode_7769 : decode runtimeBytecode ⟨7769⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨32, by decide⟩
theorem decode_7770 : decode runtimeBytecode ⟨7770⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨33, by decide⟩
theorem decode_7771 : decode runtimeBytecode ⟨7771⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨34, by decide⟩
theorem decode_7772 : decode runtimeBytecode ⟨7772⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨35, by decide⟩
theorem decode_7773 : decode runtimeBytecode ⟨7773⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨36, by decide⟩
theorem decode_7776 : decode runtimeBytecode ⟨7776⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨37, by decide⟩
theorem decode_7777 : decode runtimeBytecode ⟨7777⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨38, by decide⟩
theorem decode_7778 : decode runtimeBytecode ⟨7778⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨39, by decide⟩
theorem decode_7779 : decode runtimeBytecode ⟨7779⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨40, by decide⟩
theorem decode_7780 : decode runtimeBytecode ⟨7780⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨41, by decide⟩
theorem decode_7781 : decode runtimeBytecode ⟨7781⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨42, by decide⟩
theorem decode_7783 : decode runtimeBytecode ⟨7783⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨43, by decide⟩
theorem decode_7784 : decode runtimeBytecode ⟨7784⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨44, by decide⟩
theorem decode_7787 : decode runtimeBytecode ⟨7787⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨45, by decide⟩
theorem decode_7788 : decode runtimeBytecode ⟨7788⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨46, by decide⟩
theorem decode_7789 : decode runtimeBytecode ⟨7789⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨47, by decide⟩
theorem decode_7790 : decode runtimeBytecode ⟨7790⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨48, by decide⟩
theorem decode_7791 : decode runtimeBytecode ⟨7791⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨49, by decide⟩
theorem decode_7792 : decode runtimeBytecode ⟨7792⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨50, by decide⟩
theorem decode_7794 : decode runtimeBytecode ⟨7794⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨51, by decide⟩
theorem decode_7795 : decode runtimeBytecode ⟨7795⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨52, by decide⟩
theorem decode_7798 : decode runtimeBytecode ⟨7798⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨53, by decide⟩
theorem decode_7799 : decode runtimeBytecode ⟨7799⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨54, by decide⟩
theorem decode_7800 : decode runtimeBytecode ⟨7800⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨55, by decide⟩
theorem decode_7801 : decode runtimeBytecode ⟨7801⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨56, by decide⟩
theorem decode_7802 : decode runtimeBytecode ⟨7802⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨57, by decide⟩
theorem decode_7803 : decode runtimeBytecode ⟨7803⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨58, by decide⟩
theorem decode_7805 : decode runtimeBytecode ⟨7805⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨59, by decide⟩
theorem decode_7806 : decode runtimeBytecode ⟨7806⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨60, by decide⟩
theorem decode_7809 : decode runtimeBytecode ⟨7809⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨61, by decide⟩
theorem decode_7810 : decode runtimeBytecode ⟨7810⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨62, by decide⟩
theorem decode_7811 : decode runtimeBytecode ⟨7811⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨63, by decide⟩
theorem decode_7812 : decode runtimeBytecode ⟨7812⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨64, by decide⟩
theorem decode_7813 : decode runtimeBytecode ⟨7813⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨65, by decide⟩
theorem decode_7814 : decode runtimeBytecode ⟨7814⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨66, by decide⟩
theorem decode_7816 : decode runtimeBytecode ⟨7816⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨67, by decide⟩
theorem decode_7817 : decode runtimeBytecode ⟨7817⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7643⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨68, by decide⟩
theorem decode_7820 : decode runtimeBytecode ⟨7820⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨69, by decide⟩
theorem decode_7821 : decode runtimeBytecode ⟨7821⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨70, by decide⟩
theorem decode_7822 : decode runtimeBytecode ⟨7822⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨71, by decide⟩
theorem decode_7823 : decode runtimeBytecode ⟨7823⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨72, by decide⟩
theorem decode_7825 : decode runtimeBytecode ⟨7825⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨73, by decide⟩
theorem decode_7826 : decode runtimeBytecode ⟨7826⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨74, by decide⟩
theorem decode_7827 : decode runtimeBytecode ⟨7827⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨75, by decide⟩
theorem decode_7828 : decode runtimeBytecode ⟨7828⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨76, by decide⟩
theorem decode_7829 : decode runtimeBytecode ⟨7829⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨77, by decide⟩
theorem decode_7830 : decode runtimeBytecode ⟨7830⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8119⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨78, by decide⟩
theorem decode_7833 : decode runtimeBytecode ⟨7833⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨79, by decide⟩
theorem decode_7834 : decode runtimeBytecode ⟨7834⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨80, by decide⟩
theorem decode_7835 : decode runtimeBytecode ⟨7835⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨81, by decide⟩
theorem decode_7837 : decode runtimeBytecode ⟨7837⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨82, by decide⟩
theorem decode_7838 : decode runtimeBytecode ⟨7838⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8108⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨83, by decide⟩
theorem decode_7841 : decode runtimeBytecode ⟨7841⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨84, by decide⟩
theorem decode_7842 : decode runtimeBytecode ⟨7842⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨85, by decide⟩
theorem decode_7843 : decode runtimeBytecode ⟨7843⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨86, by decide⟩
theorem decode_7845 : decode runtimeBytecode ⟨7845⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨87, by decide⟩
theorem decode_7846 : decode runtimeBytecode ⟨7846⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8097⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨88, by decide⟩
theorem decode_7849 : decode runtimeBytecode ⟨7849⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨89, by decide⟩
theorem decode_7850 : decode runtimeBytecode ⟨7850⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨90, by decide⟩
theorem decode_7851 : decode runtimeBytecode ⟨7851⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨91, by decide⟩
theorem decode_7853 : decode runtimeBytecode ⟨7853⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨92, by decide⟩
theorem decode_7854 : decode runtimeBytecode ⟨7854⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8087⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨93, by decide⟩
theorem decode_7857 : decode runtimeBytecode ⟨7857⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨94, by decide⟩
theorem decode_7858 : decode runtimeBytecode ⟨7858⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨95, by decide⟩
theorem decode_7859 : decode runtimeBytecode ⟨7859⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨96, by decide⟩
theorem decode_7861 : decode runtimeBytecode ⟨7861⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨97, by decide⟩
theorem decode_7862 : decode runtimeBytecode ⟨7862⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8076⟩, 2)) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨98, by decide⟩
theorem decode_7865 : decode runtimeBytecode ⟨7865⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes56] using generatedDecodes56_correct ⟨99, by decide⟩

end Ripemd160Old
