import Examples.Ripemd160Old.DecodeGenerated.Chunk18

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes19 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2703⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2704⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2705⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2706⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2707⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2708⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2711⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2712⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2713⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2714⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2715⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2716⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2717⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2718⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2719⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2720⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2722⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2723⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2724⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2725⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2726⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2727⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2730⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2731⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2732⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2733⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2734⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2735⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2736⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2737⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2738⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2739⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨2741⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2742⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2743⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2744⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2745⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2746⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2749⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2750⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2751⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2752⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2753⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2754⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2755⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2756⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2757⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2758⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨2760⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2761⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2762⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2763⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2764⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2765⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2768⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2769⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2770⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨2772⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨2773⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨2774⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2775⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨2776⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2777⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3066⟩, 2))),
  (⟨2780⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2781⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2782⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨2784⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2785⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3056⟩, 2))),
  (⟨2788⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2789⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2790⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨2792⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2793⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3045⟩, 2))),
  (⟨2796⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2797⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2798⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨2800⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2801⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3034⟩, 2))),
  (⟨2804⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2805⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2806⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨2808⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2809⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3023⟩, 2))),
  (⟨2812⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2813⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2814⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨2816⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2817⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3012⟩, 2))),
  (⟨2820⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2821⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2822⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨2824⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2825⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3001⟩, 2))),
  (⟨2828⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2829⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2830⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨2832⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2833⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2991⟩, 2))),
  (⟨2836⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2837⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none))
]

private theorem generatedDecodes19_correct : ∀ i : Fin generatedDecodes19.size,
    decode runtimeBytecode generatedDecodes19[i].1 = generatedDecodes19[i].2 := by
  native_decide

theorem decode_2703 : decode runtimeBytecode ⟨2703⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨0, by decide⟩
theorem decode_2704 : decode runtimeBytecode ⟨2704⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨1, by decide⟩
theorem decode_2705 : decode runtimeBytecode ⟨2705⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨2, by decide⟩
theorem decode_2706 : decode runtimeBytecode ⟨2706⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨3, by decide⟩
theorem decode_2707 : decode runtimeBytecode ⟨2707⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨4, by decide⟩
theorem decode_2708 : decode runtimeBytecode ⟨2708⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨5, by decide⟩
theorem decode_2711 : decode runtimeBytecode ⟨2711⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨6, by decide⟩
theorem decode_2712 : decode runtimeBytecode ⟨2712⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨7, by decide⟩
theorem decode_2713 : decode runtimeBytecode ⟨2713⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨8, by decide⟩
theorem decode_2714 : decode runtimeBytecode ⟨2714⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨9, by decide⟩
theorem decode_2715 : decode runtimeBytecode ⟨2715⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨10, by decide⟩
theorem decode_2716 : decode runtimeBytecode ⟨2716⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨11, by decide⟩
theorem decode_2717 : decode runtimeBytecode ⟨2717⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨12, by decide⟩
theorem decode_2718 : decode runtimeBytecode ⟨2718⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨13, by decide⟩
theorem decode_2719 : decode runtimeBytecode ⟨2719⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨14, by decide⟩
theorem decode_2720 : decode runtimeBytecode ⟨2720⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨15, by decide⟩
theorem decode_2722 : decode runtimeBytecode ⟨2722⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨16, by decide⟩
theorem decode_2723 : decode runtimeBytecode ⟨2723⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨17, by decide⟩
theorem decode_2724 : decode runtimeBytecode ⟨2724⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨18, by decide⟩
theorem decode_2725 : decode runtimeBytecode ⟨2725⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨19, by decide⟩
theorem decode_2726 : decode runtimeBytecode ⟨2726⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨20, by decide⟩
theorem decode_2727 : decode runtimeBytecode ⟨2727⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨21, by decide⟩
theorem decode_2730 : decode runtimeBytecode ⟨2730⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨22, by decide⟩
theorem decode_2731 : decode runtimeBytecode ⟨2731⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨23, by decide⟩
theorem decode_2732 : decode runtimeBytecode ⟨2732⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨24, by decide⟩
theorem decode_2733 : decode runtimeBytecode ⟨2733⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨25, by decide⟩
theorem decode_2734 : decode runtimeBytecode ⟨2734⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨26, by decide⟩
theorem decode_2735 : decode runtimeBytecode ⟨2735⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨27, by decide⟩
theorem decode_2736 : decode runtimeBytecode ⟨2736⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨28, by decide⟩
theorem decode_2737 : decode runtimeBytecode ⟨2737⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨29, by decide⟩
theorem decode_2738 : decode runtimeBytecode ⟨2738⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨30, by decide⟩
theorem decode_2739 : decode runtimeBytecode ⟨2739⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨31, by decide⟩
theorem decode_2741 : decode runtimeBytecode ⟨2741⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨32, by decide⟩
theorem decode_2742 : decode runtimeBytecode ⟨2742⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨33, by decide⟩
theorem decode_2743 : decode runtimeBytecode ⟨2743⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨34, by decide⟩
theorem decode_2744 : decode runtimeBytecode ⟨2744⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨35, by decide⟩
theorem decode_2745 : decode runtimeBytecode ⟨2745⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨36, by decide⟩
theorem decode_2746 : decode runtimeBytecode ⟨2746⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨37, by decide⟩
theorem decode_2749 : decode runtimeBytecode ⟨2749⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨38, by decide⟩
theorem decode_2750 : decode runtimeBytecode ⟨2750⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨39, by decide⟩
theorem decode_2751 : decode runtimeBytecode ⟨2751⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨40, by decide⟩
theorem decode_2752 : decode runtimeBytecode ⟨2752⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨41, by decide⟩
theorem decode_2753 : decode runtimeBytecode ⟨2753⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨42, by decide⟩
theorem decode_2754 : decode runtimeBytecode ⟨2754⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨43, by decide⟩
theorem decode_2755 : decode runtimeBytecode ⟨2755⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨44, by decide⟩
theorem decode_2756 : decode runtimeBytecode ⟨2756⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨45, by decide⟩
theorem decode_2757 : decode runtimeBytecode ⟨2757⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨46, by decide⟩
theorem decode_2758 : decode runtimeBytecode ⟨2758⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨47, by decide⟩
theorem decode_2760 : decode runtimeBytecode ⟨2760⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨48, by decide⟩
theorem decode_2761 : decode runtimeBytecode ⟨2761⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨49, by decide⟩
theorem decode_2762 : decode runtimeBytecode ⟨2762⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨50, by decide⟩
theorem decode_2763 : decode runtimeBytecode ⟨2763⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨51, by decide⟩
theorem decode_2764 : decode runtimeBytecode ⟨2764⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨52, by decide⟩
theorem decode_2765 : decode runtimeBytecode ⟨2765⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨53, by decide⟩
theorem decode_2768 : decode runtimeBytecode ⟨2768⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨54, by decide⟩
theorem decode_2769 : decode runtimeBytecode ⟨2769⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨55, by decide⟩
theorem decode_2770 : decode runtimeBytecode ⟨2770⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨56, by decide⟩
theorem decode_2772 : decode runtimeBytecode ⟨2772⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨57, by decide⟩
theorem decode_2773 : decode runtimeBytecode ⟨2773⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨58, by decide⟩
theorem decode_2774 : decode runtimeBytecode ⟨2774⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨59, by decide⟩
theorem decode_2775 : decode runtimeBytecode ⟨2775⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨60, by decide⟩
theorem decode_2776 : decode runtimeBytecode ⟨2776⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨61, by decide⟩
theorem decode_2777 : decode runtimeBytecode ⟨2777⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3066⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨62, by decide⟩
theorem decode_2780 : decode runtimeBytecode ⟨2780⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨63, by decide⟩
theorem decode_2781 : decode runtimeBytecode ⟨2781⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨64, by decide⟩
theorem decode_2782 : decode runtimeBytecode ⟨2782⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨65, by decide⟩
theorem decode_2784 : decode runtimeBytecode ⟨2784⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨66, by decide⟩
theorem decode_2785 : decode runtimeBytecode ⟨2785⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3056⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨67, by decide⟩
theorem decode_2788 : decode runtimeBytecode ⟨2788⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨68, by decide⟩
theorem decode_2789 : decode runtimeBytecode ⟨2789⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨69, by decide⟩
theorem decode_2790 : decode runtimeBytecode ⟨2790⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨70, by decide⟩
theorem decode_2792 : decode runtimeBytecode ⟨2792⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨71, by decide⟩
theorem decode_2793 : decode runtimeBytecode ⟨2793⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3045⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨72, by decide⟩
theorem decode_2796 : decode runtimeBytecode ⟨2796⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨73, by decide⟩
theorem decode_2797 : decode runtimeBytecode ⟨2797⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨74, by decide⟩
theorem decode_2798 : decode runtimeBytecode ⟨2798⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨75, by decide⟩
theorem decode_2800 : decode runtimeBytecode ⟨2800⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨76, by decide⟩
theorem decode_2801 : decode runtimeBytecode ⟨2801⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3034⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨77, by decide⟩
theorem decode_2804 : decode runtimeBytecode ⟨2804⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨78, by decide⟩
theorem decode_2805 : decode runtimeBytecode ⟨2805⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨79, by decide⟩
theorem decode_2806 : decode runtimeBytecode ⟨2806⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨80, by decide⟩
theorem decode_2808 : decode runtimeBytecode ⟨2808⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨81, by decide⟩
theorem decode_2809 : decode runtimeBytecode ⟨2809⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3023⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨82, by decide⟩
theorem decode_2812 : decode runtimeBytecode ⟨2812⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨83, by decide⟩
theorem decode_2813 : decode runtimeBytecode ⟨2813⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨84, by decide⟩
theorem decode_2814 : decode runtimeBytecode ⟨2814⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨85, by decide⟩
theorem decode_2816 : decode runtimeBytecode ⟨2816⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨86, by decide⟩
theorem decode_2817 : decode runtimeBytecode ⟨2817⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3012⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨87, by decide⟩
theorem decode_2820 : decode runtimeBytecode ⟨2820⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨88, by decide⟩
theorem decode_2821 : decode runtimeBytecode ⟨2821⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨89, by decide⟩
theorem decode_2822 : decode runtimeBytecode ⟨2822⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨90, by decide⟩
theorem decode_2824 : decode runtimeBytecode ⟨2824⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨91, by decide⟩
theorem decode_2825 : decode runtimeBytecode ⟨2825⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3001⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨92, by decide⟩
theorem decode_2828 : decode runtimeBytecode ⟨2828⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨93, by decide⟩
theorem decode_2829 : decode runtimeBytecode ⟨2829⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨94, by decide⟩
theorem decode_2830 : decode runtimeBytecode ⟨2830⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨95, by decide⟩
theorem decode_2832 : decode runtimeBytecode ⟨2832⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨96, by decide⟩
theorem decode_2833 : decode runtimeBytecode ⟨2833⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2991⟩, 2)) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨97, by decide⟩
theorem decode_2836 : decode runtimeBytecode ⟨2836⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨98, by decide⟩
theorem decode_2837 : decode runtimeBytecode ⟨2837⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes19] using generatedDecodes19_correct ⟨99, by decide⟩

end Ripemd160Old
