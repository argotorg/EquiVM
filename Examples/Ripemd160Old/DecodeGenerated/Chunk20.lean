import Examples.Ripemd160Old.DecodeGenerated.Chunk19

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes20 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2838⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨2840⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2841⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2980⟩, 2))),
  (⟨2844⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2845⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2846⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨2848⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2849⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2969⟩, 2))),
  (⟨2852⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2853⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2854⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨2855⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2856⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2958⟩, 2))),
  (⟨2859⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2860⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2861⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨2863⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2864⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2947⟩, 2))),
  (⟨2867⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2868⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2869⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨2871⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2872⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2936⟩, 2))),
  (⟨2875⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2876⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2877⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨2879⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2880⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2925⟩, 2))),
  (⟨2883⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2884⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2885⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨2887⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2888⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2914⟩, 2))),
  (⟨2891⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2892⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2894⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2895⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2904⟩, 2))),
  (⟨2898⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2899⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2900⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨453⟩, 2))),
  (⟨2903⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2904⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2905⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2906⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2907⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨2909⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2910⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2913⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2914⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2915⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2916⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2917⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2918⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2920⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2921⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2924⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2925⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2926⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2927⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2928⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2929⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨2931⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2932⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2935⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2936⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2937⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2938⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2939⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2940⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨2942⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2943⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2946⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2947⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2948⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2949⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2950⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2951⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨2953⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2954⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2957⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2958⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2959⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2960⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2961⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2962⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨2964⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2965⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2968⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2969⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2970⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2971⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2972⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2973⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨2975⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2976⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2979⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2980⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2981⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2982⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2983⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes20_correct : ∀ i : Fin generatedDecodes20.size,
    decode runtimeBytecode generatedDecodes20[i].1 = generatedDecodes20[i].2 := by
  native_decide

theorem decode_2838 : decode runtimeBytecode ⟨2838⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨0, by decide⟩
theorem decode_2840 : decode runtimeBytecode ⟨2840⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨1, by decide⟩
theorem decode_2841 : decode runtimeBytecode ⟨2841⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2980⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨2, by decide⟩
theorem decode_2844 : decode runtimeBytecode ⟨2844⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨3, by decide⟩
theorem decode_2845 : decode runtimeBytecode ⟨2845⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨4, by decide⟩
theorem decode_2846 : decode runtimeBytecode ⟨2846⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨5, by decide⟩
theorem decode_2848 : decode runtimeBytecode ⟨2848⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨6, by decide⟩
theorem decode_2849 : decode runtimeBytecode ⟨2849⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2969⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨7, by decide⟩
theorem decode_2852 : decode runtimeBytecode ⟨2852⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨8, by decide⟩
theorem decode_2853 : decode runtimeBytecode ⟨2853⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨9, by decide⟩
theorem decode_2854 : decode runtimeBytecode ⟨2854⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨10, by decide⟩
theorem decode_2855 : decode runtimeBytecode ⟨2855⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨11, by decide⟩
theorem decode_2856 : decode runtimeBytecode ⟨2856⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2958⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨12, by decide⟩
theorem decode_2859 : decode runtimeBytecode ⟨2859⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨13, by decide⟩
theorem decode_2860 : decode runtimeBytecode ⟨2860⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨14, by decide⟩
theorem decode_2861 : decode runtimeBytecode ⟨2861⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨15, by decide⟩
theorem decode_2863 : decode runtimeBytecode ⟨2863⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨16, by decide⟩
theorem decode_2864 : decode runtimeBytecode ⟨2864⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2947⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨17, by decide⟩
theorem decode_2867 : decode runtimeBytecode ⟨2867⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨18, by decide⟩
theorem decode_2868 : decode runtimeBytecode ⟨2868⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨19, by decide⟩
theorem decode_2869 : decode runtimeBytecode ⟨2869⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨20, by decide⟩
theorem decode_2871 : decode runtimeBytecode ⟨2871⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨21, by decide⟩
theorem decode_2872 : decode runtimeBytecode ⟨2872⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2936⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨22, by decide⟩
theorem decode_2875 : decode runtimeBytecode ⟨2875⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨23, by decide⟩
theorem decode_2876 : decode runtimeBytecode ⟨2876⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨24, by decide⟩
theorem decode_2877 : decode runtimeBytecode ⟨2877⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨25, by decide⟩
theorem decode_2879 : decode runtimeBytecode ⟨2879⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨26, by decide⟩
theorem decode_2880 : decode runtimeBytecode ⟨2880⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2925⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨27, by decide⟩
theorem decode_2883 : decode runtimeBytecode ⟨2883⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨28, by decide⟩
theorem decode_2884 : decode runtimeBytecode ⟨2884⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨29, by decide⟩
theorem decode_2885 : decode runtimeBytecode ⟨2885⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨30, by decide⟩
theorem decode_2887 : decode runtimeBytecode ⟨2887⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨31, by decide⟩
theorem decode_2888 : decode runtimeBytecode ⟨2888⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2914⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨32, by decide⟩
theorem decode_2891 : decode runtimeBytecode ⟨2891⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨33, by decide⟩
theorem decode_2892 : decode runtimeBytecode ⟨2892⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨34, by decide⟩
theorem decode_2894 : decode runtimeBytecode ⟨2894⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨35, by decide⟩
theorem decode_2895 : decode runtimeBytecode ⟨2895⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2904⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨36, by decide⟩
theorem decode_2898 : decode runtimeBytecode ⟨2898⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨37, by decide⟩
theorem decode_2899 : decode runtimeBytecode ⟨2899⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨38, by decide⟩
theorem decode_2900 : decode runtimeBytecode ⟨2900⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨453⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨39, by decide⟩
theorem decode_2903 : decode runtimeBytecode ⟨2903⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨40, by decide⟩
theorem decode_2904 : decode runtimeBytecode ⟨2904⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨41, by decide⟩
theorem decode_2905 : decode runtimeBytecode ⟨2905⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨42, by decide⟩
theorem decode_2906 : decode runtimeBytecode ⟨2906⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨43, by decide⟩
theorem decode_2907 : decode runtimeBytecode ⟨2907⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨44, by decide⟩
theorem decode_2909 : decode runtimeBytecode ⟨2909⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨45, by decide⟩
theorem decode_2910 : decode runtimeBytecode ⟨2910⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨46, by decide⟩
theorem decode_2913 : decode runtimeBytecode ⟨2913⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨47, by decide⟩
theorem decode_2914 : decode runtimeBytecode ⟨2914⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨48, by decide⟩
theorem decode_2915 : decode runtimeBytecode ⟨2915⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨49, by decide⟩
theorem decode_2916 : decode runtimeBytecode ⟨2916⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨50, by decide⟩
theorem decode_2917 : decode runtimeBytecode ⟨2917⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨51, by decide⟩
theorem decode_2918 : decode runtimeBytecode ⟨2918⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨52, by decide⟩
theorem decode_2920 : decode runtimeBytecode ⟨2920⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨53, by decide⟩
theorem decode_2921 : decode runtimeBytecode ⟨2921⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨54, by decide⟩
theorem decode_2924 : decode runtimeBytecode ⟨2924⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨55, by decide⟩
theorem decode_2925 : decode runtimeBytecode ⟨2925⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨56, by decide⟩
theorem decode_2926 : decode runtimeBytecode ⟨2926⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨57, by decide⟩
theorem decode_2927 : decode runtimeBytecode ⟨2927⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨58, by decide⟩
theorem decode_2928 : decode runtimeBytecode ⟨2928⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨59, by decide⟩
theorem decode_2929 : decode runtimeBytecode ⟨2929⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨60, by decide⟩
theorem decode_2931 : decode runtimeBytecode ⟨2931⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨61, by decide⟩
theorem decode_2932 : decode runtimeBytecode ⟨2932⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨62, by decide⟩
theorem decode_2935 : decode runtimeBytecode ⟨2935⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨63, by decide⟩
theorem decode_2936 : decode runtimeBytecode ⟨2936⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨64, by decide⟩
theorem decode_2937 : decode runtimeBytecode ⟨2937⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨65, by decide⟩
theorem decode_2938 : decode runtimeBytecode ⟨2938⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨66, by decide⟩
theorem decode_2939 : decode runtimeBytecode ⟨2939⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨67, by decide⟩
theorem decode_2940 : decode runtimeBytecode ⟨2940⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨68, by decide⟩
theorem decode_2942 : decode runtimeBytecode ⟨2942⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨69, by decide⟩
theorem decode_2943 : decode runtimeBytecode ⟨2943⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨70, by decide⟩
theorem decode_2946 : decode runtimeBytecode ⟨2946⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨71, by decide⟩
theorem decode_2947 : decode runtimeBytecode ⟨2947⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨72, by decide⟩
theorem decode_2948 : decode runtimeBytecode ⟨2948⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨73, by decide⟩
theorem decode_2949 : decode runtimeBytecode ⟨2949⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨74, by decide⟩
theorem decode_2950 : decode runtimeBytecode ⟨2950⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨75, by decide⟩
theorem decode_2951 : decode runtimeBytecode ⟨2951⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨76, by decide⟩
theorem decode_2953 : decode runtimeBytecode ⟨2953⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨77, by decide⟩
theorem decode_2954 : decode runtimeBytecode ⟨2954⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨78, by decide⟩
theorem decode_2957 : decode runtimeBytecode ⟨2957⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨79, by decide⟩
theorem decode_2958 : decode runtimeBytecode ⟨2958⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨80, by decide⟩
theorem decode_2959 : decode runtimeBytecode ⟨2959⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨81, by decide⟩
theorem decode_2960 : decode runtimeBytecode ⟨2960⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨82, by decide⟩
theorem decode_2961 : decode runtimeBytecode ⟨2961⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨83, by decide⟩
theorem decode_2962 : decode runtimeBytecode ⟨2962⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨84, by decide⟩
theorem decode_2964 : decode runtimeBytecode ⟨2964⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨85, by decide⟩
theorem decode_2965 : decode runtimeBytecode ⟨2965⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨86, by decide⟩
theorem decode_2968 : decode runtimeBytecode ⟨2968⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨87, by decide⟩
theorem decode_2969 : decode runtimeBytecode ⟨2969⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨88, by decide⟩
theorem decode_2970 : decode runtimeBytecode ⟨2970⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨89, by decide⟩
theorem decode_2971 : decode runtimeBytecode ⟨2971⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨90, by decide⟩
theorem decode_2972 : decode runtimeBytecode ⟨2972⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨91, by decide⟩
theorem decode_2973 : decode runtimeBytecode ⟨2973⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨92, by decide⟩
theorem decode_2975 : decode runtimeBytecode ⟨2975⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨93, by decide⟩
theorem decode_2976 : decode runtimeBytecode ⟨2976⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨94, by decide⟩
theorem decode_2979 : decode runtimeBytecode ⟨2979⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨95, by decide⟩
theorem decode_2980 : decode runtimeBytecode ⟨2980⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨96, by decide⟩
theorem decode_2981 : decode runtimeBytecode ⟨2981⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨97, by decide⟩
theorem decode_2982 : decode runtimeBytecode ⟨2982⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨98, by decide⟩
theorem decode_2983 : decode runtimeBytecode ⟨2983⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes20] using generatedDecodes20_correct ⟨99, by decide⟩

end Ripemd160Old
