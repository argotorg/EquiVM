import Examples.Ripemd160Old.DecodeGenerated.Chunk20

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes21 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2984⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨2986⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2987⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨2990⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2991⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2992⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2993⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2994⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2995⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨2996⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2997⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3000⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3001⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3002⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3003⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3004⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3005⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3007⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3008⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3011⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3012⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3013⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3014⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3015⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3016⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨3018⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3019⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3022⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3023⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3024⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3025⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3026⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3027⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨3029⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3030⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3033⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3034⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3035⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3036⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3037⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3038⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨3040⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3041⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3044⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3045⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3046⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3047⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3048⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3049⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3051⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3052⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3055⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3056⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3057⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3058⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3059⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3060⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3061⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3062⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3065⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3066⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3067⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3068⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3069⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨3070⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3072⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨3073⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2))),
  (⟨3076⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨3077⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨3078⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨48⟩, 1))),
  (⟨3080⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨3081⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨3082⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3083⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨3084⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3085⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3374⟩, 2))),
  (⟨3088⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3089⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3090⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨3092⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3093⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3363⟩, 2))),
  (⟨3096⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3097⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3098⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨3100⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3101⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3352⟩, 2))),
  (⟨3104⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3105⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3106⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨3108⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3109⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3342⟩, 2))),
  (⟨3112⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3113⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3114⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨3116⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨3117⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3332⟩, 2))),
  (⟨3120⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨3121⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨3122⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨3124⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none))
]

private theorem generatedDecodes21_correct : ∀ i : Fin generatedDecodes21.size,
    decode runtimeBytecode generatedDecodes21[i].1 = generatedDecodes21[i].2 := by
  native_decide

theorem decode_2984 : decode runtimeBytecode ⟨2984⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨0, by decide⟩
theorem decode_2986 : decode runtimeBytecode ⟨2986⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨1, by decide⟩
theorem decode_2987 : decode runtimeBytecode ⟨2987⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨2, by decide⟩
theorem decode_2990 : decode runtimeBytecode ⟨2990⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨3, by decide⟩
theorem decode_2991 : decode runtimeBytecode ⟨2991⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨4, by decide⟩
theorem decode_2992 : decode runtimeBytecode ⟨2992⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨5, by decide⟩
theorem decode_2993 : decode runtimeBytecode ⟨2993⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨6, by decide⟩
theorem decode_2994 : decode runtimeBytecode ⟨2994⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨7, by decide⟩
theorem decode_2995 : decode runtimeBytecode ⟨2995⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨8, by decide⟩
theorem decode_2996 : decode runtimeBytecode ⟨2996⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨9, by decide⟩
theorem decode_2997 : decode runtimeBytecode ⟨2997⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨10, by decide⟩
theorem decode_3000 : decode runtimeBytecode ⟨3000⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨11, by decide⟩
theorem decode_3001 : decode runtimeBytecode ⟨3001⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨12, by decide⟩
theorem decode_3002 : decode runtimeBytecode ⟨3002⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨13, by decide⟩
theorem decode_3003 : decode runtimeBytecode ⟨3003⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨14, by decide⟩
theorem decode_3004 : decode runtimeBytecode ⟨3004⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨15, by decide⟩
theorem decode_3005 : decode runtimeBytecode ⟨3005⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨16, by decide⟩
theorem decode_3007 : decode runtimeBytecode ⟨3007⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨17, by decide⟩
theorem decode_3008 : decode runtimeBytecode ⟨3008⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨18, by decide⟩
theorem decode_3011 : decode runtimeBytecode ⟨3011⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨19, by decide⟩
theorem decode_3012 : decode runtimeBytecode ⟨3012⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨20, by decide⟩
theorem decode_3013 : decode runtimeBytecode ⟨3013⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨21, by decide⟩
theorem decode_3014 : decode runtimeBytecode ⟨3014⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨22, by decide⟩
theorem decode_3015 : decode runtimeBytecode ⟨3015⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨23, by decide⟩
theorem decode_3016 : decode runtimeBytecode ⟨3016⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨24, by decide⟩
theorem decode_3018 : decode runtimeBytecode ⟨3018⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨25, by decide⟩
theorem decode_3019 : decode runtimeBytecode ⟨3019⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨26, by decide⟩
theorem decode_3022 : decode runtimeBytecode ⟨3022⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨27, by decide⟩
theorem decode_3023 : decode runtimeBytecode ⟨3023⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨28, by decide⟩
theorem decode_3024 : decode runtimeBytecode ⟨3024⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨29, by decide⟩
theorem decode_3025 : decode runtimeBytecode ⟨3025⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨30, by decide⟩
theorem decode_3026 : decode runtimeBytecode ⟨3026⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨31, by decide⟩
theorem decode_3027 : decode runtimeBytecode ⟨3027⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨32, by decide⟩
theorem decode_3029 : decode runtimeBytecode ⟨3029⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨33, by decide⟩
theorem decode_3030 : decode runtimeBytecode ⟨3030⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨34, by decide⟩
theorem decode_3033 : decode runtimeBytecode ⟨3033⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨35, by decide⟩
theorem decode_3034 : decode runtimeBytecode ⟨3034⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨36, by decide⟩
theorem decode_3035 : decode runtimeBytecode ⟨3035⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨37, by decide⟩
theorem decode_3036 : decode runtimeBytecode ⟨3036⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨38, by decide⟩
theorem decode_3037 : decode runtimeBytecode ⟨3037⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨39, by decide⟩
theorem decode_3038 : decode runtimeBytecode ⟨3038⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨40, by decide⟩
theorem decode_3040 : decode runtimeBytecode ⟨3040⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨41, by decide⟩
theorem decode_3041 : decode runtimeBytecode ⟨3041⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨42, by decide⟩
theorem decode_3044 : decode runtimeBytecode ⟨3044⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨43, by decide⟩
theorem decode_3045 : decode runtimeBytecode ⟨3045⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨44, by decide⟩
theorem decode_3046 : decode runtimeBytecode ⟨3046⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨45, by decide⟩
theorem decode_3047 : decode runtimeBytecode ⟨3047⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨46, by decide⟩
theorem decode_3048 : decode runtimeBytecode ⟨3048⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨47, by decide⟩
theorem decode_3049 : decode runtimeBytecode ⟨3049⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨48, by decide⟩
theorem decode_3051 : decode runtimeBytecode ⟨3051⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨49, by decide⟩
theorem decode_3052 : decode runtimeBytecode ⟨3052⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨50, by decide⟩
theorem decode_3055 : decode runtimeBytecode ⟨3055⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨51, by decide⟩
theorem decode_3056 : decode runtimeBytecode ⟨3056⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨52, by decide⟩
theorem decode_3057 : decode runtimeBytecode ⟨3057⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨53, by decide⟩
theorem decode_3058 : decode runtimeBytecode ⟨3058⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨54, by decide⟩
theorem decode_3059 : decode runtimeBytecode ⟨3059⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨55, by decide⟩
theorem decode_3060 : decode runtimeBytecode ⟨3060⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨56, by decide⟩
theorem decode_3061 : decode runtimeBytecode ⟨3061⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨57, by decide⟩
theorem decode_3062 : decode runtimeBytecode ⟨3062⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨58, by decide⟩
theorem decode_3065 : decode runtimeBytecode ⟨3065⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨59, by decide⟩
theorem decode_3066 : decode runtimeBytecode ⟨3066⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨60, by decide⟩
theorem decode_3067 : decode runtimeBytecode ⟨3067⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨61, by decide⟩
theorem decode_3068 : decode runtimeBytecode ⟨3068⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨62, by decide⟩
theorem decode_3069 : decode runtimeBytecode ⟨3069⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨63, by decide⟩
theorem decode_3070 : decode runtimeBytecode ⟨3070⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨64, by decide⟩
theorem decode_3072 : decode runtimeBytecode ⟨3072⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨65, by decide⟩
theorem decode_3073 : decode runtimeBytecode ⟨3073⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2899⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨66, by decide⟩
theorem decode_3076 : decode runtimeBytecode ⟨3076⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨67, by decide⟩
theorem decode_3077 : decode runtimeBytecode ⟨3077⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨68, by decide⟩
theorem decode_3078 : decode runtimeBytecode ⟨3078⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨48⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨69, by decide⟩
theorem decode_3080 : decode runtimeBytecode ⟨3080⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨70, by decide⟩
theorem decode_3081 : decode runtimeBytecode ⟨3081⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨71, by decide⟩
theorem decode_3082 : decode runtimeBytecode ⟨3082⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨72, by decide⟩
theorem decode_3083 : decode runtimeBytecode ⟨3083⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨73, by decide⟩
theorem decode_3084 : decode runtimeBytecode ⟨3084⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨74, by decide⟩
theorem decode_3085 : decode runtimeBytecode ⟨3085⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3374⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨75, by decide⟩
theorem decode_3088 : decode runtimeBytecode ⟨3088⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨76, by decide⟩
theorem decode_3089 : decode runtimeBytecode ⟨3089⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨77, by decide⟩
theorem decode_3090 : decode runtimeBytecode ⟨3090⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨78, by decide⟩
theorem decode_3092 : decode runtimeBytecode ⟨3092⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨79, by decide⟩
theorem decode_3093 : decode runtimeBytecode ⟨3093⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3363⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨80, by decide⟩
theorem decode_3096 : decode runtimeBytecode ⟨3096⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨81, by decide⟩
theorem decode_3097 : decode runtimeBytecode ⟨3097⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨82, by decide⟩
theorem decode_3098 : decode runtimeBytecode ⟨3098⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨83, by decide⟩
theorem decode_3100 : decode runtimeBytecode ⟨3100⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨84, by decide⟩
theorem decode_3101 : decode runtimeBytecode ⟨3101⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3352⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨85, by decide⟩
theorem decode_3104 : decode runtimeBytecode ⟨3104⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨86, by decide⟩
theorem decode_3105 : decode runtimeBytecode ⟨3105⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨87, by decide⟩
theorem decode_3106 : decode runtimeBytecode ⟨3106⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨88, by decide⟩
theorem decode_3108 : decode runtimeBytecode ⟨3108⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨89, by decide⟩
theorem decode_3109 : decode runtimeBytecode ⟨3109⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3342⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨90, by decide⟩
theorem decode_3112 : decode runtimeBytecode ⟨3112⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨91, by decide⟩
theorem decode_3113 : decode runtimeBytecode ⟨3113⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨92, by decide⟩
theorem decode_3114 : decode runtimeBytecode ⟨3114⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨93, by decide⟩
theorem decode_3116 : decode runtimeBytecode ⟨3116⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨94, by decide⟩
theorem decode_3117 : decode runtimeBytecode ⟨3117⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨3332⟩, 2)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨95, by decide⟩
theorem decode_3120 : decode runtimeBytecode ⟨3120⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨96, by decide⟩
theorem decode_3121 : decode runtimeBytecode ⟨3121⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨97, by decide⟩
theorem decode_3122 : decode runtimeBytecode ⟨3122⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨98, by decide⟩
theorem decode_3124 : decode runtimeBytecode ⟨3124⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes21] using generatedDecodes21_correct ⟨99, by decide⟩

end Ripemd160Old
