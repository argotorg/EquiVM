import Examples.Ripemd160Old.DecodeGenerated.Chunk52

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes53 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨7291⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7391⟩, 2))),
  (⟨7294⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7295⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7296⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7298⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7299⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7380⟩, 2))),
  (⟨7302⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7303⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7304⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7306⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7307⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7370⟩, 2))),
  (⟨7310⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7311⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7312⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7314⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7315⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7360⟩, 2))),
  (⟨7318⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7319⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨7320⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨7322⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7323⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7349⟩, 2))),
  (⟨7326⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7327⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨7329⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨7330⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7339⟩, 2))),
  (⟨7333⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨7334⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7335⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2))),
  (⟨7338⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7339⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7340⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7341⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7342⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨7344⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7345⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7348⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7349⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7350⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7351⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7352⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7353⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨7355⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7356⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7359⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7360⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7361⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7362⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7363⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7364⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨7365⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7366⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7369⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7370⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7371⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7372⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7373⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7374⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none)),
  (⟨7375⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7376⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7379⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7380⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7381⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7382⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7383⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7384⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨7386⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7387⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7390⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7391⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7392⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7393⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7394⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7395⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨7397⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7398⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7401⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7402⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7403⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7404⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7405⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7406⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨7408⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7409⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7412⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7413⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7414⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7415⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7416⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7417⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨7419⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7420⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7423⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨7424⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨7425⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7426⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7427⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨7428⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨7430⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨7431⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2))),
  (⟨7434⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none))
]

private theorem generatedDecodes53_correct : ∀ i : Fin generatedDecodes53.size,
    decode runtimeBytecode generatedDecodes53[i].1 = generatedDecodes53[i].2 := by
  native_decide

theorem decode_7291 : decode runtimeBytecode ⟨7291⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7391⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨0, by decide⟩
theorem decode_7294 : decode runtimeBytecode ⟨7294⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨1, by decide⟩
theorem decode_7295 : decode runtimeBytecode ⟨7295⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨2, by decide⟩
theorem decode_7296 : decode runtimeBytecode ⟨7296⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨3, by decide⟩
theorem decode_7298 : decode runtimeBytecode ⟨7298⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨4, by decide⟩
theorem decode_7299 : decode runtimeBytecode ⟨7299⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7380⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨5, by decide⟩
theorem decode_7302 : decode runtimeBytecode ⟨7302⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨6, by decide⟩
theorem decode_7303 : decode runtimeBytecode ⟨7303⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨7, by decide⟩
theorem decode_7304 : decode runtimeBytecode ⟨7304⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨8, by decide⟩
theorem decode_7306 : decode runtimeBytecode ⟨7306⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨9, by decide⟩
theorem decode_7307 : decode runtimeBytecode ⟨7307⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7370⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨10, by decide⟩
theorem decode_7310 : decode runtimeBytecode ⟨7310⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨11, by decide⟩
theorem decode_7311 : decode runtimeBytecode ⟨7311⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨12, by decide⟩
theorem decode_7312 : decode runtimeBytecode ⟨7312⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨13, by decide⟩
theorem decode_7314 : decode runtimeBytecode ⟨7314⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨14, by decide⟩
theorem decode_7315 : decode runtimeBytecode ⟨7315⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7360⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨15, by decide⟩
theorem decode_7318 : decode runtimeBytecode ⟨7318⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨16, by decide⟩
theorem decode_7319 : decode runtimeBytecode ⟨7319⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨17, by decide⟩
theorem decode_7320 : decode runtimeBytecode ⟨7320⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨18, by decide⟩
theorem decode_7322 : decode runtimeBytecode ⟨7322⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨19, by decide⟩
theorem decode_7323 : decode runtimeBytecode ⟨7323⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7349⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨20, by decide⟩
theorem decode_7326 : decode runtimeBytecode ⟨7326⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨21, by decide⟩
theorem decode_7327 : decode runtimeBytecode ⟨7327⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨22, by decide⟩
theorem decode_7329 : decode runtimeBytecode ⟨7329⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨23, by decide⟩
theorem decode_7330 : decode runtimeBytecode ⟨7330⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7339⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨24, by decide⟩
theorem decode_7333 : decode runtimeBytecode ⟨7333⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨25, by decide⟩
theorem decode_7334 : decode runtimeBytecode ⟨7334⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨26, by decide⟩
theorem decode_7335 : decode runtimeBytecode ⟨7335⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨4270⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨27, by decide⟩
theorem decode_7338 : decode runtimeBytecode ⟨7338⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨28, by decide⟩
theorem decode_7339 : decode runtimeBytecode ⟨7339⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨29, by decide⟩
theorem decode_7340 : decode runtimeBytecode ⟨7340⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨30, by decide⟩
theorem decode_7341 : decode runtimeBytecode ⟨7341⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨31, by decide⟩
theorem decode_7342 : decode runtimeBytecode ⟨7342⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨32, by decide⟩
theorem decode_7344 : decode runtimeBytecode ⟨7344⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨33, by decide⟩
theorem decode_7345 : decode runtimeBytecode ⟨7345⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨34, by decide⟩
theorem decode_7348 : decode runtimeBytecode ⟨7348⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨35, by decide⟩
theorem decode_7349 : decode runtimeBytecode ⟨7349⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨36, by decide⟩
theorem decode_7350 : decode runtimeBytecode ⟨7350⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨37, by decide⟩
theorem decode_7351 : decode runtimeBytecode ⟨7351⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨38, by decide⟩
theorem decode_7352 : decode runtimeBytecode ⟨7352⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨39, by decide⟩
theorem decode_7353 : decode runtimeBytecode ⟨7353⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨40, by decide⟩
theorem decode_7355 : decode runtimeBytecode ⟨7355⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨41, by decide⟩
theorem decode_7356 : decode runtimeBytecode ⟨7356⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨42, by decide⟩
theorem decode_7359 : decode runtimeBytecode ⟨7359⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨43, by decide⟩
theorem decode_7360 : decode runtimeBytecode ⟨7360⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨44, by decide⟩
theorem decode_7361 : decode runtimeBytecode ⟨7361⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨45, by decide⟩
theorem decode_7362 : decode runtimeBytecode ⟨7362⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨46, by decide⟩
theorem decode_7363 : decode runtimeBytecode ⟨7363⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨47, by decide⟩
theorem decode_7364 : decode runtimeBytecode ⟨7364⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨48, by decide⟩
theorem decode_7365 : decode runtimeBytecode ⟨7365⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨49, by decide⟩
theorem decode_7366 : decode runtimeBytecode ⟨7366⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨50, by decide⟩
theorem decode_7369 : decode runtimeBytecode ⟨7369⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨51, by decide⟩
theorem decode_7370 : decode runtimeBytecode ⟨7370⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨52, by decide⟩
theorem decode_7371 : decode runtimeBytecode ⟨7371⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨53, by decide⟩
theorem decode_7372 : decode runtimeBytecode ⟨7372⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨54, by decide⟩
theorem decode_7373 : decode runtimeBytecode ⟨7373⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨55, by decide⟩
theorem decode_7374 : decode runtimeBytecode ⟨7374⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP14), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨56, by decide⟩
theorem decode_7375 : decode runtimeBytecode ⟨7375⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨57, by decide⟩
theorem decode_7376 : decode runtimeBytecode ⟨7376⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨58, by decide⟩
theorem decode_7379 : decode runtimeBytecode ⟨7379⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨59, by decide⟩
theorem decode_7380 : decode runtimeBytecode ⟨7380⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨60, by decide⟩
theorem decode_7381 : decode runtimeBytecode ⟨7381⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨61, by decide⟩
theorem decode_7382 : decode runtimeBytecode ⟨7382⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨62, by decide⟩
theorem decode_7383 : decode runtimeBytecode ⟨7383⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨63, by decide⟩
theorem decode_7384 : decode runtimeBytecode ⟨7384⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨64, by decide⟩
theorem decode_7386 : decode runtimeBytecode ⟨7386⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨65, by decide⟩
theorem decode_7387 : decode runtimeBytecode ⟨7387⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨66, by decide⟩
theorem decode_7390 : decode runtimeBytecode ⟨7390⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨67, by decide⟩
theorem decode_7391 : decode runtimeBytecode ⟨7391⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨68, by decide⟩
theorem decode_7392 : decode runtimeBytecode ⟨7392⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨69, by decide⟩
theorem decode_7393 : decode runtimeBytecode ⟨7393⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨70, by decide⟩
theorem decode_7394 : decode runtimeBytecode ⟨7394⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨71, by decide⟩
theorem decode_7395 : decode runtimeBytecode ⟨7395⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨72, by decide⟩
theorem decode_7397 : decode runtimeBytecode ⟨7397⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨73, by decide⟩
theorem decode_7398 : decode runtimeBytecode ⟨7398⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨74, by decide⟩
theorem decode_7401 : decode runtimeBytecode ⟨7401⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨75, by decide⟩
theorem decode_7402 : decode runtimeBytecode ⟨7402⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨76, by decide⟩
theorem decode_7403 : decode runtimeBytecode ⟨7403⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨77, by decide⟩
theorem decode_7404 : decode runtimeBytecode ⟨7404⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨78, by decide⟩
theorem decode_7405 : decode runtimeBytecode ⟨7405⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨79, by decide⟩
theorem decode_7406 : decode runtimeBytecode ⟨7406⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨80, by decide⟩
theorem decode_7408 : decode runtimeBytecode ⟨7408⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨81, by decide⟩
theorem decode_7409 : decode runtimeBytecode ⟨7409⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨82, by decide⟩
theorem decode_7412 : decode runtimeBytecode ⟨7412⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨83, by decide⟩
theorem decode_7413 : decode runtimeBytecode ⟨7413⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨84, by decide⟩
theorem decode_7414 : decode runtimeBytecode ⟨7414⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨85, by decide⟩
theorem decode_7415 : decode runtimeBytecode ⟨7415⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨86, by decide⟩
theorem decode_7416 : decode runtimeBytecode ⟨7416⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨87, by decide⟩
theorem decode_7417 : decode runtimeBytecode ⟨7417⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨88, by decide⟩
theorem decode_7419 : decode runtimeBytecode ⟨7419⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨89, by decide⟩
theorem decode_7420 : decode runtimeBytecode ⟨7420⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨90, by decide⟩
theorem decode_7423 : decode runtimeBytecode ⟨7423⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨91, by decide⟩
theorem decode_7424 : decode runtimeBytecode ⟨7424⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨92, by decide⟩
theorem decode_7425 : decode runtimeBytecode ⟨7425⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨93, by decide⟩
theorem decode_7426 : decode runtimeBytecode ⟨7426⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨94, by decide⟩
theorem decode_7427 : decode runtimeBytecode ⟨7427⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨95, by decide⟩
theorem decode_7428 : decode runtimeBytecode ⟨7428⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨96, by decide⟩
theorem decode_7430 : decode runtimeBytecode ⟨7430⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨97, by decide⟩
theorem decode_7431 : decode runtimeBytecode ⟨7431⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨7334⟩, 2)) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨98, by decide⟩
theorem decode_7434 : decode runtimeBytecode ⟨7434⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes53] using generatedDecodes53_correct ⟨99, by decide⟩

end Ripemd160Old
