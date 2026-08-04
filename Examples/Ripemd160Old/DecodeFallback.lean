import Examples.Ripemd160Old.JumpAllocator

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def fallbackDecodes :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨157⟩, some (.SWAP1, none)), (⟨158⟩, some (.DUP3, none)),
  (⟨159⟩, some (.PUSH0, none)), (⟨160⟩, some (.SWAP4, none)),
  (⟨161⟩, some (.SWAP3, none)), (⟨162⟩, some (.DUP3, none)),
  (⟨163⟩, some (.CALLDATACOPY, none)), (⟨164⟩, some (.ADD, none)),
  (⟨165⟩, some (.MSTORE, none)), (⟨166⟩, some (.JUMP, none)),
  (⟨214⟩, some (.JUMPDEST, none)), (⟨215⟩, some (.JUMP, none)),
  (⟨232⟩, some (.JUMPDEST, none)), (⟨233⟩, some (.SWAP1, none)),
  (⟨234⟩, some (.JUMP, none)), (⟨249⟩, some (.JUMPDEST, none)),
  (⟨250⟩, some (.PUSH2, some (⟨8306⟩, 2))), (⟨253⟩, some (.JUMP, none)),
  (⟨8306⟩, some (.JUMPDEST, none))
]

private theorem fallbackDecodes_correct : ∀ i : Fin fallbackDecodes.size,
    decode runtimeBytecode fallbackDecodes[i].1 = fallbackDecodes[i].2 := by
  native_decide

macro "fallback_decode" name:ident " at " pc:term " is " rhs:term " index " idx:num : command =>
  `(theorem $name : decode runtimeBytecode $pc = $rhs := by
      simpa [fallbackDecodes] using fallbackDecodes_correct ⟨$idx, by decide⟩)

fallback_decode decode_157 at ⟨157⟩ is some (.SWAP1, none) index 0
fallback_decode decode_158 at ⟨158⟩ is some (.DUP3, none) index 1
fallback_decode decode_159 at ⟨159⟩ is some (.PUSH0, none) index 2
fallback_decode decode_160 at ⟨160⟩ is some (.SWAP4, none) index 3
fallback_decode decode_161 at ⟨161⟩ is some (.SWAP3, none) index 4
fallback_decode decode_162 at ⟨162⟩ is some (.DUP3, none) index 5
fallback_decode decode_163 at ⟨163⟩ is some (.CALLDATACOPY, none) index 6
fallback_decode decode_164 at ⟨164⟩ is some (.ADD, none) index 7
fallback_decode decode_165 at ⟨165⟩ is some (.MSTORE, none) index 8
fallback_decode decode_166 at ⟨166⟩ is some (.JUMP, none) index 9
fallback_decode decode_214 at ⟨214⟩ is some (.JUMPDEST, none) index 10
fallback_decode decode_215 at ⟨215⟩ is some (.JUMP, none) index 11
fallback_decode decode_232 at ⟨232⟩ is some (.JUMPDEST, none) index 12
fallback_decode decode_233 at ⟨233⟩ is some (.SWAP1, none) index 13
fallback_decode decode_234 at ⟨234⟩ is some (.JUMP, none) index 14
fallback_decode decode_249 at ⟨249⟩ is some (.JUMPDEST, none) index 15
fallback_decode decode_250 at ⟨250⟩ is some (.PUSH2, some (⟨8306⟩, 2)) index 16
fallback_decode decode_253 at ⟨253⟩ is some (.JUMP, none) index 17
fallback_decode decode_8306 at ⟨8306⟩ is some (.JUMPDEST, none) index 18

end Ripemd160Old
