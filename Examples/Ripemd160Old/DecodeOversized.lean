import Examples.Ripemd160Old.Bytecode

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def oversizedDecodes :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨39⟩, some (.JUMPDEST, none)),
  (⟨40⟩, some (.PUSH4, some (⟨1313373041⟩, 4))),
  (⟨45⟩, some (.PUSH1, some (⟨224⟩, 1))),
  (⟨47⟩, some (.SHL, none)),
  (⟨48⟩, some (.PUSH0, none)),
  (⟨49⟩, some (.MSTORE, none)),
  (⟨50⟩, some (.PUSH1, some (⟨65⟩, 1))),
  (⟨52⟩, some (.PUSH1, some (⟨4⟩, 1))),
  (⟨54⟩, some (.MSTORE, none)),
  (⟨55⟩, some (.PUSH1, some (⟨36⟩, 1))),
  (⟨57⟩, some (.PUSH0, none)),
  (⟨58⟩, some (.REVERT, none)),
  (⟨95⟩, some (.JUMPDEST, none)),
  (⟨96⟩, some (.PUSH2, some (⟨39⟩, 2))),
  (⟨99⟩, some (.JUMP, none)),
  (⟨151⟩, some (.JUMPDEST, none)),
  (⟨152⟩, some (.PUSH2, some (⟨39⟩, 2))),
  (⟨155⟩, some (.JUMP, none))
]

private theorem oversizedDecodes_correct : ∀ i : Fin oversizedDecodes.size,
    decode runtimeBytecode oversizedDecodes[i].1 = oversizedDecodes[i].2 := by
  native_decide

macro "oversized_decode" name:ident " at " pc:term " is " rhs:term " index " idx:num : command =>
  `(theorem $name : decode runtimeBytecode $pc = $rhs := by
      simpa [oversizedDecodes] using oversizedDecodes_correct ⟨$idx, by decide⟩)

oversized_decode decode_39 at ⟨39⟩ is some (.JUMPDEST, none) index 0
oversized_decode decode_40 at ⟨40⟩ is some (.PUSH4, some (⟨1313373041⟩, 4)) index 1
oversized_decode decode_45 at ⟨45⟩ is some (.PUSH1, some (⟨224⟩, 1)) index 2
oversized_decode decode_47 at ⟨47⟩ is some (.SHL, none) index 3
oversized_decode decode_48 at ⟨48⟩ is some (.PUSH0, none) index 4
oversized_decode decode_49 at ⟨49⟩ is some (.MSTORE, none) index 5
oversized_decode decode_50 at ⟨50⟩ is some (.PUSH1, some (⟨65⟩, 1)) index 6
oversized_decode decode_52 at ⟨52⟩ is some (.PUSH1, some (⟨4⟩, 1)) index 7
oversized_decode decode_54 at ⟨54⟩ is some (.MSTORE, none) index 8
oversized_decode decode_55 at ⟨55⟩ is some (.PUSH1, some (⟨36⟩, 1)) index 9
oversized_decode decode_57 at ⟨57⟩ is some (.PUSH0, none) index 10
oversized_decode decode_58 at ⟨58⟩ is some (.REVERT, none) index 11
oversized_decode decode_95 at ⟨95⟩ is some (.JUMPDEST, none) index 12
oversized_decode decode_96 at ⟨96⟩ is some (.PUSH2, some (⟨39⟩, 2)) index 13
oversized_decode decode_99 at ⟨99⟩ is some (.JUMP, none) index 14
oversized_decode decode_151 at ⟨151⟩ is some (.JUMPDEST, none) index 15
oversized_decode decode_152 at ⟨152⟩ is some (.PUSH2, some (⟨39⟩, 2)) index 16
oversized_decode decode_155 at ⟨155⟩ is some (.JUMP, none) index 17

private def oversizedJumpTargets : Array UInt256 := #[⟨39⟩, ⟨95⟩, ⟨151⟩]

private theorem oversizedJumpTargets_valid : ∀ i : Fin oversizedJumpTargets.size,
    (D_J runtimeBytecode 0).contains oversizedJumpTargets[i] = true := by
  rw [runtimeValidJumps]
  native_decide

theorem jump_39 : (D_J runtimeBytecode 0).contains ⟨39⟩ = true := by
  simpa [oversizedJumpTargets] using oversizedJumpTargets_valid ⟨0, by decide⟩

theorem jump_95 : (D_J runtimeBytecode 0).contains ⟨95⟩ = true := by
  simpa [oversizedJumpTargets] using oversizedJumpTargets_valid ⟨1, by decide⟩

theorem jump_151 : (D_J runtimeBytecode 0).contains ⟨151⟩ = true := by
  simpa [oversizedJumpTargets] using oversizedJumpTargets_valid ⟨2, by decide⟩

end Ripemd160Old
