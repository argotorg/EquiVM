import Examples.Ripemd160Old.DecodeEntry

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def allocatorDecodes0 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨15⟩, some (.JUMPDEST, none)), (⟨16⟩, some (.PUSH1, some (⟨64⟩, 1))),
  (⟨18⟩, some (.MLOAD, none)), (⟨19⟩, some (.SWAP1, none)),
  (⟨20⟩, some (.JUMP, none)), (⟨29⟩, some (.JUMPDEST, none)),
  (⟨30⟩, some (.PUSH1, some (⟨31⟩, 1))), (⟨32⟩, some (.DUP1, none)),
  (⟨33⟩, some (.NOT, none)), (⟨34⟩, some (.SWAP2, none)),
  (⟨35⟩, some (.ADD, none)), (⟨36⟩, some (.AND, none)),
  (⟨37⟩, some (.SWAP1, none)), (⟨38⟩, some (.JUMP, none)),
  (⟨59⟩, some (.JUMPDEST, none)), (⟨60⟩, some (.SWAP1, none)),
  (⟨61⟩, some (.PUSH2, some (⟨69⟩, 2))), (⟨64⟩, some (.SWAP1, none)),
  (⟨65⟩, some (.PUSH2, some (⟨29⟩, 2))), (⟨68⟩, some (.JUMP, none)),
  (⟨69⟩, some (.JUMPDEST, none)), (⟨70⟩, some (.DUP2, none)),
  (⟨71⟩, some (.ADD, none)), (⟨72⟩, some (.SWAP1, none)),
  (⟨73⟩, some (.DUP2, none)), (⟨74⟩, some (.LT, none)),
  (⟨75⟩, some (.PUSH8, some (⟨18446744073709551615⟩, 8))),
  (⟨84⟩, some (.DUP3, none)), (⟨85⟩, some (.GT, none)),
  (⟨86⟩, some (.OR, none)), (⟨87⟩, some (.PUSH2, some (⟨95⟩, 2)))
]

private theorem allocatorDecodes0_correct : ∀ i : Fin allocatorDecodes0.size,
    decode runtimeBytecode allocatorDecodes0[i].1 = allocatorDecodes0[i].2 := by
  native_decide

macro "allocator_decode0" name:ident " at " pc:term " is " rhs:term " index " idx:num : command =>
  `(theorem $name : decode runtimeBytecode $pc = $rhs := by
      simpa [allocatorDecodes0] using allocatorDecodes0_correct ⟨$idx, by decide⟩)

allocator_decode0 decode_15 at ⟨15⟩ is some (.JUMPDEST, none) index 0
allocator_decode0 decode_16 at ⟨16⟩ is some (.PUSH1, some (⟨64⟩, 1)) index 1
allocator_decode0 decode_18 at ⟨18⟩ is some (.MLOAD, none) index 2
allocator_decode0 decode_19 at ⟨19⟩ is some (.SWAP1, none) index 3
allocator_decode0 decode_20 at ⟨20⟩ is some (.JUMP, none) index 4
allocator_decode0 decode_29 at ⟨29⟩ is some (.JUMPDEST, none) index 5
allocator_decode0 decode_30 at ⟨30⟩ is some (.PUSH1, some (⟨31⟩, 1)) index 6
allocator_decode0 decode_32 at ⟨32⟩ is some (.DUP1, none) index 7
allocator_decode0 decode_33 at ⟨33⟩ is some (.NOT, none) index 8
allocator_decode0 decode_34 at ⟨34⟩ is some (.SWAP2, none) index 9
allocator_decode0 decode_35 at ⟨35⟩ is some (.ADD, none) index 10
allocator_decode0 decode_36 at ⟨36⟩ is some (.AND, none) index 11
allocator_decode0 decode_37 at ⟨37⟩ is some (.SWAP1, none) index 12
allocator_decode0 decode_38 at ⟨38⟩ is some (.JUMP, none) index 13
allocator_decode0 decode_59 at ⟨59⟩ is some (.JUMPDEST, none) index 14
allocator_decode0 decode_60 at ⟨60⟩ is some (.SWAP1, none) index 15
allocator_decode0 decode_61 at ⟨61⟩ is some (.PUSH2, some (⟨69⟩, 2)) index 16
allocator_decode0 decode_64 at ⟨64⟩ is some (.SWAP1, none) index 17
allocator_decode0 decode_65 at ⟨65⟩ is some (.PUSH2, some (⟨29⟩, 2)) index 18
allocator_decode0 decode_68 at ⟨68⟩ is some (.JUMP, none) index 19
allocator_decode0 decode_69 at ⟨69⟩ is some (.JUMPDEST, none) index 20
allocator_decode0 decode_70 at ⟨70⟩ is some (.DUP2, none) index 21
allocator_decode0 decode_71 at ⟨71⟩ is some (.ADD, none) index 22
allocator_decode0 decode_72 at ⟨72⟩ is some (.SWAP1, none) index 23
allocator_decode0 decode_73 at ⟨73⟩ is some (.DUP2, none) index 24
allocator_decode0 decode_74 at ⟨74⟩ is some (.LT, none) index 25
allocator_decode0 decode_75 at ⟨75⟩ is some (.PUSH8, some (⟨18446744073709551615⟩, 8)) index 26
allocator_decode0 decode_84 at ⟨84⟩ is some (.DUP3, none) index 27
allocator_decode0 decode_85 at ⟨85⟩ is some (.GT, none) index 28
allocator_decode0 decode_86 at ⟨86⟩ is some (.OR, none) index 29
allocator_decode0 decode_87 at ⟨87⟩ is some (.PUSH2, some (⟨95⟩, 2)) index 30

end Ripemd160Old
