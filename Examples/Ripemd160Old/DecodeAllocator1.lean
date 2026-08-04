import Examples.Ripemd160Old.DecodeAllocator0

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def allocatorDecodes1 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨90⟩, some (.JUMPI, none)), (⟨91⟩, some (.PUSH1, some (⟨64⟩, 1))),
  (⟨93⟩, some (.MSTORE, none)), (⟨94⟩, some (.JUMP, none)),
  (⟨100⟩, some (.JUMPDEST, none)), (⟨101⟩, some (.SWAP1, none)),
  (⟨102⟩, some (.PUSH2, some (⟨119⟩, 2))),
  (⟨105⟩, some (.PUSH2, some (⟨112⟩, 2))),
  (⟨108⟩, some (.PUSH2, some (⟨15⟩, 2))), (⟨111⟩, some (.JUMP, none)),
  (⟨112⟩, some (.JUMPDEST, none)), (⟨113⟩, some (.SWAP3, none)),
  (⟨114⟩, some (.DUP4, none)), (⟨115⟩, some (.PUSH2, some (⟨59⟩, 2))),
  (⟨118⟩, some (.JUMP, none)), (⟨119⟩, some (.JUMPDEST, none)),
  (⟨120⟩, some (.JUMP, none)),
  (⟨122⟩, some (.PUSH8, some (⟨18446744073709551615⟩, 8))),
  (⟨131⟩, some (.DUP2, none)), (⟨132⟩, some (.GT, none)),
  (⟨133⟩, some (.PUSH2, some (⟨151⟩, 2))), (⟨136⟩, some (.JUMPI, none)),
  (⟨137⟩, some (.PUSH2, some (⟨147⟩, 2))),
  (⟨140⟩, some (.PUSH1, some (⟨32⟩, 1))), (⟨142⟩, some (.SWAP2, none)),
  (⟨143⟩, some (.PUSH2, some (⟨29⟩, 2))), (⟨146⟩, some (.JUMP, none)),
  (⟨147⟩, some (.JUMPDEST, none)), (⟨148⟩, some (.ADD, none)),
  (⟨149⟩, some (.SWAP1, none)), (⟨150⟩, some (.JUMP, none))
]

private theorem allocatorDecodes1_correct : ∀ i : Fin allocatorDecodes1.size,
    decode runtimeBytecode allocatorDecodes1[i].1 = allocatorDecodes1[i].2 := by
  native_decide

macro "allocator_decode1" name:ident " at " pc:term " is " rhs:term " index " idx:num : command =>
  `(theorem $name : decode runtimeBytecode $pc = $rhs := by
      simpa [allocatorDecodes1] using allocatorDecodes1_correct ⟨$idx, by decide⟩)

allocator_decode1 decode_90 at ⟨90⟩ is some (.JUMPI, none) index 0
allocator_decode1 decode_91 at ⟨91⟩ is some (.PUSH1, some (⟨64⟩, 1)) index 1
allocator_decode1 decode_93 at ⟨93⟩ is some (.MSTORE, none) index 2
allocator_decode1 decode_94 at ⟨94⟩ is some (.JUMP, none) index 3
allocator_decode1 decode_100 at ⟨100⟩ is some (.JUMPDEST, none) index 4
allocator_decode1 decode_101 at ⟨101⟩ is some (.SWAP1, none) index 5
allocator_decode1 decode_102 at ⟨102⟩ is some (.PUSH2, some (⟨119⟩, 2)) index 6
allocator_decode1 decode_105 at ⟨105⟩ is some (.PUSH2, some (⟨112⟩, 2)) index 7
allocator_decode1 decode_108 at ⟨108⟩ is some (.PUSH2, some (⟨15⟩, 2)) index 8
allocator_decode1 decode_111 at ⟨111⟩ is some (.JUMP, none) index 9
allocator_decode1 decode_112 at ⟨112⟩ is some (.JUMPDEST, none) index 10
allocator_decode1 decode_113 at ⟨113⟩ is some (.SWAP3, none) index 11
allocator_decode1 decode_114 at ⟨114⟩ is some (.DUP4, none) index 12
allocator_decode1 decode_115 at ⟨115⟩ is some (.PUSH2, some (⟨59⟩, 2)) index 13
allocator_decode1 decode_118 at ⟨118⟩ is some (.JUMP, none) index 14
allocator_decode1 decode_119 at ⟨119⟩ is some (.JUMPDEST, none) index 15
allocator_decode1 decode_120 at ⟨120⟩ is some (.JUMP, none) index 16
allocator_decode1 decode_122 at ⟨122⟩ is some (.PUSH8, some (⟨18446744073709551615⟩, 8)) index 17
allocator_decode1 decode_131 at ⟨131⟩ is some (.DUP2, none) index 18
allocator_decode1 decode_132 at ⟨132⟩ is some (.GT, none) index 19
allocator_decode1 decode_133 at ⟨133⟩ is some (.PUSH2, some (⟨151⟩, 2)) index 20
allocator_decode1 decode_136 at ⟨136⟩ is some (.JUMPI, none) index 21
allocator_decode1 decode_137 at ⟨137⟩ is some (.PUSH2, some (⟨147⟩, 2)) index 22
allocator_decode1 decode_140 at ⟨140⟩ is some (.PUSH1, some (⟨32⟩, 1)) index 23
allocator_decode1 decode_142 at ⟨142⟩ is some (.SWAP2, none) index 24
allocator_decode1 decode_143 at ⟨143⟩ is some (.PUSH2, some (⟨29⟩, 2)) index 25
allocator_decode1 decode_146 at ⟨146⟩ is some (.JUMP, none) index 26
allocator_decode1 decode_147 at ⟨147⟩ is some (.JUMPDEST, none) index 27
allocator_decode1 decode_148 at ⟨148⟩ is some (.ADD, none) index 28
allocator_decode1 decode_149 at ⟨149⟩ is some (.SWAP1, none) index 29
allocator_decode1 decode_150 at ⟨150⟩ is some (.JUMP, none) index 30

end Ripemd160Old
