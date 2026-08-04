import Examples.Ripemd160Old.DecodeAllocator1

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def allocatorDecodes2 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨156⟩, some (.JUMPDEST, none)), (⟨183⟩, some (.JUMPDEST, none)),
  (⟨184⟩, some (.PUSH2, some (⟨100⟩, 2))), (⟨187⟩, some (.JUMP, none)),
  (⟨188⟩, some (.JUMPDEST, none)), (⟨189⟩, some (.SWAP4, none)),
  (⟨190⟩, some (.DUP2, none)), (⟨191⟩, some (.DUP6, none)),
  (⟨192⟩, some (.MSTORE, none)), (⟨193⟩, some (.PUSH1, some (⟨32⟩, 1))),
  (⟨195⟩, some (.DUP6, none)), (⟨196⟩, some (.ADD, none)),
  (⟨197⟩, some (.SWAP1, none)), (⟨198⟩, some (.DUP3, none)),
  (⟨199⟩, some (.DUP5, none)), (⟨200⟩, some (.ADD, none)),
  (⟨201⟩, some (.GT, none)), (⟨202⟩, some (.PUSH2, some (⟨216⟩, 2))),
  (⟨205⟩, some (.JUMPI, none)), (⟨206⟩, some (.PUSH2, some (⟨214⟩, 2))),
  (⟨209⟩, some (.SWAP3, none)), (⟨210⟩, some (.PUSH2, some (⟨156⟩, 2))),
  (⟨213⟩, some (.JUMP, none))
]

private theorem allocatorDecodes2_correct : ∀ i : Fin allocatorDecodes2.size,
    decode runtimeBytecode allocatorDecodes2[i].1 = allocatorDecodes2[i].2 := by
  native_decide

macro "allocator_decode2" name:ident " at " pc:term " is " rhs:term " index " idx:num : command =>
  `(theorem $name : decode runtimeBytecode $pc = $rhs := by
      simpa [allocatorDecodes2] using allocatorDecodes2_correct ⟨$idx, by decide⟩)

allocator_decode2 decode_156 at ⟨156⟩ is some (.JUMPDEST, none) index 0
allocator_decode2 decode_183 at ⟨183⟩ is some (.JUMPDEST, none) index 1
allocator_decode2 decode_184 at ⟨184⟩ is some (.PUSH2, some (⟨100⟩, 2)) index 2
allocator_decode2 decode_187 at ⟨187⟩ is some (.JUMP, none) index 3
allocator_decode2 decode_188 at ⟨188⟩ is some (.JUMPDEST, none) index 4
allocator_decode2 decode_189 at ⟨189⟩ is some (.SWAP4, none) index 5
allocator_decode2 decode_190 at ⟨190⟩ is some (.DUP2, none) index 6
allocator_decode2 decode_191 at ⟨191⟩ is some (.DUP6, none) index 7
allocator_decode2 decode_192 at ⟨192⟩ is some (.MSTORE, none) index 8
allocator_decode2 decode_193 at ⟨193⟩ is some (.PUSH1, some (⟨32⟩, 1)) index 9
allocator_decode2 decode_195 at ⟨195⟩ is some (.DUP6, none) index 10
allocator_decode2 decode_196 at ⟨196⟩ is some (.ADD, none) index 11
allocator_decode2 decode_197 at ⟨197⟩ is some (.SWAP1, none) index 12
allocator_decode2 decode_198 at ⟨198⟩ is some (.DUP3, none) index 13
allocator_decode2 decode_199 at ⟨199⟩ is some (.DUP5, none) index 14
allocator_decode2 decode_200 at ⟨200⟩ is some (.ADD, none) index 15
allocator_decode2 decode_201 at ⟨201⟩ is some (.GT, none) index 16
allocator_decode2 decode_202 at ⟨202⟩ is some (.PUSH2, some (⟨216⟩, 2)) index 17
allocator_decode2 decode_205 at ⟨205⟩ is some (.JUMPI, none) index 18
allocator_decode2 decode_206 at ⟨206⟩ is some (.PUSH2, some (⟨214⟩, 2)) index 19
allocator_decode2 decode_209 at ⟨209⟩ is some (.SWAP3, none) index 20
allocator_decode2 decode_210 at ⟨210⟩ is some (.PUSH2, some (⟨156⟩, 2)) index 21
allocator_decode2 decode_213 at ⟨213⟩ is some (.JUMP, none) index 22

end Ripemd160Old
