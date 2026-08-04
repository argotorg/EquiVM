import Examples.Ripemd160Old.DecodeAllocator2
import Examples.Ripemd160Old.JumpEntry

open Ethereum Ethereum.EVM

namespace Ripemd160Old

private def allocatorJumpTargets : Array UInt256 :=
  #[⟨15⟩, ⟨29⟩, ⟨59⟩, ⟨69⟩, ⟨100⟩, ⟨112⟩,
    ⟨119⟩, ⟨147⟩, ⟨156⟩, ⟨183⟩, ⟨188⟩]

private theorem allocatorJumpTargets_valid : ∀ i : Fin allocatorJumpTargets.size,
    (D_J runtimeBytecode 0).contains allocatorJumpTargets[i] = true := by
  rw [runtimeValidJumps]
  native_decide

macro "allocator_jump" name:ident " at " pc:term " index " idx:num : command =>
  `(theorem $name : (D_J runtimeBytecode 0).contains $pc = true := by
      simpa [allocatorJumpTargets] using allocatorJumpTargets_valid ⟨$idx, by decide⟩)

allocator_jump jump_15 at ⟨15⟩ index 0
allocator_jump jump_29 at ⟨29⟩ index 1
allocator_jump jump_59 at ⟨59⟩ index 2
allocator_jump jump_69 at ⟨69⟩ index 3
allocator_jump jump_100 at ⟨100⟩ index 4
allocator_jump jump_112 at ⟨112⟩ index 5
allocator_jump jump_119 at ⟨119⟩ index 6
allocator_jump jump_147 at ⟨147⟩ index 7
allocator_jump jump_156 at ⟨156⟩ index 8
allocator_jump jump_183 at ⟨183⟩ index 9
allocator_jump jump_188 at ⟨188⟩ index 10

end Ripemd160Old
