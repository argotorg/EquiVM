import Benchmarks.WETH9.StringReturnLong2

/-!
# WETH9 `symbol()` dynamic-string getter — EVM-side return lemmas (slot 1)

`symbol()` is the exact twin of `name()`: it reads the Solidity compact dynamic string from storage
**slot 1** (`name` reads slot 0) and ABI-returns it.  Symbol dispatches through its own non-payable
guard (pc 623) into a **symbol-specific** string-load routine at pc 1571, which — apart from reading
slot 1 and a different `DUP` schedule for the `header & 1` short-flag test — is byte-identical to
`name`'s routine at pc 839.  Crucially it pushes the **same** return address `0xbb = 187`, so it
shares `name`'s entire ABI-string return encoder (pc 187 → `RETURN`) and its empty/short/long
dispatch (pc 930/973) verbatim.

This module re-derives the symbol routine-reach (`weth9SymbolRoutineReach1628`, the analog of
`weth9NameRoutineReach897`) and proves the three symbol return lemmas mirroring
`weth9NameString*Returns`, reusing every header/slot-parametric shape/arith/byte definition and the
shared short encoder `weth9NameShortEncoder`.

The one genuinely new wrinkle: symbol computes `header & 1` as `DUP5; DUP7; AND` (producing
`land ⟨1⟩ header`) where `name` used `PUSH1 1; DUP6; AND` (producing `land header ⟨1⟩`).  We reconcile
the reversed operands with `u256_land_comm` right after the `AND`, after which every downstream
definition (`weth9StringMask`/`Len`/`WC`/`NewFp`, `weth9RoutineMem`, …) matches `name`'s.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-! ## Reach the symbol string-load routine (pc 1571)

`symbol()` enters at pc 623; the non-payable guard (gt = 635) peels to pc 637, whose
`PUSH2 187; PUSH2 1571; JUMP` lands at the routine (pc 1571) with `[187, sel]` — the exact analog of
`weth9ReachName839`. -/

theorem weth9ReachSymbol1571 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1571⟩
      [⟨187⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h623⟩ := weth9ReachSymbol (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h637⟩ := weth9GuardPeelOk (gt := ⟨635⟩) h623 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
  have h1571 := h637.push2 ⟨187⟩ (by decide +native) (by simp)
    |>.push2 ⟨1571⟩ (by decide +native) (by simp)
    |>.jump (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, h1571⟩

/-! ## Symbol string-load routine prefix (pc 1571 → 1628)

The analog of `weth9NameRoutineReach897`.  Decodes the compact header of slot 1, allocates the
`[len ; data]` object (bumped free pointer at `0x40`, length at `0x80`), and reaches pc 1628 (the
`DUP1` before the empty/short/long dispatch).  Slot 1's value flows into the two carried stack slots
(`⟨1⟩` where `name` carried `⟨0⟩`).  The `header & 1` short-flag test uses `DUP5; DUP7; AND`, so we
convert `land ⟨1⟩ header → land header ⟨1⟩` via `u256_land_comm` to match `name`'s shape. -/

set_option maxHeartbeats 8000000 in
theorem weth9SymbolRoutineReach1628 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1628⟩
      [weth9StringLen (weth9StringSlotWord σ I ⟨1⟩), ⟨1⟩, ⟨160⟩,
       weth9StringLen (weth9StringSlotWord σ I ⟨1⟩), ⟨1⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9RoutineMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1571⟩ := weth9ReachSymbol1571 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  obtain ⟨_, _, h1576raw⟩ := (evm_run h1571 with [jumpdest, push1 ⟨1⟩, dup1]).sload
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, h1576⟩ : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1576⟩
      [weth9StringSlotWord σ I ⟨1⟩, ⟨1⟩, ⟨187⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [weth9StringSlotWord, initState] using h1576raw⟩
  have hAnd := evm_run h1576 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨2⟩, dup5, dup7, and]
  rw [u256_land_comm ⟨1⟩ (weth9StringSlotWord σ I ⟨1⟩)] at hAnd
  have h886 := evm_run hAnd with [
    iszero, push2 ⟨256⟩, mul,
    push1 ⟨0⟩, not, add, swap1, swap5, and, swap4, swap1, swap4, div,
    push1 ⟨31⟩, dup2, add, dup5, swap1, div, dup5, mul, dup3, add, dup5, add, swap1, swap3]
  have h1628 := evm_run h886 with [
    raw mstore 0 ((UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩))).write 0
        solcFreePtrMem (⟨64⟩ : UInt256).toNat 32) (UInt256.ofNat 3)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    dup2, dup2,
    raw mstore 6 (weth9RoutineMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 5)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    swap3, swap2, dup4, add, dup3, dup3]
  exact ⟨_, _, h1628⟩

/-! ## Empty-string case (`len = 0`) — GOAL 1 -/

set_option maxHeartbeats 8000000 in
theorem weth9SymbolStringEmptyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hlen0 : weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) = ⟨0⟩) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) weth9EmptyStringAbi := by
  obtain ⟨_, _, h1628⟩ := weth9SymbolRoutineReach1628 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  rw [hlen0, weth9RoutineMem_zero hlen0] at h1628
  have h187 := evm_run h1628 with [
    dup1, iszero, push2 ⟨973⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, dup2, jump (by jump_dest)]
  have h196 := evm_run h187 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 _ (UInt256.ofNat 6) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov)]
  have h221 := evm_run h196 with [
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 _ (UInt256.ofNat 7) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have hret := evm_run h221 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨290⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run hret with [
    raw ret 0 weth9EmptyStringAbi (by decide +native) mem_cost (by decide +native) (by evm_ov)]

/-! ## Short-string load routine (pc 1628 → encoder entry 187)

Byte-identical to `weth9NameShortLoadReach187`: from the dispatch checkpoint the short branch reads
the inline word (via `DUP4` grabbing slot 1, then `SLOAD`), stores the `[len ; data]` object, and
jumps back through the shared `973` bookkeeping to the encoder entry 187. -/

set_option maxHeartbeats 8000000 in
theorem weth9SymbolShortLoadReach187 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hne : weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) = ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9ShortObjMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1628⟩ := weth9SymbolRoutineReach1628 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  rw [weth9RoutineMem_short hne hlt31] at h1628
  have h915 := evm_run h1628 with [
    dup1, iszero, push2 ⟨973⟩, jumpiNT (isZero_eq_zero_of_ne hne),
    dup1, push1 ⟨31⟩, lt, push2 ⟨930⟩, jumpiNT hlt31,
    push2 ⟨256⟩, dup1, dup4]
  obtain ⟨_, _, h916⟩ := h915.sload (by decide +native) (by evm_ov)
  have h187 := evm_run h916 with [
    div, mul, dup4,
    raw mstore 3 (weth9ShortObjMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 6)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    swap2, push1 ⟨32⟩, add, swap2, push2 ⟨973⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, dup2, jump (by jump_dest)]
  exact ⟨_, _, h187⟩

/-! ## Short-string case (`0 < len < 32`) — GOAL 2

Reuses `name`'s shared short ABI return encoder `weth9NameShortEncoder` (parametric in the header)
with `H := weth9StringSlotWord σ I ⟨1⟩`. -/

theorem weth9SymbolStringShortReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hne : weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) = ⟨0⟩) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (weth9ShortStringAbi (weth9StringSlotWord σ I ⟨1⟩)) := by
  obtain ⟨_, _, h187⟩ := weth9SymbolShortLoadReach187 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hne hlt31
  exact weth9NameShortEncoder (weth9StringSlotWord σ I ⟨1⟩) hne hlt31 h187

/-! ## LONG case (`len ≥ 32`) — storage→memory copy loop setup (slot 1)

For a long string the routine hashes the base **slot 1** to find the data region and runs the shared
storage→memory copy loop (pc 944–963).  All the loop stepping/schedule machinery
(`weth9NameLongCopyContinue`/`Exit`/`Schedule`, `Weth9LongLoopState`/`Step`/`Final`,
`weth9LongLoopMstoreCost`) is header/slot-agnostic and reused verbatim; only the base slot
(`keccak(bytes32 1)` vs `keccak(bytes32 0)`) and the scratch-memory slot word (`⟨1⟩` vs `⟨0⟩`) are
symbol-specific. -/

/-- keccak(slot 1): the base storage slot of symbol's long-string data words. -/
def weth9SymLongDataBase : UInt256 := solidityBytesDataBaseSlot ⟨1⟩

/-- Scratch memory at the copy-loop entry: routine memory with the base slot (`1`) at `mem[0]`. -/
noncomputable def weth9SymLongScratchMem (header : UInt256) : ByteArray :=
  writeWord (weth9RoutineMem header) 0 ⟨1⟩

theorem weth9SymLongScratchMem_read0 (H : UInt256) :
    (weth9SymLongScratchMem H).readWithPadding 0 32 = UInt256.toByteArray ⟨1⟩ := by
  rw [weth9SymLongScratchMem]
  exact writeWord_read_back _ 0 _ (by exact lt_usize _ (by norm_num))

/-- The `KECCAK256(0, 32)` at the loop setup yields the data base slot `keccak(slot 1)`. -/
theorem weth9SymLongScratchMem_keccak1 (H : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((weth9SymLongScratchMem H).readWithPadding 0 32))) = weth9SymLongDataBase := by
  rw [weth9SymLongScratchMem_read0, weth9SymLongDataBase, solidityBytesDataBaseSlot,
    uInt256OfByteArray_eq]

set_option maxHeartbeats 8000000 in
theorem weth9SymNameLongReachLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [⟨160⟩, weth9SymLongDataBase, weth9LongEnd (weth9StringSlotWord σ I ⟨1⟩),
       weth9StringLen (weth9StringSlotWord σ I ⟨1⟩), ⟨1⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9SymLongScratchMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1628⟩ := weth9SymbolRoutineReach1628 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  have h910 := evm_run h1628 with [
    dup1, iszero, push2 ⟨973⟩, jumpiNT (isZero_eq_zero_of_ne (weth9LongLen_ne hge31)),
    dup1, push1 ⟨31⟩, lt, push2 ⟨930⟩, jumpiT hge31 (by jump_dest)]
  have h942 := evm_run h910 with [
    jumpdest, dup3, add, swap2, swap1, push1 ⟨0⟩,
    raw mstore 0 (weth9SymLongScratchMem (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat 5)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨0⟩]
  have h943 := h942.keccak256 0 weth9SymLongDataBase (UInt256.ofNat 5) (by decide +native)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        decide +native)
    (weth9SymLongScratchMem_keccak1 _) (by decide) (by evm_ov)
  exact ⟨_, _, evm_run h943 with [swap1]⟩

/-! ### Symbol copy-loop stepping machinery (slot marker `⟨1⟩`)

`name`'s copy-loop combinators (`Weth9LongLoopState.stack`, `weth9NameLongCopyContinue`/`Exit`,
`Weth9LongLoopStep`/`Final`, `weth9LongLoopMstoreCost`) all bake the storage-slot value `⟨0⟩` into the
carried stack slot (position 5 at pc 944, position 7 during the body `MSTORE`).  For `symbol` the
carried value is `⟨1⟩`, so we reproduce those combinators verbatim with the `⟨1⟩` marker.  The proofs
are byte-identical — the marker is dead (popped at exit) and never affects the `MSTORE` cost. -/

/-- The EVM stack at the symbol copy-loop head (pc 944): slot marker `⟨1⟩` at position 5. -/
def weth9SymLongLoopStack (s : Weth9LongLoopState) (endp len : UInt256) (I : ExecutionEnv) :
    List UInt256 :=
  [s.ptr, s.slot, endp, len, ⟨1⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]

/-- One copy-loop iteration (pc 944 → 944), continuing branch (slot marker `⟨1⟩`). -/
theorem weth9SymNameLongCopyContinue {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [ptr, slot, endp, len, ⟨1⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) ≠ ⟨0⟩)
    (hmemout : (weth9LongStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨1⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [(⟨32⟩ : UInt256) + ptr, (⟨1⟩ : UInt256) + slot, endp, len, ⟨1⟩,
        ⟨128⟩, ⟨187⟩, weth9SelWord I]
      memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd944⟩ := hreach
  have rd946 := evm_run rd944 with [jumpdest, dup2]
  obtain ⟨_, _, rd947₀⟩ := rd946.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd947⟩ : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨947⟩
      [weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨1⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] m aw ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [weth9LongStorageWord, initState] using rd947₀⟩
  have rd948 := evm_run rd947 with [dup2]
  have rd949 := rd948.mstore mstoreCost memout awStore (by decide +native) hmstoreCost hmemout
    hawStore (by evm_ov)
  have rd960 := evm_run rd949 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨944⟩]
  exact ⟨_, _, rd960.jumpiT (by decide +native) hcontinue (by jump_dest) (by evm_ov)⟩

/-- Copy-loop exit (pc 944 → 187), done branch (slot marker `⟨1⟩`). -/
theorem weth9SymNameLongCopyExit {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [ptr, slot, endp, len, ⟨1⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) = ⟨0⟩)
    (hmemout : (weth9LongStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨1⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd944⟩ := hreach
  have rd946 := evm_run rd944 with [jumpdest, dup2]
  obtain ⟨_, _, rd947₀⟩ := rd946.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd947⟩ : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨947⟩
      [weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨1⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] m aw ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [weth9LongStorageWord, initState] using rd947₀⟩
  have rd948 := evm_run rd947 with [dup2]
  have rd949 := rd948.mstore mstoreCost memout awStore (by decide +native) hmstoreCost hmemout
    hawStore (by evm_ov)
  have rd960 := evm_run rd949 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨944⟩]
  have rd963 := rd960.jumpiNT (by decide +native) hdone (by evm_ov)
  have rd980 := evm_run rd963 with [
    dup3, swap1, sub, push1 ⟨31⟩, and, dup3, add, swap2,
    jumpdest, pop, pop, pop, pop, pop, dup2]
  exact ⟨_, _, rd980.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

/-- Per-step data proving one symbol copy iteration advances the generated state (marker `⟨1⟩`). -/
structure Weth9SymLongLoopStep (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s t : Weth9LongLoopState) where
  mstoreCost : Nat
  hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) ≠ ⟨0⟩
  hmemout : (weth9LongStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = t.mem
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨1⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = t.aw
  hptrNext : t.ptr = (⟨32⟩ : UInt256) + s.ptr
  hslotNext : t.slot = (⟨1⟩ : UInt256) + s.slot

/-- Terminal data proving the loop exits and yields the finished memory (marker `⟨1⟩`). -/
structure Weth9SymLongLoopFinal (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : Weth9LongLoopState) where
  memout : ByteArray
  awStore : UInt256
  mstoreCost : Nat
  hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) = ⟨0⟩
  hmemout : (weth9LongStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = memout
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨1⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = awStore

/-- Fuel-induction assembly for the symbol copy loop (reaches encoder entry 187). -/
theorem weth9SymNameLongCopySchedule {cA gh bl σ σ₀ A I} {g : Sat256} {endp len : UInt256}
    (fuel : Nat) (st : Nat → Weth9LongLoopState)
    (hsteps : ∀ i, i < fuel → Weth9SymLongLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : Weth9SymLongLoopFinal σ I endp len (st fuel))
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      (weth9SymLongLoopStack (st 0) endp len I) (st 0).mem (st 0).aw ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] hfinal.memout hfinal.awStore ByteArray.empty (cA, σ) k C := by
  induction fuel generalizing st with
  | zero =>
      simpa [weth9SymLongLoopStack] using
        weth9SymNameLongCopyExit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp) (len := len)
          (aw := (st 0).aw) (m := (st 0).mem) (memout := hfinal.memout) (awStore := hfinal.awStore)
          (mstoreCost := hfinal.mstoreCost)
          hreach hfinal.hdone hfinal.hmemout hfinal.hmstoreCost hfinal.hawStore
  | succ fuel ih =>
      have hs : Weth9SymLongLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hnext₀ := weth9SymNameLongCopyContinue
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp) (len := len) (aw := (st 0).aw)
        (m := (st 0).mem) (memout := (st 1).mem) (awStore := (st 1).aw)
        (mstoreCost := hs.mstoreCost)
        hreach hs.hcontinue hs.hmemout hs.hmstoreCost hs.hawStore
      have hnext : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
          (weth9SymLongLoopStack ((fun i => st i.succ) 0) endp len I)
          ((fun i => st i.succ) 0).mem ((fun i => st i.succ) 0).aw ByteArray.empty (cA, σ) k C := by
        obtain ⟨k, C, rd⟩ := hnext₀
        exact ⟨k, C, by simpa [weth9SymLongLoopStack, hs.hptrNext, hs.hslotNext] using rd⟩
      have hsteps' : ∀ i, i < fuel →
          Weth9SymLongLoopStep σ I endp len ((fun j => st j.succ) i) ((fun j => st j.succ) (i + 1)) := by
        intro i hi
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hsteps i.succ (Nat.succ_lt_succ hi)
      exact ih (fun i => st i.succ) hsteps' hfinal hnext

/-- The (symbolic) `MSTORE` cost at symbol generated loop state `s` (marker `⟨1⟩`). -/
def weth9SymLongLoopMstoreCost (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : Weth9LongLoopState) : Nat :=
  memoryExpansionCost
    { (default : State) with
      machineState := { (default : State).machineState with
        activeWords := s.aw
        stack := [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨1⟩,
          ⟨128⟩, ⟨187⟩, weth9SelWord I] } }
    .MSTORE

theorem weth9SymLongLoopMstoreCost_spec {σ : AccountMap} {I : ExecutionEnv} {endp len : UInt256}
    {s : Weth9LongLoopState} :
    ∀ st : State, st.machineState.activeWords = s.aw →
      st.machineState.stack =
        [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨1⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost st .MSTORE = weth9SymLongLoopMstoreCost σ I endp len s := by
  intro st haw hstk
  rw [weth9SymLongLoopMstoreCost]
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw]

/-- The generated symbol copy-loop state after `n` iterations (base = keccak(slot 1)). -/
noncomputable def weth9SymLongGeneratedLoopState (σ : AccountMap) (I : ExecutionEnv) :
    Nat → Weth9LongLoopState
  | 0 =>
      { ptr := ⟨160⟩
        slot := weth9SymLongDataBase
        mem := weth9SymLongScratchMem (weth9StringSlotWord σ I ⟨1⟩)
        aw := UInt256.ofNat 5 }
  | n + 1 =>
      let s := weth9SymLongGeneratedLoopState σ I n
      { ptr := (⟨32⟩ : UInt256) + s.ptr
        slot := (⟨1⟩ : UInt256) + s.slot
        mem := weth9LongCopyMem s.mem s.ptr (weth9LongStorageWord σ I s.slot)
        aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) }

theorem weth9SymLongGeneratedLoopState_zero (σ : AccountMap) (I : ExecutionEnv) :
    weth9SymLongGeneratedLoopState σ I 0 =
      { ptr := ⟨160⟩, slot := weth9SymLongDataBase,
        mem := weth9SymLongScratchMem (weth9StringSlotWord σ I ⟨1⟩), aw := UInt256.ofNat 5 } := rfl

theorem weth9SymLongGeneratedLoopState_succ (σ : AccountMap) (I : ExecutionEnv) (n : Nat) :
    weth9SymLongGeneratedLoopState σ I (n + 1) =
      (let s := weth9SymLongGeneratedLoopState σ I n
       { ptr := (⟨32⟩ : UInt256) + s.ptr, slot := (⟨1⟩ : UInt256) + s.slot,
         mem := weth9LongCopyMem s.mem s.ptr (weth9LongStorageWord σ I s.slot),
         aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) }) := rfl

/-- One generated copy-loop step for symbol. -/
noncomputable def weth9SymLongGeneratedLoopStep {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {i : Nat}
    (hcontinue : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I i).ptr) ≠ ⟨0⟩) :
    Weth9SymLongLoopStep σ I endp len
      (weth9SymLongGeneratedLoopState σ I i) (weth9SymLongGeneratedLoopState σ I (i + 1)) :=
  { mstoreCost := weth9SymLongLoopMstoreCost σ I endp len (weth9SymLongGeneratedLoopState σ I i)
    hcontinue := hcontinue
    hmemout := by
      simp only [weth9SymLongGeneratedLoopState_succ, weth9LongCopyMem, Reasoning.Theory.writeWord]
    hmstoreCost := fun st haw hstk =>
      weth9SymLongLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp) (len := len)
        (s := weth9SymLongGeneratedLoopState σ I i) st haw hstk
    hawStore := by simp [weth9SymLongGeneratedLoopState_succ]
    hptrNext := by simp [weth9SymLongGeneratedLoopState_succ]
    hslotNext := by simp [weth9SymLongGeneratedLoopState_succ] }

/-- The generated final step for symbol. -/
noncomputable def weth9SymLongGeneratedLoopFinal {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {fuel : Nat}
    (hdone : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I fuel).ptr) = ⟨0⟩) :
    Weth9SymLongLoopFinal σ I endp len (weth9SymLongGeneratedLoopState σ I fuel) :=
  { memout := weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I fuel).mem
      (weth9SymLongGeneratedLoopState σ I fuel).ptr
      (weth9LongStorageWord σ I (weth9SymLongGeneratedLoopState σ I fuel).slot)
    awStore := UInt256.ofNat (MachineState.M (weth9SymLongGeneratedLoopState σ I fuel).aw.toNat
      (weth9SymLongGeneratedLoopState σ I fuel).ptr.toNat 32)
    mstoreCost := weth9SymLongLoopMstoreCost σ I endp len (weth9SymLongGeneratedLoopState σ I fuel)
    hdone := hdone
    hmemout := by simp only [weth9LongCopyMem, Reasoning.Theory.writeWord]
    hmstoreCost := fun st haw hstk =>
      weth9SymLongLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp) (len := len)
        (s := weth9SymLongGeneratedLoopState σ I fuel) st haw hstk
    hawStore := rfl }

/-! ### Count / termination (slot 1) -/

theorem weth9SymLongPtr_toNat_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i
  | 0, _ => by change (⟨160⟩ : UInt256).toNat = 160 + 32 * 0; decide
  | i + 1, hbound => by
      have hprev : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound (σ := σ) (I := I) i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      change ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I i).ptr).toNat = 160 + 32 * (i + 1)
      rw [uadd_lit32_toNat _ (by rw [hprev]; omega), hprev]; omega

/-- Word count `wc = ⌈len/32⌉ - 1` (fuel), for slot 1. -/
def weth9SymLongWC (σ : AccountMap) (I : ExecutionEnv) : Nat :=
  ((weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat - 1) / 32

/-- Continue condition at iteration `i < wc-1`. -/
theorem weth9SymLongContinue {σ : AccountMap} {I : ExecutionEnv} {i : Nat}
    (hi : i < ((weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat - 1) / 32) :
    UInt256.gt (weth9LongEnd (weth9StringSlotWord σ I ⟨1⟩))
      ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I i).ptr) ≠ ⟨0⟩ := by
  set H := weth9StringSlotWord σ I ⟨1⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  have hsize : (2 : Nat) ^ 255 + 192 < UInt256.size := by norm_num [UInt256.size]
  have hcontNat : 32 * i + 32 < (weth9StringLen H).toNat :=
    weth9LongFuel_continue_nat (by omega : 0 < (weth9StringLen H).toNat) hi
  have hptr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
    weth9SymLongPtr_toNat_of_bound (σ := σ) (I := I) i (by omega)
  have hrhs : ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I i).ptr).toNat =
      160 + 32 * i + 32 := by rw [uadd_lit32_toNat _ (by rw [hptr]; omega), hptr]
  rw [ugt_one (by rw [weth9LongEnd_toNat, hrhs]; omega)]; decide

/-- Done condition at `fuel = wc-1`. -/
theorem weth9SymLongDone {σ : AccountMap} {I : ExecutionEnv}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩) :
    UInt256.gt (weth9LongEnd (weth9StringSlotWord σ I ⟨1⟩))
      ((⟨32⟩ : UInt256) + (weth9SymLongGeneratedLoopState σ I
        (((weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat - 1) / 32)).ptr) = ⟨0⟩ := by
  set H := weth9StringSlotWord σ I ⟨1⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  have hgtNat : 31 < (weth9StringLen H).toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using ult_ne_zero_toNat_lt hge31
  have hfb := weth9LongFuel_bound hlt (n := (weth9StringLen H).toNat)
  have hdoneNat : (weth9StringLen H).toNat ≤ 32 * (((weth9StringLen H).toNat - 1) / 32) + 32 :=
    weth9LongFuel_done_nat (by omega)
  have hptr : (weth9SymLongGeneratedLoopState σ I (((weth9StringLen H).toNat - 1) / 32)).ptr.toNat =
      160 + 32 * (((weth9StringLen H).toNat - 1) / 32) :=
    weth9SymLongPtr_toNat_of_bound (σ := σ) (I := I) _ (by omega)
  have hrhs : ((⟨32⟩ : UInt256) +
      (weth9SymLongGeneratedLoopState σ I (((weth9StringLen H).toNat - 1) / 32)).ptr).toNat =
      160 + 32 * (((weth9StringLen H).toNat - 1) / 32) + 32 := by
    rw [uadd_lit32_toNat _ (by rw [hptr]; omega), hptr]
  exact ugt_zero (by rw [weth9LongEnd_toNat, hrhs]; omega)

/-- The memory after the storage→memory copy loop finishes (all `wc` data words copied). -/
noncomputable def weth9SymLongFinalMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).mem
    (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr
    (weth9LongStorageWord σ I (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).slot)

/-- Active-words count after the copy loop. -/
noncomputable def weth9SymLongFinalAw (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).aw.toNat
    (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat 32)

set_option maxHeartbeats 8000000 in
theorem weth9SymNameLongReach187 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] (weth9SymLongFinalMem σ I) (weth9SymLongFinalAw σ I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hloop⟩ := weth9SymNameLongReachLoop (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31
  exact weth9SymNameLongCopySchedule (weth9SymLongWC σ I) (weth9SymLongGeneratedLoopState σ I)
    (fun i hi => weth9SymLongGeneratedLoopStep
      (len := weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) (weth9SymLongContinue hi))
    (weth9SymLongGeneratedLoopFinal
      (len := weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) (weth9SymLongDone hge31))
    ⟨_, _, by simpa [weth9SymLongGeneratedLoopState_zero, weth9SymLongLoopStack, weth9LongEnd]
      using hloop⟩

/-! ### Memory read-preservation invariants (slot 1)

The free-pointer word (`0x40`) and length word (`0x80`) survive the copy loop; the memory size grows
to track the running pointer.  Mirrors `StringReturnLong`'s invariants with slot 1. -/

theorem weth9SymLongScratchMem_size (H : UInt256) : (weth9SymLongScratchMem H).size = 160 := by
  rw [weth9SymLongScratchMem, writeWord_size _ 0 _
    (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num)), weth9RoutineMem_size]; decide

theorem weth9SymLongScratchMem_read64 (H : UInt256) :
    (weth9SymLongScratchMem H).readWithPadding 64 32 = UInt256.toByteArray (weth9StringNewFp H) := by
  rw [weth9SymLongScratchMem,
    writeWord_read_preserved _ 0 64 _ (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num))
      (Or.inr ⟨by decide, by rw [weth9RoutineMem_size]; decide⟩)]
  exact weth9RoutineMem_read64 H

theorem weth9SymLongScratchMem_read128 (H : UInt256) :
    (weth9SymLongScratchMem H).readWithPadding 128 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9SymLongScratchMem,
    writeWord_read_preserved _ 0 128 _ (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num))
      (Or.inr ⟨by decide, by rw [weth9RoutineMem_size]⟩)]
  exact weth9RoutineMem_read128 H

theorem weth9SymLongMem_size_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).mem.size = 160 + 32 * i
  | 0, _ => by rw [weth9SymLongGeneratedLoopState_zero, weth9SymLongScratchMem_size]
  | i + 1, hbound => by
      have hprevSize : (weth9SymLongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9SymLongMem_size_of_bound i (by omega)
      have hprevPtr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      show (weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I i).mem
        (weth9SymLongGeneratedLoopState σ I i).ptr _).size = 160 + 32 * (i + 1)
      rw [weth9LongCopyMem, writeWord_size _ _ _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num)),
        hprevSize, hprevPtr]; omega

theorem weth9SymLongMem_read64_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).mem.readWithPadding 64 32 =
        UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩))
  | 0, _ => by rw [weth9SymLongGeneratedLoopState_zero]; exact weth9SymLongScratchMem_read64 _
  | i + 1, hbound => by
      have hprevPtr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9SymLongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9SymLongMem_size_of_bound i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      show ((weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I i).mem
        (weth9SymLongGeneratedLoopState σ I i).ptr _)).readWithPadding 64 32 = _
      rw [weth9LongCopyMem,
        writeWord_read_preserved _ _ 64 _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
          (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
      exact weth9SymLongMem_read64_of_bound i (by omega)

theorem weth9SymLongMem_read128_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).mem.readWithPadding 128 32 =
        UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))
  | 0, _ => by rw [weth9SymLongGeneratedLoopState_zero]; exact weth9SymLongScratchMem_read128 _
  | i + 1, hbound => by
      have hprevPtr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9SymLongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9SymLongMem_size_of_bound i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      show ((weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I i).mem
        (weth9SymLongGeneratedLoopState σ I i).ptr _)).readWithPadding 128 32 = _
      rw [weth9LongCopyMem,
        writeWord_read_preserved _ _ 128 _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
          (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
      exact weth9SymLongMem_read128_of_bound i (by omega)

theorem weth9SymLongWC_size_bound (σ : AccountMap) (I : ExecutionEnv) :
    160 + 32 * weth9SymLongWC σ I + 32 < UInt256.size :=
  weth9LongFuel_bound (weth9StringLen_toNat_lt_sign (weth9StringSlotWord σ I ⟨1⟩))

theorem weth9SymLongFinalMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (weth9SymLongFinalMem σ I).size = 160 + 32 * (weth9SymLongWC σ I + 1) := by
  have hbnd := weth9SymLongWC_size_bound σ I
  have hptr : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).mem.size =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongMem_size_of_bound _ (by omega)
  rw [weth9SymLongFinalMem, weth9LongCopyMem,
    writeWord_size _ _ _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num)), hsize, hptr]; omega

theorem weth9SymLongFinalMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (weth9SymLongFinalMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)) := by
  have hbnd := weth9SymLongWC_size_bound σ I
  have hptr : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).mem.size =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongMem_size_of_bound _ (by omega)
  rw [weth9SymLongFinalMem, weth9LongCopyMem,
    writeWord_read_preserved _ _ 64 _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
  exact weth9SymLongMem_read64_of_bound _ (by omega)

theorem weth9SymLongFinalMem_read128 (σ : AccountMap) (I : ExecutionEnv) :
    (weth9SymLongFinalMem σ I).readWithPadding 128 32 =
      UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) := by
  have hbnd := weth9SymLongWC_size_bound σ I
  have hptr : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).mem.size =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongMem_size_of_bound _ (by omega)
  rw [weth9SymLongFinalMem, weth9LongCopyMem,
    writeWord_read_preserved _ _ 128 _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
  exact weth9SymLongMem_read128_of_bound _ (by omega)

end Benchmarks.WETH9
