import Benchmarks.WETH9.StringReturn

/-!
# WETH9 dynamic-string getter — LONG case (`len ≥ 32`)

For a long string the runtime routine (`runtime.hex` 0x3a2–0x3cc) hashes the base slot to find the
data region, then runs a **storage→memory copy loop** (pc 944–963) copying `⌈len/32⌉` words, and the
ABI return encoder (pc 187) runs a second **mem→mem copy loop** (pc 221–244).  This mirrors
`Examples/StringStoreLite/ClearCurrentLong.lean`.

This file currently establishes the LONG-path setup up to the copy-loop entry (the config-independent
`weth9NameLongReachLoop`).  The symbolic-count copy loops themselves follow the
`currentLengthGeneratedLoopState`/`_Step`/`_Final` fuel-recursion template.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-- keccak(slot 0): the base storage slot of the long-string data words. -/
def weth9LongDataBase : UInt256 := solidityBytesDataBaseSlot ⟨0⟩

/-- Data-region end pointer in memory: `0xa0 + len`. -/
def weth9LongEnd (header : UInt256) : UInt256 := (⟨160⟩ : UInt256) + weth9StringLen header

/-- Scratch memory at the copy-loop entry: the routine memory with the base slot (`0`) written at
    `mem[0]` (for the `KECCAK256`). -/
noncomputable def weth9LongScratchMem (header : UInt256) : ByteArray :=
  writeWord (weth9RoutineMem header) 0 ⟨0⟩

theorem weth9LongLen_ne {H : UInt256} (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen H) ≠ ⟨0⟩) :
    weth9StringLen H ≠ ⟨0⟩ := by
  intro hz
  apply hge31
  rw [hz]; exact ult_zero (by decide)

theorem weth9LongScratchMem_read0 (H : UInt256) :
    (weth9LongScratchMem H).readWithPadding 0 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [weth9LongScratchMem]
  exact writeWord_read_back _ 0 _ (by exact lt_usize _ (by norm_num))

/-- The `KECCAK256(0, 32)` at the loop setup yields the data base slot `keccak(slot 0)`. -/
theorem weth9LongScratchMem_keccak0 (H : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((weth9LongScratchMem H).readWithPadding 0 32))) = weth9LongDataBase := by
  rw [weth9LongScratchMem_read0, weth9LongDataBase, solidityBytesDataBaseSlot,
    uInt256OfByteArray_eq]

/-! ## Reach the storage→memory copy loop (pc 897 → 944)

From the shared decode checkpoint, take the long branch (`len ≥ 32`), hash `slot 0` for the data
region, and reach the copy-loop head with `[dataPtr=0xa0, dataSlot=keccak(0), end=0xa0+len, len, …]`. -/

set_option maxHeartbeats 8000000 in
theorem weth9NameLongReachLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [⟨160⟩, weth9LongDataBase, weth9LongEnd (weth9StringSlotWord σ I ⟨0⟩),
       weth9StringLen (weth9StringSlotWord σ I ⟨0⟩), ⟨0⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9LongScratchMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h897⟩ := weth9NameRoutineReach897 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  have h910 := evm_run h897 with [
    dup1, iszero, push2 ⟨973⟩, jumpiNT (isZero_eq_zero_of_ne (weth9LongLen_ne hge31)),
    dup1, push1 ⟨31⟩, lt, push2 ⟨930⟩, jumpiT hge31 (by jump_dest)]
  have h942 := evm_run h910 with [
    jumpdest, dup3, add, swap2, swap1, push1 ⟨0⟩,
    raw mstore 0 (weth9LongScratchMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 5)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨0⟩]
  have h943 := h942.keccak256 0 weth9LongDataBase (UInt256.ofNat 5) (by decide +native)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        decide +native)
    (weth9LongScratchMem_keccak0 _) (by decide) (by evm_ov)
  exact ⟨_, _, evm_run h943 with [swap1]⟩

/-! ## Storage→memory copy loop (pc 944) — fuel-recursion machinery

Mirrors `Examples/StringStoreLite/ClearCurrentLong.lean`.  Each iteration `SLOAD`s the next data
slot, `MSTORE`s it at the running memory pointer, bumps `ptr += 32`, `slot += 1`, and loops while
`end > ptr`. -/

/-- The word stored at data slot `slot`. -/
def weth9LongStorageWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)

/-- Loop state: memory write pointer, storage read slot, memory buffer, active words. -/
structure Weth9LongLoopState where
  ptr : UInt256
  slot : UInt256
  mem : ByteArray
  aw : UInt256

/-- The EVM stack at the copy-loop head (pc 944). -/
def Weth9LongLoopState.stack (s : Weth9LongLoopState) (endp len : UInt256) (I : ExecutionEnv) :
    List UInt256 :=
  [s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]

/-- One copy-loop iteration (pc 944 → 944), continuing branch (`end > ptr + 32`). -/
theorem weth9NameLongCopyContinue {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) ≠ ⟨0⟩)
    (hmemout : (weth9LongStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [(⟨32⟩ : UInt256) + ptr, (⟨1⟩ : UInt256) + slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨187⟩, weth9SelWord I]
      memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd944⟩ := hreach
  have rd946 := evm_run rd944 with [jumpdest, dup2]
  obtain ⟨_, _, rd947₀⟩ := rd946.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd947⟩ : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨947⟩
      [weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] m aw ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [weth9LongStorageWord, initState] using rd947₀⟩
  have rd948 := evm_run rd947 with [dup2]
  have rd949 := rd948.mstore mstoreCost memout awStore (by decide +native) hmstoreCost hmemout
    hawStore (by evm_ov)
  have rd960 := evm_run rd949 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨944⟩]
  exact ⟨_, _, rd960.jumpiT (by decide +native) hcontinue (by jump_dest) (by evm_ov)⟩

/-- Copy-loop exit (pc 944 → 187), done branch (`end ≤ ptr + 32`): converges through the trailing
    bookkeeping (964–972) and the shared `POP×5; DUP2; JUMP` (973–980) back to the encoder entry. -/
theorem weth9NameLongCopyExit {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) = ⟨0⟩)
    (hmemout : (weth9LongStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd944⟩ := hreach
  have rd946 := evm_run rd944 with [jumpdest, dup2]
  obtain ⟨_, _, rd947₀⟩ := rd946.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd947⟩ : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨947⟩
      [weth9LongStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
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

/-- One `writeWord` copy at the running pointer. -/
noncomputable def weth9LongCopyMem (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  writeWord mem ptr.toNat word

/-- The generated copy-loop state after `n` iterations. -/
noncomputable def weth9LongGeneratedLoopState (σ : AccountMap) (I : ExecutionEnv) :
    Nat → Weth9LongLoopState
  | 0 =>
      { ptr := ⟨160⟩
        slot := weth9LongDataBase
        mem := weth9LongScratchMem (weth9StringSlotWord σ I ⟨0⟩)
        aw := UInt256.ofNat 5 }
  | n + 1 =>
      let s := weth9LongGeneratedLoopState σ I n
      { ptr := (⟨32⟩ : UInt256) + s.ptr
        slot := (⟨1⟩ : UInt256) + s.slot
        mem := weth9LongCopyMem s.mem s.ptr (weth9LongStorageWord σ I s.slot)
        aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) }

theorem weth9LongGeneratedLoopState_zero (σ : AccountMap) (I : ExecutionEnv) :
    weth9LongGeneratedLoopState σ I 0 =
      { ptr := ⟨160⟩, slot := weth9LongDataBase,
        mem := weth9LongScratchMem (weth9StringSlotWord σ I ⟨0⟩), aw := UInt256.ofNat 5 } := rfl

theorem weth9LongGeneratedLoopState_succ (σ : AccountMap) (I : ExecutionEnv) (n : Nat) :
    weth9LongGeneratedLoopState σ I (n + 1) =
      (let s := weth9LongGeneratedLoopState σ I n
       { ptr := (⟨32⟩ : UInt256) + s.ptr, slot := (⟨1⟩ : UInt256) + s.slot,
         mem := weth9LongCopyMem s.mem s.ptr (weth9LongStorageWord σ I s.slot),
         aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) }) := rfl

/-- Per-step data proving one copy iteration advances the generated state. -/
structure Weth9LongLoopStep (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s t : Weth9LongLoopState) where
  mstoreCost : Nat
  hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) ≠ ⟨0⟩
  hmemout : (weth9LongStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = t.mem
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = t.aw
  hptrNext : t.ptr = (⟨32⟩ : UInt256) + s.ptr
  hslotNext : t.slot = (⟨1⟩ : UInt256) + s.slot

/-- Terminal data proving the loop exits and yields the finished memory. -/
structure Weth9LongLoopFinal (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : Weth9LongLoopState) where
  memout : ByteArray
  awStore : UInt256
  mstoreCost : Nat
  hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) = ⟨0⟩
  hmemout : (weth9LongStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = memout
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨187⟩, weth9SelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = awStore

/-- Fuel-induction assembly: run `fuel` copy iterations then exit, reaching the encoder entry (187)
    with the finished memory. -/
theorem weth9NameLongCopySchedule {cA gh bl σ σ₀ A I} {g : Sat256} {endp len : UInt256}
    (fuel : Nat) (st : Nat → Weth9LongLoopState)
    (hsteps : ∀ i, i < fuel → Weth9LongLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : Weth9LongLoopFinal σ I endp len (st fuel))
    (hreach : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      ((st 0).stack endp len I) (st 0).mem (st 0).aw ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] hfinal.memout hfinal.awStore ByteArray.empty (cA, σ) k C := by
  induction fuel generalizing st with
  | zero =>
      simpa [Weth9LongLoopState.stack] using
        weth9NameLongCopyExit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp) (len := len)
          (aw := (st 0).aw) (m := (st 0).mem) (memout := hfinal.memout) (awStore := hfinal.awStore)
          (mstoreCost := hfinal.mstoreCost)
          hreach hfinal.hdone hfinal.hmemout hfinal.hmstoreCost hfinal.hawStore
  | succ fuel ih =>
      have hs : Weth9LongLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hnext₀ := weth9NameLongCopyContinue
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp) (len := len) (aw := (st 0).aw)
        (m := (st 0).mem) (memout := (st 1).mem) (awStore := (st 1).aw)
        (mstoreCost := hs.mstoreCost)
        hreach hs.hcontinue hs.hmemout hs.hmstoreCost hs.hawStore
      have hnext : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
          (((fun i => st i.succ) 0).stack endp len I)
          ((fun i => st i.succ) 0).mem ((fun i => st i.succ) 0).aw ByteArray.empty (cA, σ) k C := by
        obtain ⟨k, C, rd⟩ := hnext₀
        exact ⟨k, C, by simpa [Weth9LongLoopState.stack, hs.hptrNext, hs.hslotNext] using rd⟩
      have hsteps' : ∀ i, i < fuel →
          Weth9LongLoopStep σ I endp len ((fun j => st j.succ) i) ((fun j => st j.succ) (i + 1)) := by
        intro i hi
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hsteps i.succ (Nat.succ_lt_succ hi)
      exact ih (fun i => st i.succ) hsteps' hfinal hnext

/-! ## Instantiating the schedule for the generated loop state -/

/-- The (symbolic) `MSTORE` cost at generated loop state `s`. -/
def weth9LongLoopMstoreCost (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : Weth9LongLoopState) : Nat :=
  memoryExpansionCost
    { (default : State) with
      machineState := { (default : State).machineState with
        activeWords := s.aw
        stack := [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩,
          ⟨128⟩, ⟨187⟩, weth9SelWord I] } }
    .MSTORE

theorem weth9LongLoopMstoreCost_spec {σ : AccountMap} {I : ExecutionEnv} {endp len : UInt256}
    {s : Weth9LongLoopState} :
    ∀ st : State, st.machineState.activeWords = s.aw →
      st.machineState.stack =
        [s.ptr, weth9LongStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨187⟩, weth9SelWord I] →
      memoryExpansionCost st .MSTORE = weth9LongLoopMstoreCost σ I endp len s := by
  intro st haw hstk
  rw [weth9LongLoopMstoreCost]
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw]

/-- One generated copy-loop step, given the continue condition at state `i`. -/
noncomputable def weth9LongGeneratedLoopStep {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {i : Nat}
    (hcontinue : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I i).ptr) ≠ ⟨0⟩) :
    Weth9LongLoopStep σ I endp len
      (weth9LongGeneratedLoopState σ I i) (weth9LongGeneratedLoopState σ I (i + 1)) :=
  { mstoreCost := weth9LongLoopMstoreCost σ I endp len (weth9LongGeneratedLoopState σ I i)
    hcontinue := hcontinue
    hmemout := by
      simp only [weth9LongGeneratedLoopState_succ, weth9LongCopyMem, Reasoning.Theory.writeWord]
    hmstoreCost := fun st haw hstk =>
      weth9LongLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp) (len := len)
        (s := weth9LongGeneratedLoopState σ I i) st haw hstk
    hawStore := by simp [weth9LongGeneratedLoopState_succ]
    hptrNext := by simp [weth9LongGeneratedLoopState_succ]
    hslotNext := by simp [weth9LongGeneratedLoopState_succ] }

/-- The generated final step, given the done condition at state `fuel`. -/
noncomputable def weth9LongGeneratedLoopFinal {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {fuel : Nat}
    (hdone : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I fuel).ptr) = ⟨0⟩) :
    Weth9LongLoopFinal σ I endp len (weth9LongGeneratedLoopState σ I fuel) :=
  { memout := weth9LongCopyMem (weth9LongGeneratedLoopState σ I fuel).mem
      (weth9LongGeneratedLoopState σ I fuel).ptr
      (weth9LongStorageWord σ I (weth9LongGeneratedLoopState σ I fuel).slot)
    awStore := UInt256.ofNat (MachineState.M (weth9LongGeneratedLoopState σ I fuel).aw.toNat
      (weth9LongGeneratedLoopState σ I fuel).ptr.toNat 32)
    mstoreCost := weth9LongLoopMstoreCost σ I endp len (weth9LongGeneratedLoopState σ I fuel)
    hdone := hdone
    hmemout := by simp only [weth9LongCopyMem, Reasoning.Theory.writeWord]
    hmstoreCost := fun st haw hstk =>
      weth9LongLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp) (len := len)
        (s := weth9LongGeneratedLoopState σ I fuel) st haw hstk
    hawStore := rfl }

/-! ## Step 1 — count / termination

The copy loop runs `wc = ⌈len/32⌉` times: `fuel := (len-1)/32 = wc-1` continue iterations plus the
exit (the `wc`-th copy).  Mirrors ClearCurrentLong's fuel arithmetic. -/

theorem weth9StringLen_toNat_lt_sign (H : UInt256) : (weth9StringLen H).toNat < 2 ^ 255 := by
  unfold weth9StringLen
  rw [udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  apply Nat.div_lt_of_lt_mul
  have hh : (UInt256.land H (weth9StringMask H)).toNat < UInt256.size :=
    (UInt256.land H (weth9StringMask H)).val.isLt
  norm_num [UInt256.size] at hh ⊢; omega

theorem weth9LongEnd_toNat (H : UInt256) :
    (weth9LongEnd H).toNat = 160 + (weth9StringLen H).toNat := by
  rw [weth9LongEnd, uadd_toNat, show (⟨160⟩ : UInt256).toNat = 160 from by decide,
    Nat.add_comm 160 _]
  exact Nat.mod_eq_of_lt (by
    have := weth9StringLen_toNat_lt_sign H
    have hsize : (2 : Nat) ^ 255 + 160 < UInt256.size := by norm_num [UInt256.size]
    omega)

theorem weth9LongPtr_toNat_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i
  | 0, _ => by change (⟨160⟩ : UInt256).toNat = 160 + 32 * 0; decide
  | i + 1, hbound => by
      have hprev : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound (σ := σ) (I := I) i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      change ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I i).ptr).toNat = 160 + 32 * (i + 1)
      rw [uadd_lit32_toNat _ (by rw [hprev]; omega), hprev]; omega

theorem weth9LongAdd32_of_fuelBound {σ : AccountMap} {I : ExecutionEnv} {fuel : Nat}
    (hfuelBound : 160 + 32 * fuel + 32 < UInt256.size) :
    ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I i).ptr).toNat =
        (weth9LongGeneratedLoopState σ I i).ptr.toNat + 32) := by
  intro i hi
  have hptr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
    weth9LongPtr_toNat_of_bound (σ := σ) (I := I) i (by nlinarith)
  exact uadd_lit32_toNat _ (by rw [hptr]; nlinarith)

theorem weth9LongFuel_continue_nat {n i : Nat} (hn : 0 < n) (hi : i < (n - 1) / 32) :
    32 * i + 32 < n := by
  have hiSucc : i + 1 ≤ (n - 1) / 32 := Nat.succ_le_of_lt hi
  have hmul : 32 * (i + 1) ≤ 32 * ((n - 1) / 32) := Nat.mul_le_mul_left 32 hiSucc
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  omega

theorem weth9LongFuel_done_nat {n : Nat} (hn : 0 < n) : n ≤ 32 * ((n - 1) / 32) + 32 := by
  have hdecomp : n - 1 = (n - 1) / 32 * 32 + (n - 1) % 32 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (n - 1) 32).symm
  have hmod : (n - 1) % 32 < 32 := Nat.mod_lt _ (by decide)
  omega

theorem weth9LongFuel_bound {n : Nat} (hn : n < 2 ^ 255) :
    160 + 32 * ((n - 1) / 32) + 32 < UInt256.size := by
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  have hsize : (2 : Nat) ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
  omega

/-- Continue condition at iteration `i < wc-1`. -/
theorem weth9LongContinue {σ : AccountMap} {I : ExecutionEnv} {i : Nat}
    (hi : i < ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 1) / 32) :
    UInt256.gt (weth9LongEnd (weth9StringSlotWord σ I ⟨0⟩))
      ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I i).ptr) ≠ ⟨0⟩ := by
  set H := weth9StringSlotWord σ I ⟨0⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  have hsize : (2 : Nat) ^ 255 + 192 < UInt256.size := by norm_num [UInt256.size]
  have hcontNat : 32 * i + 32 < (weth9StringLen H).toNat :=
    weth9LongFuel_continue_nat (by omega : 0 < (weth9StringLen H).toNat) hi
  have hptr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
    weth9LongPtr_toNat_of_bound (σ := σ) (I := I) i (by omega)
  have hrhs : ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I i).ptr).toNat =
      160 + 32 * i + 32 := by rw [uadd_lit32_toNat _ (by rw [hptr]; omega), hptr]
  rw [ugt_one (by rw [weth9LongEnd_toNat, hrhs]; omega)]; decide

/-- Done condition at `fuel = wc-1` (the exit iteration performs the `wc`-th copy). -/
theorem weth9LongDone {σ : AccountMap} {I : ExecutionEnv}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩) :
    UInt256.gt (weth9LongEnd (weth9StringSlotWord σ I ⟨0⟩))
      ((⟨32⟩ : UInt256) + (weth9LongGeneratedLoopState σ I
        (((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 1) / 32)).ptr) = ⟨0⟩ := by
  set H := weth9StringSlotWord σ I ⟨0⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  have hgtNat : 31 < (weth9StringLen H).toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using ult_ne_zero_toNat_lt hge31
  have hfb := weth9LongFuel_bound hlt (n := (weth9StringLen H).toNat)
  have hdoneNat : (weth9StringLen H).toNat ≤ 32 * (((weth9StringLen H).toNat - 1) / 32) + 32 :=
    weth9LongFuel_done_nat (by omega)
  have hptr : (weth9LongGeneratedLoopState σ I (((weth9StringLen H).toNat - 1) / 32)).ptr.toNat =
      160 + 32 * (((weth9StringLen H).toNat - 1) / 32) :=
    weth9LongPtr_toNat_of_bound (σ := σ) (I := I) _ (by omega)
  have hrhs : ((⟨32⟩ : UInt256) +
      (weth9LongGeneratedLoopState σ I (((weth9StringLen H).toNat - 1) / 32)).ptr).toNat =
      160 + 32 * (((weth9StringLen H).toNat - 1) / 32) + 32 := by
    rw [uadd_lit32_toNat _ (by rw [hptr]; omega), hptr]
  exact ugt_zero (by rw [weth9LongEnd_toNat, hrhs]; omega)

/-! ## Step 2 — connect the reach-loop to the schedule (pc 897 → 187 with the copied memory) -/

/-- Word count `wc = ⌈len/32⌉` as a `Nat`. -/
def weth9LongWC (σ : AccountMap) (I : ExecutionEnv) : Nat :=
  ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 1) / 32

/-- The memory after the storage→memory copy loop finishes (all `wc` data words copied). -/
noncomputable def weth9LongFinalMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  weth9LongCopyMem (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).mem
    (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr
    (weth9LongStorageWord σ I (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).slot)

/-- Active-words count after the copy loop. -/
noncomputable def weth9LongFinalAw (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).aw.toNat
    (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat 32)

set_option maxHeartbeats 8000000 in
theorem weth9NameLongReach187 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] (weth9LongFinalMem σ I) (weth9LongFinalAw σ I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hloop⟩ := weth9NameLongReachLoop (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31
  exact weth9NameLongCopySchedule (weth9LongWC σ I) (weth9LongGeneratedLoopState σ I)
    (fun i hi => weth9LongGeneratedLoopStep
      (len := weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) (weth9LongContinue hi))
    (weth9LongGeneratedLoopFinal
      (len := weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) (weth9LongDone hge31))
    ⟨_, _, by simpa [weth9LongGeneratedLoopState_zero, Weth9LongLoopState.stack, weth9LongEnd]
      using hloop⟩

/-! ## Step 3 — memory read-preservation invariants

The free-pointer word (`0x40`) and length word (`0x80`) survive the copy loop, since every write is at
`ptr ≥ 0xa0`.  The memory size grows to track the pointer. -/

/-- `weth9RoutineMem` as a `writeWord` tower (free ptr at `0x40`, length word at `0x80`). -/
theorem weth9RoutineMem_writeWord (H : UInt256) :
    weth9RoutineMem H =
      writeWord (writeWord solcFreePtrMem 64 (weth9StringNewFp H)) 128 (weth9StringLen H) := rfl

theorem weth9RoutineMem_size (H : UInt256) : (weth9RoutineMem H).size = 160 := by
  rw [weth9RoutineMem_writeWord,
    writeWord_size _ 128 _ (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num)),
    weth9ShortL1_size]; omega

theorem weth9LongScratchMem_size (H : UInt256) : (weth9LongScratchMem H).size = 160 := by
  rw [weth9LongScratchMem, writeWord_size _ 0 _ (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num)),
    weth9RoutineMem_size]; decide

theorem weth9RoutineMem_read64 (H : UInt256) :
    (weth9RoutineMem H).readWithPadding 64 32 = UInt256.toByteArray (weth9StringNewFp H) := by
  rw [weth9RoutineMem_writeWord,
    writeWord_read_preserved _ 128 64 _ (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortL1_size]⟩)]
  exact writeWord_read_back _ 64 _ (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))

theorem weth9RoutineMem_read128 (H : UInt256) :
    (weth9RoutineMem H).readWithPadding 128 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9RoutineMem_writeWord]
  exact writeWord_read_back _ 128 _
    (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num))

theorem weth9LongScratchMem_read64 (H : UInt256) :
    (weth9LongScratchMem H).readWithPadding 64 32 = UInt256.toByteArray (weth9StringNewFp H) := by
  rw [weth9LongScratchMem,
    writeWord_read_preserved _ 0 64 _ (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num))
      (Or.inr ⟨by decide, by rw [weth9RoutineMem_size]; decide⟩)]
  exact weth9RoutineMem_read64 H

theorem weth9LongScratchMem_read128 (H : UInt256) :
    (weth9LongScratchMem H).readWithPadding 128 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9LongScratchMem,
    writeWord_read_preserved _ 0 128 _ (by rw [weth9RoutineMem_size]; exact lt_usize _ (by norm_num))
      (Or.inr ⟨by decide, by rw [weth9RoutineMem_size]⟩)]
  exact weth9RoutineMem_read128 H

/-- Loop memory size after `i` copies: `0xa0 + 32·i` (each copy is an at-end 32-byte write). -/
theorem weth9LongMem_size_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).mem.size = 160 + 32 * i
  | 0, _ => by rw [weth9LongGeneratedLoopState_zero, weth9LongScratchMem_size]
  | i + 1, hbound => by
      have hprevSize : (weth9LongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9LongMem_size_of_bound i (by omega)
      have hprevPtr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      show (weth9LongCopyMem (weth9LongGeneratedLoopState σ I i).mem
        (weth9LongGeneratedLoopState σ I i).ptr _).size = 160 + 32 * (i + 1)
      rw [weth9LongCopyMem, writeWord_size _ _ _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num)),
        hprevSize, hprevPtr]; omega

/-- The free-pointer word at `0x40` is unchanged by the copy loop (writes are all at `ptr ≥ 0xa0`). -/
theorem weth9LongMem_read64_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).mem.readWithPadding 64 32 =
        UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩))
  | 0, _ => by rw [weth9LongGeneratedLoopState_zero]; exact weth9LongScratchMem_read64 _
  | i + 1, hbound => by
      have hprevPtr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9LongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9LongMem_size_of_bound i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      show ((weth9LongCopyMem (weth9LongGeneratedLoopState σ I i).mem
        (weth9LongGeneratedLoopState σ I i).ptr _)).readWithPadding 64 32 = _
      rw [weth9LongCopyMem,
        writeWord_read_preserved _ _ 64 _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
          (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
      exact weth9LongMem_read64_of_bound i (by omega)

/-- The length word at `0x80` is unchanged by the copy loop. -/
theorem weth9LongMem_read128_of_bound {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).mem.readWithPadding 128 32 =
        UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))
  | 0, _ => by rw [weth9LongGeneratedLoopState_zero]; exact weth9LongScratchMem_read128 _
  | i + 1, hbound => by
      have hprevPtr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9LongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9LongMem_size_of_bound i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      show ((weth9LongCopyMem (weth9LongGeneratedLoopState σ I i).mem
        (weth9LongGeneratedLoopState σ I i).ptr _)).readWithPadding 128 32 = _
      rw [weth9LongCopyMem,
        writeWord_read_preserved _ _ 128 _ (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
          (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
      exact weth9LongMem_read128_of_bound i (by omega)

/-- Sign bound on `wc`: `160 + 32·wc < UInt256.size`. -/
theorem weth9LongWC_size_bound (σ : AccountMap) (I : ExecutionEnv) :
    160 + 32 * weth9LongWC σ I + 32 < UInt256.size :=
  weth9LongFuel_bound (weth9StringLen_toNat_lt_sign (weth9StringSlotWord σ I ⟨0⟩))

theorem weth9LongFinalMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (weth9LongFinalMem σ I).size = 160 + 32 * (weth9LongWC σ I + 1) := by
  have hbnd := weth9LongWC_size_bound σ I
  have hptr : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat =
      160 + 32 * weth9LongWC σ I := weth9LongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).mem.size =
      160 + 32 * weth9LongWC σ I := weth9LongMem_size_of_bound _ (by omega)
  rw [weth9LongFinalMem, weth9LongCopyMem,
    writeWord_size _ _ _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num)), hsize, hptr]; omega

theorem weth9LongFinalMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (weth9LongFinalMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)) := by
  have hbnd := weth9LongWC_size_bound σ I
  have hptr : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat =
      160 + 32 * weth9LongWC σ I := weth9LongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).mem.size =
      160 + 32 * weth9LongWC σ I := weth9LongMem_size_of_bound _ (by omega)
  rw [weth9LongFinalMem, weth9LongCopyMem,
    writeWord_read_preserved _ _ 64 _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
  exact weth9LongMem_read64_of_bound _ (by omega)

theorem weth9LongFinalMem_read128 (σ : AccountMap) (I : ExecutionEnv) :
    (weth9LongFinalMem σ I).readWithPadding 128 32 =
      UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) := by
  have hbnd := weth9LongWC_size_bound σ I
  have hptr : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat =
      160 + 32 * weth9LongWC σ I := weth9LongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).mem.size =
      160 + 32 * weth9LongWC σ I := weth9LongMem_size_of_bound _ (by omega)
  rw [weth9LongFinalMem, weth9LongCopyMem,
    writeWord_read_preserved _ _ 128 _ (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
  exact weth9LongMem_read128_of_bound _ (by omega)

/-! ## Steps 4-5 — symbolic-offset ABI encoder (pc 187 → RETURN)

The encoder is the same bytecode as the short path but with a **symbolic** free pointer
`newFp = 0xa0 + 32·wc`.  The generic memory-cost witnesses below (giving the cost as a symbolic
`Cₘ` expression rather than a concrete `decide`) are what make the symbolic-offset `MLOAD`/`MSTORE`/
`RETURN` steps drivable — the analog of the mem-cost specs used for the copy loop. -/

theorem weth9MloadCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw → st.machineState.stack = off :: stk →
      memoryExpansionCost st .MLOAD =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem weth9MstoreCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw → st.machineState.stack = off :: stk →
      memoryExpansionCost st .MSTORE =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem weth9ReturnCostSpec {aw off len : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw → st.machineState.stack = off :: len :: stk →
      memoryExpansionCost st .RETURN =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
    List.getElem!_cons_zero, List.getElem!_cons_succ]

end Benchmarks.WETH9
