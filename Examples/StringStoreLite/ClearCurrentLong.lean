import Examples.StringStoreLite.Getters

/-!
# StringStoreLite — `currentLength()` long-string branch work

This module extends the getter proof with the valid long-string path.  It imports the completed
getter/shared facts but keeps new loop-heavy proof work out of `Getters.lean`, so iteration on the
remaining storage-copy loop does not force that module to re-elaborate.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStoreLite

def currentLengthStorageWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

structure CurrentLengthLoopState where
  ptr : UInt256
  slot : UInt256
  mem : ByteArray
  aw : UInt256

def CurrentLengthLoopState.stack (s : CurrentLengthLoopState) (endp len : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]

noncomputable def currentLengthLongScratchMem (len : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (currentLengthMem len) 0 32

noncomputable def currentLengthCopyMem (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  word.toByteArray.write 0 mem ptr.toNat 32

def currentLengthLoopMstoreStack (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : CurrentLengthLoopState) : List UInt256 :=
  [s.ptr, currentLengthStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩,
    ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]

def currentLengthLoopMstoreCost (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : CurrentLengthLoopState) : Nat :=
  memoryExpansionCost
    { (default : State) with
      machineState := { (default : State).machineState with
        activeWords := s.aw
        stack := currentLengthLoopMstoreStack σ I endp len s } }
    .MSTORE

noncomputable def currentLengthGeneratedLoopState (σ : AccountMap) (I : ExecutionEnv)
    (len : UInt256) : Nat → CurrentLengthLoopState
  | 0 =>
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 }
  | n + 1 =>
      let s := currentLengthGeneratedLoopState σ I len n
      { ptr := (⟨32⟩ : UInt256) + s.ptr
        slot := (⟨1⟩ : UInt256) + s.slot
        mem := currentLengthCopyMem s.mem s.ptr (currentLengthStorageWord σ I s.slot)
        aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) }

theorem currentLengthLoopMstoreCost_spec {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {s : CurrentLengthLoopState} :
    ∀ st : State, st.machineState.activeWords = s.aw →
      st.machineState.stack = currentLengthLoopMstoreStack σ I endp len s →
      memoryExpansionCost st .MSTORE =
        currentLengthLoopMstoreCost σ I endp len s := by
  intro st haw hstk
  rw [currentLengthLoopMstoreCost]
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw]

theorem mloadCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: stk →
      memoryExpansionCost st .MLOAD =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem mstoreCostSpec {aw off : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: stk →
      memoryExpansionCost st .MSTORE =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]

theorem returnCostSpec {aw off len : UInt256} {stk : List UInt256} :
    ∀ st : State, st.machineState.activeWords = aw →
      st.machineState.stack = off :: len :: stk →
      memoryExpansionCost st .RETURN =
        Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) - Cₘ aw := by
  intro st haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
    List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem currentLengthGeneratedLoopState_zero {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    currentLengthGeneratedLoopState σ I len 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 } := by
  rfl

theorem currentLengthGeneratedLoopState_succ {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} {n : Nat} :
    currentLengthGeneratedLoopState σ I len (n + 1) =
      let s := currentLengthGeneratedLoopState σ I len n
      { ptr := (⟨32⟩ : UInt256) + s.ptr
        slot := (⟨1⟩ : UInt256) + s.slot
        mem := currentLengthCopyMem s.mem s.ptr (currentLengthStorageWord σ I s.slot)
        aw := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) } := by
  rfl

structure CurrentLengthLoopStep (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s t : CurrentLengthLoopState) where
  mstoreCost : Nat
  hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) ≠ ⟨0⟩
  hmemout :
    (currentLengthStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = t.mem
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, currentLengthStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = t.aw
  hptrNext : t.ptr = (⟨32⟩ : UInt256) + s.ptr
  hslotNext : t.slot = (⟨1⟩ : UInt256) + s.slot

structure CurrentLengthLoopFinal (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : CurrentLengthLoopState) where
  memout : ByteArray
  awStore : UInt256
  awLoad : UInt256
  mstoreCost : Nat
  mloadCost : Nat
  hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + s.ptr) = ⟨0⟩
  hmemout :
    (currentLengthStorageWord σ I s.slot).toByteArray.write 0 s.mem s.ptr.toNat 32 = memout
  hmstoreCost : ∀ st : State, st.machineState.activeWords = s.aw →
    st.machineState.stack =
      [s.ptr, currentLengthStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = awStore
  hmloadCost : ∀ st : State, st.machineState.activeWords = awStore →
    st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
    memoryExpansionCost st .MLOAD = mloadCost
  hloadVal : (if (⟨128⟩ : UInt256).toNat ≥ memout.size
      ∨ (⟨128⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (memout.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len
  hawLoad : UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32) = awLoad

noncomputable def currentLengthGeneratedLoopStep {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {i : Nat}
    (hcontinue : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩) :
    CurrentLengthLoopStep σ I endp len
      (currentLengthGeneratedLoopState σ I len i)
      (currentLengthGeneratedLoopState σ I len (i + 1)) := by
  let s := currentLengthGeneratedLoopState σ I len i
  refine
    { mstoreCost := currentLengthLoopMstoreCost σ I endp len s
      hcontinue := by simpa [s] using hcontinue
      hmemout := ?_
      hmstoreCost := ?_
      hawStore := ?_
      hptrNext := ?_
      hslotNext := ?_ }
  · simp [currentLengthGeneratedLoopState_succ, currentLengthCopyMem]
  · intro st haw hstk
    exact currentLengthLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp)
      (len := len) (s := s) st haw (by simpa [currentLengthLoopMstoreStack, s] using hstk)
  · simp [currentLengthGeneratedLoopState_succ]
  · simp [currentLengthGeneratedLoopState_succ]
  · simp [currentLengthGeneratedLoopState_succ]

noncomputable def currentLengthGeneratedLoopSteps {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {fuel : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt endp ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠
        ⟨0⟩) :
    ∀ i, i < fuel →
      CurrentLengthLoopStep σ I endp len
        (currentLengthGeneratedLoopState σ I len i)
        (currentLengthGeneratedLoopState σ I len (i + 1)) := by
  intro i hi
  exact currentLengthGeneratedLoopStep (σ := σ) (I := I) (endp := endp) (len := len)
    (i := i) (hcontinue i hi)

noncomputable def currentLengthGeneratedLoopFinal {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} {fuel finalMloadCost : Nat} {awLoad : UInt256}
    (hdone : UInt256.gt endp
      ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad) :
    CurrentLengthLoopFinal σ I endp len
      (currentLengthGeneratedLoopState σ I len fuel) := by
  let s := currentLengthGeneratedLoopState σ I len fuel
  refine
    { memout := currentLengthCopyMem s.mem s.ptr (currentLengthStorageWord σ I s.slot)
      awStore := UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32)
      awLoad := awLoad
      mstoreCost := currentLengthLoopMstoreCost σ I endp len s
      mloadCost := finalMloadCost
      hdone := by simpa [s] using hdone
      hmemout := by simp [s, currentLengthCopyMem]
      hmstoreCost := ?_
      hawStore := rfl
      hmloadCost := by simpa [s] using hmloadCost
      hloadVal := by simpa [s, currentLengthCopyMem] using hloadVal
      hawLoad := by simpa [s] using hawLoad }
  intro st haw hstk
  exact currentLengthLoopMstoreCost_spec (σ := σ) (I := I) (endp := endp)
    (len := len) (s := s) st haw (by simpa [currentLengthLoopMstoreStack, s] using hstk)

theorem currentLengthCopyMem_read64 {mem : ByteArray} {ptr word : UInt256}
    (hptr : 96 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size) :
    (currentLengthCopyMem mem ptr word).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  exact write32_read_below (UInt256.toByteArray word) mem ptr.toNat 64
    (by rw [toByteArray_size]) hin (by
      rw [show 64 + 32 = 96 from rfl]
      exact hptr)

theorem currentLengthCopyMem_read128 {mem : ByteArray} {ptr word : UInt256}
    (hptr : 160 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size) :
    (currentLengthCopyMem mem ptr word).readWithPadding 128 32 =
      mem.readWithPadding 128 32 := by
  exact write32_read_below (UInt256.toByteArray word) mem ptr.toNat 128
    (by rw [toByteArray_size]) hin (by
      rw [show 128 + 32 = 160 from rfl]
      exact hptr)

theorem currentLengthCopyMem_size_at_end {mem : ByteArray} {ptr word : UInt256}
    (hptr : ptr.toNat = mem.size) :
    (currentLengthCopyMem mem ptr word).size = mem.size + 32 := by
  have hgap : ptr.toNat - mem.size = 0 := by rw [hptr]; omega
  rw [currentLengthCopyMem,
    toByteArray_write_eq word mem ptr.toNat (by rw [hptr]) (by rw [hgap]; native_decide),
    hgap]
  rw [ByteArray.size_append, ByteArray.size_append,
    zeroes_zero (n := USize.ofNat 0) (by native_decide), ByteArray.size_empty,
    toByteArray_size]

theorem currentLengthCopyMem_size_ge_mem {mem : ByteArray} {ptr word : UInt256}
    (hin : ptr.toNat ≤ mem.size) :
    mem.size ≤ (currentLengthCopyMem mem ptr word).size := by
  rw [currentLengthCopyMem,
    write32_eq (UInt256.toByteArray word) mem ptr.toNat
      (by rw [toByteArray_size]) hin]
  have hhead : (mem.extract 0 ptr.toNat).size = ptr.toNat := by
    rw [ByteArray.size_extract]
    omega
  have hword : ((UInt256.toByteArray word).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  by_cases htailIn : ptr.toNat + 32 ≤ mem.size
  · have htail :
        (mem.extract (ptr.toNat + 32) mem.size).size =
          mem.size - (ptr.toNat + 32) := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega
  · have htail : (mem.extract (ptr.toNat + 32) mem.size).size = 0 := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega

theorem writeWord_size_ge_mem {mem : ByteArray} {off : Nat} {word : UInt256}
    (hin : off ≤ mem.size) :
    mem.size ≤ (word.toByteArray.write 0 mem off 32).size := by
  rw [write32_eq (UInt256.toByteArray word) mem off
      (by rw [toByteArray_size]) hin]
  have hhead : (mem.extract 0 off).size = off := by
    rw [ByteArray.size_extract]
    omega
  have hword : ((UInt256.toByteArray word).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  by_cases htailIn : off + 32 ≤ mem.size
  · have htail :
        (mem.extract (off + 32) mem.size).size =
          mem.size - (off + 32) := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega
  · have htail : (mem.extract (off + 32) mem.size).size = 0 := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega

theorem writeWord_size_gt64_of_mem {mem : ByteArray} {off : Nat} {word : UInt256}
    (hmem : 64 < mem.size) (hin : off ≤ mem.size) :
    64 < (word.toByteArray.write 0 mem off 32).size :=
  lt_of_lt_of_le hmem (writeWord_size_ge_mem (mem := mem) (off := off) (word := word) hin)

theorem currentLengthCopyMem_size_gt128 {mem : ByteArray} {ptr word : UInt256}
    (hptr : 160 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size) :
    128 < (currentLengthCopyMem mem ptr word).size := by
  have hmem : 128 < mem.size := by omega
  exact lt_of_lt_of_le hmem (currentLengthCopyMem_size_ge_mem (mem := mem) (ptr := ptr)
    (word := word) hin)

theorem currentLengthLongScratchMem_read0 (len : UInt256) :
    (currentLengthLongScratchMem len).readWithPadding 0 32 =
      UInt256.toByteArray ⟨0⟩ := by
  rw [currentLengthLongScratchMem]
  rw [write32_read_back (UInt256.toByteArray ⟨0⟩) (currentLengthMem len) 0
    (by rw [toByteArray_size])
    (by rw [currentLengthMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem currentLengthLongScratchMem_read128 (len : UInt256) :
    (currentLengthLongScratchMem len).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  have hpres :
      ((UInt256.toByteArray ⟨0⟩).write 0 (currentLengthMem len) 0 32).readWithPadding 128 32 =
        (currentLengthMem len).readWithPadding 128 32 :=
    write32_read_above (UInt256.toByteArray ⟨0⟩) (currentLengthMem len) 0 128
      (by rw [toByteArray_size])
      (by rw [currentLengthMem_size]; decide)
      (by decide)
      (by rw [currentLengthMem_size])
  rw [currentLengthMem_read128] at hpres
  simpa [currentLengthLongScratchMem] using hpres

theorem currentLengthLongScratchMem_read64 (len : UInt256) :
    (currentLengthLongScratchMem len).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  have hpres :
      ((UInt256.toByteArray ⟨0⟩).write 0 (currentLengthMem len) 0 32).readWithPadding 64 32 =
        (currentLengthMem len).readWithPadding 64 32 :=
    write32_read_above (UInt256.toByteArray ⟨0⟩) (currentLengthMem len) 0 64
      (by rw [toByteArray_size])
      (by rw [currentLengthMem_size]; decide)
      (by decide)
      (by rw [currentLengthMem_size]; decide)
  rw [currentLengthMem_read64] at hpres
  simpa [currentLengthLongScratchMem] using hpres

theorem currentLengthLongScratchMem_size (len : UInt256) :
    (currentLengthLongScratchMem len).size = 160 := by
  have hEq :
      currentLengthLongScratchMem len =
        (currentLengthMem len).extract 0 0 ++ UInt256.toByteArray ⟨0⟩ ++
          (currentLengthMem len).extract 32 (currentLengthMem len).size := by
    rw [currentLengthLongScratchMem,
      write32_eq (UInt256.toByteArray ⟨0⟩) (currentLengthMem len) 0
      (by rw [toByteArray_size])
      (by rw [currentLengthMem_size]; decide),
      toByteArray_extract_all]
  have hhead : ((currentLengthMem len).extract 0 0).size = 0 := by
    simp
  have htail :
      ((currentLengthMem len).extract 32 (currentLengthMem len).size).size = 128 := by
    rw [ByteArray.size_extract, currentLengthMem_size]
    omega
  rw [hEq, ByteArray.size_append, ByteArray.size_append, hhead, htail, toByteArray_size]

theorem currentLengthLongScratchMem_mload128 (len : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (currentLengthLongScratchMem len).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((currentLengthLongScratchMem len).readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 5) (v := len)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, currentLengthLongScratchMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      currentLengthLongScratchMem_read128 len)

theorem currentLengthLongScratchMem_keccak0 (len : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((currentLengthLongScratchMem len).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨0⟩ := by
  rw [currentLengthLongScratchMem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨0⟩ : UInt256))

theorem currentLengthCopyMem_preserves_read64 {mem : ByteArray} {ptr word freePtr : UInt256}
    (hptr : 96 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (currentLengthCopyMem mem ptr word).readWithPadding 64 32 =
      UInt256.toByteArray freePtr := by
  rw [currentLengthCopyMem_read64 hptr hin, hread]

theorem currentLengthReturnWrite_preserves_read64 {mem : ByteArray} {len freePtr : UInt256}
    (hptr : 96 ≤ freePtr.toNat) (hin : freePtr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (len.toByteArray.write 0 mem freePtr.toNat 32).readWithPadding 64 32 =
      UInt256.toByteArray freePtr := by
  rw [write32_read_below (UInt256.toByteArray len) mem freePtr.toNat 64
    (by rw [toByteArray_size]) hin (by
      rw [show 64 + 32 = 96 from rfl]
      exact hptr)]
  exact hread

theorem currentLengthReturnWrite_readBack {mem : ByteArray} {len freePtr : UInt256}
    (hin : freePtr.toNat ≤ mem.size) :
    (len.toByteArray.write 0 mem freePtr.toNat 32).readWithPadding freePtr.toNat 32 =
      UInt256.toByteArray len := by
  rw [write32_read_back (UInt256.toByteArray len) mem freePtr.toNat
    (by rw [toByteArray_size]) hin]
  rw [toByteArray_extract_all]

theorem currentLength_add_zero_toNat (w : UInt256) :
    ((w + ⟨0⟩ : UInt256).toNat) = w.toNat := by
  rw [uadd_toNat]
  simp only [UInt256.toNat]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem currentLengthReturnWrite_preserves_read64_zero {mem : ByteArray} {len freePtr : UInt256}
    (hptr : 96 ≤ freePtr.toNat) (hin : freePtr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (len.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).readWithPadding 64 32 =
      UInt256.toByteArray freePtr := by
  simpa [currentLength_add_zero_toNat] using
    currentLengthReturnWrite_preserves_read64
      (mem := mem) (len := len) (freePtr := freePtr) hptr hin hread

theorem currentLengthReturnWrite_retBytes {mem : ByteArray} {len freePtr : UInt256}
    (hin : freePtr.toNat ≤ mem.size)
    (hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32) :
    (len.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).readWithPadding
        freePtr.toNat (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat =
      UInt256.toByteArray len := by
  rw [hretLen]
  simpa [currentLength_add_zero_toNat] using
    currentLengthReturnWrite_readBack (mem := mem) (len := len) (freePtr := freePtr) hin

theorem currentLength_mload64_of_read64 {mem : ByteArray} {aw freePtr : UInt256}
    (hmem : 64 < mem.size)
    (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := freePtr)
    (by simpa using hmem)
    haw
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread)

theorem currentLengthLoopState_preserves_read64 {σ : AccountMap} {I : ExecutionEnv}
    {endp len freePtr : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hptr : ∀ i, i < fuel → 96 ≤ (st i).ptr.toNat)
    (hin : ∀ i, i < fuel → (st i).ptr.toNat ≤ (st i).mem.size)
    (hread : (st 0).mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (st fuel).mem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
  induction fuel generalizing st with
  | zero =>
      exact hread
  | succ fuel ih =>
      have hs : CurrentLengthLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hread1 : (st 1).mem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
        rw [← hs.hmemout]
        exact currentLengthCopyMem_preserves_read64
          (mem := (st 0).mem) (ptr := (st 0).ptr)
          (word := currentLengthStorageWord σ I (st 0).slot) (freePtr := freePtr)
          (hptr 0 (Nat.zero_lt_succ fuel))
          (hin 0 (Nat.zero_lt_succ fuel))
          hread
      exact ih (fun i => st i.succ)
        (by
          intro i hi
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            hsteps i.succ (Nat.succ_lt_succ hi))
        (by
          intro i hi
          simpa using hptr i.succ (Nat.succ_lt_succ hi))
        (by
          intro i hi
          simpa using hin i.succ (Nat.succ_lt_succ hi))
        hread1

theorem currentLengthLoopFinal_preserves_read64 {σ : AccountMap} {I : ExecutionEnv}
    {endp len freePtr : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : CurrentLengthLoopFinal σ I endp len (st fuel))
    (hptr : ∀ i, i ≤ fuel → 96 ≤ (st i).ptr.toNat)
    (hin : ∀ i, i ≤ fuel → (st i).ptr.toNat ≤ (st i).mem.size)
    (hread : (st 0).mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    hfinal.memout.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
  have hstate :
      (st fuel).mem.readWithPadding 64 32 = UInt256.toByteArray freePtr :=
    currentLengthLoopState_preserves_read64
      (σ := σ) (I := I) (endp := endp) (len := len) fuel st hsteps
      (by intro i hi; exact hptr i (Nat.le_of_lt hi))
      (by intro i hi; exact hin i (Nat.le_of_lt hi))
      hread
  rw [← hfinal.hmemout]
  exact currentLengthCopyMem_preserves_read64
    (mem := (st fuel).mem) (ptr := (st fuel).ptr)
    (word := currentLengthStorageWord σ I (st fuel).slot) (freePtr := freePtr)
    (hptr fuel (Nat.le_refl fuel))
    (hin fuel (Nat.le_refl fuel))
    hstate

theorem currentLengthCopyMem_preserves_read128 {mem : ByteArray} {ptr word len : UInt256}
    (hptr : 160 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 128 32 = UInt256.toByteArray len) :
    (currentLengthCopyMem mem ptr word).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  rw [currentLengthCopyMem_read128 hptr hin, hread]

theorem currentLengthLoopState_preserves_read128 {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hptr : ∀ i, i < fuel → 160 ≤ (st i).ptr.toNat)
    (hin : ∀ i, i < fuel → (st i).ptr.toNat ≤ (st i).mem.size)
    (hread : (st 0).mem.readWithPadding 128 32 = UInt256.toByteArray len) :
    (st fuel).mem.readWithPadding 128 32 = UInt256.toByteArray len := by
  induction fuel generalizing st with
  | zero =>
      exact hread
  | succ fuel ih =>
      have hs : CurrentLengthLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hread1 : (st 1).mem.readWithPadding 128 32 = UInt256.toByteArray len := by
        rw [← hs.hmemout]
        exact currentLengthCopyMem_preserves_read128
          (mem := (st 0).mem) (ptr := (st 0).ptr)
          (word := currentLengthStorageWord σ I (st 0).slot) (len := len)
          (hptr 0 (Nat.zero_lt_succ fuel))
          (hin 0 (Nat.zero_lt_succ fuel))
          hread
      exact ih (fun i => st i.succ)
        (by
          intro i hi
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            hsteps i.succ (Nat.succ_lt_succ hi))
        (by
          intro i hi
          simpa using hptr i.succ (Nat.succ_lt_succ hi))
        (by
          intro i hi
          simpa using hin i.succ (Nat.succ_lt_succ hi))
        hread1

theorem currentLengthLoopFinal_preserves_read128 {σ : AccountMap} {I : ExecutionEnv}
    {endp len : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : CurrentLengthLoopFinal σ I endp len (st fuel))
    (hptr : ∀ i, i ≤ fuel → 160 ≤ (st i).ptr.toNat)
    (hin : ∀ i, i ≤ fuel → (st i).ptr.toNat ≤ (st i).mem.size)
    (hread : (st 0).mem.readWithPadding 128 32 = UInt256.toByteArray len) :
    hfinal.memout.readWithPadding 128 32 = UInt256.toByteArray len := by
  have hstate :
      (st fuel).mem.readWithPadding 128 32 = UInt256.toByteArray len :=
    currentLengthLoopState_preserves_read128
      (σ := σ) (I := I) (endp := endp) (len := len) fuel st hsteps
      (by intro i hi; exact hptr i (Nat.le_of_lt hi))
      (by intro i hi; exact hin i (Nat.le_of_lt hi))
      hread
  rw [← hfinal.hmemout]
  exact currentLengthCopyMem_preserves_read128
    (mem := (st fuel).mem) (ptr := (st fuel).ptr)
    (word := currentLengthStorageWord σ I (st fuel).slot) (len := len)
    (hptr fuel (Nat.le_refl fuel))
    (hin fuel (Nat.le_refl fuel))
    hstate

theorem currentLengthGeneratedLoopFinal_read64 {σ : AccountMap} {I : ExecutionEnv}
    {len awLoad : UInt256} {fuel finalMloadCost : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad)
    (hptr : ∀ i, i ≤ fuel → 96 ≤ (currentLengthGeneratedLoopState σ I len i).ptr.toNat)
    (hin : ∀ i, i ≤ fuel →
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat ≤
        (currentLengthGeneratedLoopState σ I len i).mem.size) :
    (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).memout.readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact currentLengthLoopFinal_preserves_read64
    (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
    (freePtr := currentLengthFreePtr len) fuel
    (currentLengthGeneratedLoopState σ I len)
    (currentLengthGeneratedLoopSteps
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) hcontinue)
    (currentLengthGeneratedLoopFinal
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
      hdone hmloadCost hloadVal hawLoad)
    hptr hin
    (by
      simpa [currentLengthGeneratedLoopState_zero] using currentLengthLongScratchMem_read64 len)

theorem currentLengthGeneratedLoopState_mem_size_eq_ptr {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      (currentLengthGeneratedLoopState σ I len i).mem.size =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat
  | 0, _ => by
      rw [currentLengthGeneratedLoopState_zero, currentLengthLongScratchMem_size]
      change 160 = (⟨160⟩ : UInt256).toNat
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev :
          s.mem.size = s.ptr.toNat :=
        currentLengthGeneratedLoopState_mem_size_eq_ptr (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hcopySize :
          (currentLengthCopyMem s.mem s.ptr (currentLengthStorageWord σ I s.slot)).size =
            s.mem.size + 32 :=
        currentLengthCopyMem_size_at_end (mem := s.mem) (ptr := s.ptr)
          (word := currentLengthStorageWord σ I s.slot) hprev.symm
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      simp [currentLengthGeneratedLoopState_succ, s, hcopySize, hprev, hptrNext]

theorem currentLengthGeneratedLoopState_ptr_le_mem_size {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} (i : Nat)
    (hnext : ∀ j, j < i →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) :
    (currentLengthGeneratedLoopState σ I len i).ptr.toNat ≤
      (currentLengthGeneratedLoopState σ I len i).mem.size := by
  have hsize :=
    currentLengthGeneratedLoopState_mem_size_eq_ptr
      (σ := σ) (I := I) (len := len) i hnext
  omega

theorem currentLengthGeneratedLoopState_ptr_ge96 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      96 ≤ (currentLengthGeneratedLoopState σ I len i).ptr.toNat
  | 0, _ => by
      rw [currentLengthGeneratedLoopState_zero]
      change 96 ≤ (⟨160⟩ : UInt256).toNat
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev : 96 ≤ s.ptr.toNat :=
        currentLengthGeneratedLoopState_ptr_ge96 (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      rw [currentLengthGeneratedLoopState_succ]
      change 96 ≤ (((⟨32⟩ : UInt256) + s.ptr).toNat)
      rw [hptrNext]
      omega

theorem currentLengthGeneratedLoopState_ptr_ge160 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      160 ≤ (currentLengthGeneratedLoopState σ I len i).ptr.toNat
  | 0, _ => by
      rw [currentLengthGeneratedLoopState_zero]
      change 160 ≤ (⟨160⟩ : UInt256).toNat
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev : 160 ≤ s.ptr.toNat :=
        currentLengthGeneratedLoopState_ptr_ge160 (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      rw [currentLengthGeneratedLoopState_succ]
      change 160 ≤ (((⟨32⟩ : UInt256) + s.ptr).toNat)
      rw [hptrNext]
      omega

theorem machineState_M_32_lt_u256_size {s f : ℕ}
    (hs : s < UInt256.size) (hf : f < UInt256.size) :
    MachineState.M s f 32 < UInt256.size := by
  simp only [MachineState.M]
  apply max_lt hs
  apply Nat.div_lt_of_lt_mul
  have hsize : 64 ≤ UInt256.size := by
    norm_num [UInt256.size]
  nlinarith

theorem machineState_M_mul32_lt_of_bounds {s f l : ℕ}
    (hs : s * 32 < UInt256.size)
    (hfl : f + l + 31 < UInt256.size) :
    MachineState.M s f l * 32 < UInt256.size := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl, hs]
  · simp only [MachineState.M]
    let c := (f + l + 31) / 32
    have hceil : ((f + l + 31) / 32) * 32 ≤ f + l + 31 := by
      exact Nat.div_mul_le_self (f + l + 31) 32
    have hc : c * 32 < UInt256.size := by
      exact lt_of_le_of_lt hceil hfl
    by_cases hsc : s ≤ c
    · rw [max_eq_right hsc]
      exact hc
    · have hcs : c ≤ s := Nat.le_of_not_ge hsc
      rw [max_eq_left hcs]
      exact hs

theorem machineState_M_word_mul32_lt_of_bounds {aw off len : UInt256}
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + len.toNat + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat * 32 <
      UInt256.size := by
  have hM := machineState_M_mul32_lt_of_bounds
    (s := aw.toNat) (f := off.toNat) (l := len.toNat) haw hoff
  have hMSize : MachineState.M aw.toNat off.toNat len.toNat < UInt256.size := by
    have hle : MachineState.M aw.toNat off.toNat len.toNat ≤
        MachineState.M aw.toNat off.toNat len.toNat * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M aw.toNat off.toNat len.toNat) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hM
  rw [ulit_toNat' _ hMSize]
  exact hM

theorem machineState_M_ge_left {s f l : Nat} : s ≤ MachineState.M s f l := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl]
  · simp [MachineState.M]

theorem machineState_M_word_ge_aw {aw off len : UInt256}
    (hMSize : MachineState.M aw.toNat off.toNat len.toNat < UInt256.size) :
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat := by
  rw [ulit_toNat' _ hMSize]
  exact machineState_M_ge_left

theorem activeWordsMload64_eq_self {aw : UInt256} (hge : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 = aw.toNat := by
    simp only [MachineState.M]
    have hceil : ((⟨64⟩ : UInt256).toNat + 32 + 31) / 32 = 3 := by
      decide
    rw [hceil]
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem activeWordsMload128_eq_self {aw : UInt256} (hge : 5 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32 = aw.toNat := by
    simp only [MachineState.M]
    have hceil : ((⟨128⟩ : UInt256).toNat + 32 + 31) / 32 = 5 := by
      decide
    rw [hceil]
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem currentLengthGeneratedLoopState_aw_ge5 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat, 5 ≤ (currentLengthGeneratedLoopState σ I len i).aw.toNat
  | 0 => by
      change 5 ≤ (UInt256.ofNat 5).toNat
      decide
  | i + 1 => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev : 5 ≤ s.aw.toNat :=
        currentLengthGeneratedLoopState_aw_ge5 (σ := σ) (I := I) (len := len) i
      have hawLt : s.aw.toNat < UInt256.size := by
        simp [UInt256.toNat, s.aw.val.isLt]
      have hptrLt : s.ptr.toNat < UInt256.size := by
        simp [UInt256.toNat, s.ptr.val.isLt]
      have hMSize : MachineState.M s.aw.toNat s.ptr.toNat 32 < UInt256.size :=
        machineState_M_32_lt_u256_size hawLt hptrLt
      rw [currentLengthGeneratedLoopState_succ]
      change 5 ≤ (UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32)).toNat
      rw [ulit_toNat' _ hMSize]
      exact le_trans hprev (by
        simp only [MachineState.M]
        exact Nat.le_max_left _ _)

theorem currentLengthGeneratedLoopState_ptr_mod32 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat % 32 = 0
  | 0, _ => by
      change (⟨160⟩ : UInt256).toNat % 32 = 0
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev : s.ptr.toNat % 32 = 0 :=
        currentLengthGeneratedLoopState_ptr_mod32 (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      rw [currentLengthGeneratedLoopState_succ]
      change (((⟨32⟩ : UInt256) + s.ptr).toNat % 32 = 0)
      rw [hptrNext, Nat.add_mod, hprev]

theorem currentLengthGeneratedLoopState_aw_eq_ptr_div32 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      (currentLengthGeneratedLoopState σ I len i).aw.toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat / 32
  | 0, _ => by
      change (UInt256.ofNat 5).toNat = (⟨160⟩ : UInt256).toNat / 32
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev :
          s.aw.toNat = s.ptr.toNat / 32 :=
        currentLengthGeneratedLoopState_aw_eq_ptr_div32
          (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hmod : s.ptr.toNat % 32 = 0 :=
        currentLengthGeneratedLoopState_ptr_mod32
          (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      have hawLt : s.aw.toNat < UInt256.size := by
        simp [UInt256.toNat, s.aw.val.isLt]
      have hptrLt : s.ptr.toNat < UInt256.size := by
        simp [UInt256.toNat, s.ptr.val.isLt]
      have hMSize : MachineState.M s.aw.toNat s.ptr.toNat 32 < UInt256.size :=
        machineState_M_32_lt_u256_size hawLt hptrLt
      have hceil :
          (s.ptr.toNat + 32 + 31) / 32 = s.ptr.toNat / 32 + 1 := by
        omega
      have hdivNext :
          (s.ptr.toNat + 32) / 32 = s.ptr.toNat / 32 + 1 := by
        omega
      rw [currentLengthGeneratedLoopState_succ]
      change (UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32)).toNat =
        ((⟨32⟩ : UInt256) + s.ptr).toNat / 32
      rw [ulit_toNat' _ hMSize, hptrNext, hdivNext]
      simp only [MachineState.M]
      rw [hprev, hceil]
      exact max_eq_right (by omega)

theorem currentLengthGeneratedLoopState_ptr_toNat_eq {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat = 160 + 32 * i
  | 0, _ => by
      change (⟨160⟩ : UInt256).toNat = 160 + 32 * 0
      decide
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprev :
          s.ptr.toNat = 160 + 32 * i :=
        currentLengthGeneratedLoopState_ptr_toNat_eq
          (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptrNext :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) := by
        simpa [s] using hnext i (Nat.lt_succ_self i)
      rw [currentLengthGeneratedLoopState_succ]
      change (((⟨32⟩ : UInt256) + s.ptr).toNat = 160 + 32 * (i + 1))
      rw [hptrNext, hprev]
      omega

theorem currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hfuelBound : 160 + 32 * fuel + 32 < UInt256.size) :
    (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 < UInt256.size := by
  have hptr :
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat = 160 + 32 * fuel :=
    currentLengthGeneratedLoopState_ptr_toNat_eq
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  omega

theorem currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hptrBound : (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 < UInt256.size) :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size := by
  let s := currentLengthGeneratedLoopState σ I len fuel
  have haw :
      s.aw.toNat = s.ptr.toNat / 32 :=
    currentLengthGeneratedLoopState_aw_eq_ptr_div32
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  have hmod : s.ptr.toNat % 32 = 0 :=
    currentLengthGeneratedLoopState_ptr_mod32
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  have hceil : (s.ptr.toNat + 32 + 31) / 32 = s.ptr.toNat / 32 + 1 := by
    omega
  have hmul : (s.ptr.toNat / 32 + 1) * 32 = s.ptr.toNat + 32 := by
    omega
  change MachineState.M s.aw.toNat s.ptr.toNat 32 * 32 < UInt256.size
  simp only [MachineState.M]
  rw [haw, hceil, max_eq_right (by omega), hmul]
  exact hptrBound

theorem currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size) :
    5 ≤
      (UInt256.ofNat
        (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat := by
  let m := MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
    (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
  have hmGe : 5 ≤ m := by
    change 5 ≤ MachineState.M
      (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
    simp only [MachineState.M]
    exact le_trans (currentLengthGeneratedLoopState_aw_ge5
      (σ := σ) (I := I) (len := len) fuel)
      (Nat.le_max_left _ _)
  have hmSize : m < UInt256.size := by
    have : m ≤ m * 32 := by
      simpa using Nat.mul_le_mul_left m (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt this hMNoWrap
  simpa [m, ulit_toNat' m hmSize] using hmGe

theorem currentLengthGeneratedFinalCopy_mload128_aw_eq_awStore_of_mNoWrap
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size) :
    UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
              (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
          (⟨128⟩ : UInt256).toNat 32) =
      UInt256.ofNat
        (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) := by
  exact activeWordsMload128_eq_self
    (aw := UInt256.ofNat
      (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32))
    (currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
      (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap)

theorem currentLengthGeneratedLoopState_read128_of_add32 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} :
    ∀ i : Nat,
      (∀ j, j < i →
        (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
          (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32)) →
      (currentLengthGeneratedLoopState σ I len i).mem.readWithPadding 128 32 =
        UInt256.toByteArray len
  | 0, _ => by
      simpa [currentLengthGeneratedLoopState_zero] using currentLengthLongScratchMem_read128 len
  | i + 1, hnext => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hread :
          s.mem.readWithPadding 128 32 = UInt256.toByteArray len :=
        currentLengthGeneratedLoopState_read128_of_add32
          (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hptr : 160 ≤ s.ptr.toNat :=
        currentLengthGeneratedLoopState_ptr_ge160 (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hin : s.ptr.toNat ≤ s.mem.size :=
        currentLengthGeneratedLoopState_ptr_le_mem_size (σ := σ) (I := I) (len := len) i
          (by
            intro j hj
            exact hnext j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      rw [currentLengthGeneratedLoopState_succ]
      exact currentLengthCopyMem_preserves_read128
        (mem := s.mem) (ptr := s.ptr)
        (word := currentLengthStorageWord σ I s.slot) (len := len)
        hptr hin hread

theorem currentLengthGeneratedFinalCopy_read128_of_add32 {σ : AccountMap} {I : ExecutionEnv}
    {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32)) :
    (currentLengthCopyMem
      (currentLengthGeneratedLoopState σ I len fuel).mem
      (currentLengthGeneratedLoopState σ I len fuel).ptr
      (currentLengthStorageWord σ I
        (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  have hread :
      (currentLengthGeneratedLoopState σ I len fuel).mem.readWithPadding 128 32 =
        UInt256.toByteArray len :=
    currentLengthGeneratedLoopState_read128_of_add32
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  exact currentLengthCopyMem_preserves_read128
    (mem := (currentLengthGeneratedLoopState σ I len fuel).mem)
    (ptr := (currentLengthGeneratedLoopState σ I len fuel).ptr)
    (word := currentLengthStorageWord σ I
      (currentLengthGeneratedLoopState σ I len fuel).slot)
    (len := len)
    (currentLengthGeneratedLoopState_ptr_ge160
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel))))
    (currentLengthGeneratedLoopState_ptr_le_mem_size
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel))))
    hread

theorem currentLengthGeneratedFinalCopy_size_gt128_of_add32
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32)) :
    128 <
      (currentLengthCopyMem
        (currentLengthGeneratedLoopState σ I len fuel).mem
        (currentLengthGeneratedLoopState σ I len fuel).ptr
        (currentLengthStorageWord σ I
          (currentLengthGeneratedLoopState σ I len fuel).slot)).size := by
  exact currentLengthCopyMem_size_gt128
    (mem := (currentLengthGeneratedLoopState σ I len fuel).mem)
    (ptr := (currentLengthGeneratedLoopState σ I len fuel).ptr)
    (word := currentLengthStorageWord σ I
      (currentLengthGeneratedLoopState σ I len fuel).slot)
    (currentLengthGeneratedLoopState_ptr_ge160
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel))))
    (currentLengthGeneratedLoopState_ptr_le_mem_size
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel))))

theorem currentLengthGeneratedFinalCopy_size_eq_ptr_add32_of_add32
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32)) :
    (currentLengthCopyMem
      (currentLengthGeneratedLoopState σ I len fuel).mem
      (currentLengthGeneratedLoopState σ I len fuel).ptr
      (currentLengthStorageWord σ I
        (currentLengthGeneratedLoopState σ I len fuel).slot)).size =
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 := by
  have hmem :
      (currentLengthGeneratedLoopState σ I len fuel).mem.size =
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat :=
    currentLengthGeneratedLoopState_mem_size_eq_ptr
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  have hsize := currentLengthCopyMem_size_at_end
    (mem := (currentLengthGeneratedLoopState σ I len fuel).mem)
    (ptr := (currentLengthGeneratedLoopState σ I len fuel).ptr)
    (word := currentLengthStorageWord σ I
      (currentLengthGeneratedLoopState σ I len fuel).slot)
    hmem.symm
  rw [hsize, hmem]

theorem currentLengthGeneratedLoopFinal_read64_of_add32 {σ : AccountMap} {I : ExecutionEnv}
    {len awLoad : UInt256} {fuel finalMloadCost : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad)
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32)) :
    (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).memout.readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  exact currentLengthGeneratedLoopFinal_read64
    (σ := σ) (I := I) (len := len) (fuel := fuel)
    (finalMloadCost := finalMloadCost) (awLoad := awLoad)
    hcontinue hdone hmloadCost hloadVal hawLoad
    (by
      intro i hi
      exact currentLengthGeneratedLoopState_ptr_ge96
        (σ := σ) (I := I) (len := len) i
        (by
          intro j hj
          exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) hi)))
    (by
      intro i hi
      exact currentLengthGeneratedLoopState_ptr_le_mem_size
        (σ := σ) (I := I) (len := len) i
        (by
          intro j hj
          exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) hi)))

theorem currentLengthGeneratedLoopFinal_read128 {σ : AccountMap} {I : ExecutionEnv}
    {len awLoad : UInt256} {fuel finalMloadCost : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad)
    (hptr : ∀ i, i ≤ fuel → 160 ≤ (currentLengthGeneratedLoopState σ I len i).ptr.toNat)
    (hin : ∀ i, i ≤ fuel →
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat ≤
        (currentLengthGeneratedLoopState σ I len i).mem.size) :
    (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).memout.readWithPadding 128 32 =
      UInt256.toByteArray len := by
  exact currentLengthLoopFinal_preserves_read128
    (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
    fuel (currentLengthGeneratedLoopState σ I len)
    (currentLengthGeneratedLoopSteps
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) hcontinue)
    (currentLengthGeneratedLoopFinal
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
      hdone hmloadCost hloadVal hawLoad)
    hptr hin
    (by
      simpa [currentLengthGeneratedLoopState_zero] using currentLengthLongScratchMem_read128 len)

theorem currentLengthGeneratedLoopFinal_read128_of_add32 {σ : AccountMap} {I : ExecutionEnv}
    {len awLoad : UInt256} {fuel finalMloadCost : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad)
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32)) :
    (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).memout.readWithPadding 128 32 =
      UInt256.toByteArray len := by
  exact currentLengthGeneratedLoopFinal_read128
    (σ := σ) (I := I) (len := len) (fuel := fuel)
    (finalMloadCost := finalMloadCost) (awLoad := awLoad)
    hcontinue hdone hmloadCost hloadVal hawLoad
    (by
      intro i hi
      exact currentLengthGeneratedLoopState_ptr_ge160
        (σ := σ) (I := I) (len := len) i
        (by
          intro j hj
          exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) hi)))
    (by
      intro i hi
      exact currentLengthGeneratedLoopState_ptr_le_mem_size
        (σ := σ) (I := I) (len := len) i
        (by
          intro j hj
          exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) hi)))

theorem currentLengthGeneratedLoopFinal_mload128_of_add32
    {σ : AccountMap} {I : ExecutionEnv}
    {len awLoad : UInt256} {fuel finalMloadCost : Nat}
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost)
    (hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = awLoad)
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hsize128 :
      128 <
        (currentLengthCopyMem
          (currentLengthGeneratedLoopState σ I len fuel).mem
          (currentLengthGeneratedLoopState σ I len fuel).ptr
          (currentLengthStorageWord σ I
            (currentLengthGeneratedLoopState σ I len fuel).slot)).size)
    (haw128 :
      ¬ (⟨128⟩ : UInt256) ≥
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (mem := currentLengthCopyMem
      (currentLengthGeneratedLoopState σ I len fuel).mem
      (currentLengthGeneratedLoopState σ I len fuel).ptr
      (currentLengthStorageWord σ I
        (currentLengthGeneratedLoopState σ I len fuel).slot))
    (aw := UInt256.ofNat
      (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32))
    (off := (⟨128⟩ : UInt256)) (v := len)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using hsize128)
    haw128
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        currentLengthGeneratedLoopFinal_read128_of_add32
          (σ := σ) (I := I) (len := len) (fuel := fuel)
          (finalMloadCost := finalMloadCost) (awLoad := awLoad)
          hcontinue hdone hmloadCost hloadVal hawLoad hadd32)

theorem currentLengthGeneratedFinalCopy_mload128_of_add32
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hsize128 :
      128 <
        (currentLengthCopyMem
          (currentLengthGeneratedLoopState σ I len fuel).mem
          (currentLengthGeneratedLoopState σ I len fuel).ptr
          (currentLengthStorageWord σ I
            (currentLengthGeneratedLoopState σ I len fuel).slot)).size)
    (haw128 :
      ¬ (⟨128⟩ : UInt256) ≥
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (mem := currentLengthCopyMem
      (currentLengthGeneratedLoopState σ I len fuel).mem
      (currentLengthGeneratedLoopState σ I len fuel).ptr
      (currentLengthStorageWord σ I
        (currentLengthGeneratedLoopState σ I len fuel).slot))
    (aw := UInt256.ofNat
      (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32))
    (off := (⟨128⟩ : UInt256)) (v := len)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using hsize128)
    haw128
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        currentLengthGeneratedFinalCopy_read128_of_add32
          (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32)

theorem currentLengthGeneratedFinalCopy_mload128_of_add32_aw
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (haw128 :
      ¬ (⟨128⟩ : UInt256) ≥
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact currentLengthGeneratedFinalCopy_mload128_of_add32
    (σ := σ) (I := I) (len := len) (fuel := fuel)
    hadd32
    (currentLengthGeneratedFinalCopy_size_gt128_of_add32
      (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32)
    haw128

theorem currentLengthGeneratedFinalCopy_aw128_of_mNoWrap
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size) :
    ¬ (⟨128⟩ : UInt256) ≥
      UInt256.ofNat
        (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ := by
  let m := MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
    (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
  have hmGe : 5 ≤ m := by
    change 5 ≤ MachineState.M
      (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
    simp only [MachineState.M]
    exact le_trans (currentLengthGeneratedLoopState_aw_ge5
      (σ := σ) (I := I) (len := len) fuel)
      (Nat.le_max_left _ _)
  have hmSize : m < UInt256.size := by
    have : m ≤ m * 32 := by
      simpa using Nat.mul_le_mul_left m (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt this hMNoWrap
  have hmToNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m hmSize
  have hmul :
      (UInt256.ofNat m * (⟨32⟩ : UInt256)).toNat = m * 32 := by
    simpa [hmToNat] using
      umul_toNat (a := UInt256.ofNat m) (b := (⟨32⟩ : UInt256)) (by
        simpa [hmToNat] using hMNoWrap)
  intro hge
  have h128 : (⟨128⟩ : UInt256).toNat ≥
      (UInt256.ofNat m * (⟨32⟩ : UInt256)).toNat := by
    exact hge
  rw [hmul] at h128
  change 128 ≥ m * 32 at h128
  nlinarith

theorem wordMul32_not_le64_of_ge3 {aw : UInt256}
    (hge : 3 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h64 : (⟨64⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h64
  change 64 ≥ aw.toNat * 32 at h64
  nlinarith

theorem wordMul32_not_le128_of_ge5 {aw : UInt256}
    (hge : 5 ≤ aw.toNat) (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hgeWord
  have h128 : (⟨128⟩ : UInt256).toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hgeWord
  rw [hmul] at h128
  change 128 ≥ aw.toNat * 32 at h128
  nlinarith

theorem currentLengthGeneratedFinalCopy_aw64_of_mNoWrap
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥
      UInt256.ofNat
        (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ := by
  let m := MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
    (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
  have hmGe : 3 ≤ m := by
    have hmGe5 : 5 ≤ m := by
      change 5 ≤ MachineState.M
        (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
      simp only [MachineState.M]
      exact le_trans (currentLengthGeneratedLoopState_aw_ge5
        (σ := σ) (I := I) (len := len) fuel)
        (Nat.le_max_left _ _)
    omega
  have hmSize : m < UInt256.size := by
    have : m ≤ m * 32 := by
      simpa using Nat.mul_le_mul_left m (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt this hMNoWrap
  have hmToNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m hmSize
  exact wordMul32_not_le64_of_ge3
    (aw := UInt256.ofNat m)
    (by simpa [hmToNat] using hmGe)
    (by simpa [hmToNat] using hMNoWrap)

theorem currentLengthGeneratedFinalCopy_mload128_of_add32_mNoWrap
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact currentLengthGeneratedFinalCopy_mload128_of_add32_aw
    (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32
    (currentLengthGeneratedFinalCopy_aw128_of_mNoWrap
      (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap)

theorem currentLengthGeneratedFinalCopy_mload128_of_add32_ptrBound
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hptrBound : (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact currentLengthGeneratedFinalCopy_mload128_of_add32_mNoWrap
    (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32
    (currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32 hptrBound)

theorem currentLengthGeneratedFinalCopy_mload128_of_add32_fuelBound
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32))
    (hfuelBound : 160 + 32 * fuel + 32 < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact currentLengthGeneratedFinalCopy_mload128_of_add32_ptrBound
    (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32
    (currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
      (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32 hfuelBound)

theorem currentLengthGeneratedLoopContinue_of_nat
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {i : Nat}
    (hendp : (((⟨160⟩ : UInt256) + len).toNat = 160 + len.toNat))
    (hadd32 : ∀ j, j ≤ i →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32))
    (hcontinueNat : 32 * i + 32 < len.toNat) :
    UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠
      ⟨0⟩ := by
  have hptr :
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat = 160 + 32 * i :=
    currentLengthGeneratedLoopState_ptr_toNat_eq
      (σ := σ) (I := I) (len := len) i
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl i)))
  have hrhs :
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        160 + 32 * i + 32) := by
    rw [hadd32 i (Nat.le_refl i), hptr]
  have hgt :
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) =
        ⟨1⟩ :=
    ugt_one (by
      rw [hendp, hrhs]
      omega)
  rw [hgt]
  decide

theorem currentLengthGeneratedLoopDone_of_nat
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hendp : (((⟨160⟩ : UInt256) + len).toNat = 160 + len.toNat))
    (hadd32 : ∀ j, j ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len j).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len j).ptr.toNat + 32))
    (hdoneNat : len.toNat ≤ 32 * fuel + 32) :
    UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩ := by
  have hptr :
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat = 160 + 32 * fuel :=
    currentLengthGeneratedLoopState_ptr_toNat_eq
      (σ := σ) (I := I) (len := len) fuel
      (by
        intro j hj
        exact hadd32 j (Nat.le_trans (Nat.le_of_lt hj) (Nat.le_refl fuel)))
  have hrhs :
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len fuel).ptr).toNat =
        160 + 32 * fuel + 32) := by
    rw [hadd32 fuel (Nat.le_refl fuel), hptr]
  exact ugt_zero (by
    rw [hendp, hrhs]
    omega)

theorem currentLengthGeneratedLoopState_ptr_toNat_eq_of_bound
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} :
    ∀ i : Nat,
      160 + 32 * i < UInt256.size →
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat = 160 + 32 * i
  | 0, _ => by
      change (⟨160⟩ : UInt256).toNat = 160 + 32 * 0
      decide
  | i + 1, hbound => by
      let s := currentLengthGeneratedLoopState σ I len i
      have hprevBound : 160 + 32 * i < UInt256.size := by omega
      have hprev :
          s.ptr.toNat = 160 + 32 * i :=
        currentLengthGeneratedLoopState_ptr_toNat_eq_of_bound
          (σ := σ) (I := I) (len := len) i hprevBound
      have hadd :
          (((⟨32⟩ : UInt256) + s.ptr).toNat = s.ptr.toNat + 32) :=
        uadd_lit32_toNat (a := s.ptr) (by rw [hprev]; omega)
      rw [currentLengthGeneratedLoopState_succ]
      change (((⟨32⟩ : UInt256) + s.ptr).toNat = 160 + 32 * (i + 1))
      rw [hadd, hprev]
      omega

theorem currentLengthGeneratedLoopState_add32_of_fuelBound
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {fuel : Nat}
    (hfuelBound : 160 + 32 * fuel + 32 < UInt256.size) :
    ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32) := by
  intro i hi
  have hptr :
      (currentLengthGeneratedLoopState σ I len i).ptr.toNat = 160 + 32 * i :=
    currentLengthGeneratedLoopState_ptr_toNat_eq_of_bound
      (σ := σ) (I := I) (len := len) i (by nlinarith)
  exact uadd_lit32_toNat
    (a := (currentLengthGeneratedLoopState σ I len i).ptr) (by rw [hptr]; nlinarith)

theorem currentLengthFuel_continue_nat {n i : Nat}
    (hn : 0 < n) (hi : i < (n - 1) / 32) :
    32 * i + 32 < n := by
  have hiSucc : i + 1 ≤ (n - 1) / 32 := Nat.succ_le_of_lt hi
  have hmul : 32 * (i + 1) ≤ 32 * ((n - 1) / 32) :=
    Nat.mul_le_mul_left 32 hiSucc
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  have hle : 32 * (i + 1) ≤ n - 1 := le_trans hmul hdiv
  have hlt : 32 * (i + 1) < n := by omega
  omega

theorem currentLengthFuel_done_nat {n : Nat} (hn : 0 < n) :
    n ≤ 32 * ((n - 1) / 32) + 32 := by
  have hdecomp :
      n - 1 = (n - 1) / 32 * 32 + (n - 1) % 32 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (n - 1) 32).symm
  have hmod : (n - 1) % 32 < 32 := Nat.mod_lt _ (by decide)
  omega

theorem currentLengthFuel_bound {n : Nat}
    (hn : n < 2 ^ 255) :
    160 + 32 * ((n - 1) / 32) + 32 < UInt256.size := by
  have hdiv : 32 * ((n - 1) / 32) ≤ n - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n - 1) 32
  have hsize : (2 : Nat) ^ 255 + 191 < UInt256.size := by
    norm_num [UInt256.size]
  by_cases hzero : n = 0
  · subst hzero
    norm_num [UInt256.size]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
    have hnm1 : n - 1 + 192 = n + 191 := by omega
    nlinarith

theorem currentLength_len_toNat_lt_sign_of_div2 {header len : UInt256}
    (hlen : len = UInt256.div header ⟨2⟩) :
    len.toNat < 2 ^ 255 := by
  have hlenNat : len.toNat = header.toNat / 2 := by
    rw [hlen, udiv_toNat]
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [hlenNat]
  apply Nat.div_lt_of_lt_mul
  have hheader : header.toNat < UInt256.size := header.val.isLt
  norm_num [UInt256.size] at hheader ⊢
  exact hheader

theorem land_one_eq_one_of_ne_zero {w : UInt256}
    (h : UInt256.land w ⟨1⟩ ≠ ⟨0⟩) :
    UInt256.land w ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  change (UInt256.land w ⟨1⟩).toNat = 1
  have hbit := uInt256_land_one_toNat w
  have hlt : (UInt256.land w ⟨1⟩).toNat < 2 := by
    rw [hbit]
    exact Nat.mod_lt _ (by decide)
  have hne : (UInt256.land w ⟨1⟩).toNat ≠ 0 := by
    intro hz
    exact h (uint256_toNat_eq_zero hz)
  omega

theorem ult_eq_one_of_ne_zero {a b : UInt256}
    (h : UInt256.lt a b ≠ ⟨0⟩) :
    UInt256.lt a b = ⟨1⟩ := by
  have hlt := ult_ne_zero_toNat_lt h
  exact ult_one hlt

theorem currentLengthLongValid_gt31 {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
  have hland : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    land_one_eq_one_of_ne_zero hflag
  have hnotLt32 : UInt256.lt len ⟨32⟩ = ⟨0⟩ := by
    by_contra hltNotZero
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_eq_one_of_ne_zero hltNotZero
    exact hvalid (by simp [hland, hltOne, UInt256.sub])
  have hge32 : 32 ≤ len.toNat := by
    by_contra hlt
    have hltOne : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
      ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using Nat.lt_of_not_ge hlt)
    rw [hltOne] at hnotLt32
    contradiction
  rw [show UInt256.lt ⟨31⟩ len = ⟨1⟩ from
    ult_one (by
      rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      omega)]
  decide

theorem currentLengthLongValid_nonzero {header len : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    len ≠ ⟨0⟩ := by
  have hgt := currentLengthLongValid_gt31 (header := header) (len := len) hflag hvalid
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt
  intro hzero
  rw [hzero] at hgtNat
  contradiction

theorem currentLength_endp_toNat_of_len_lt_sign {len : UInt256}
    (hlen : len.toNat < 2 ^ 255) :
    (((⟨160⟩ : UInt256) + len).toNat = 160 + len.toNat) := by
  rw [uadd_toNat, show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  rw [Nat.add_comm 160 len.toNat]
  exact Nat.mod_eq_of_lt (by
    have hsize : (2 : Nat) ^ 255 + 160 < UInt256.size := by
      norm_num [UInt256.size]
    nlinarith)

theorem currentLengthConcreteFuel_add32
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) :
    ∀ i, i ≤ (len.toNat - 1) / 32 →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32) :=
  currentLengthGeneratedLoopState_add32_of_fuelBound
    (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
    (currentLengthFuel_bound hlenLt)

theorem currentLengthConcreteFuel_continue
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∀ i, i < (len.toNat - 1) / 32 →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠
          ⟨0⟩ := by
  intro i hi
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  exact currentLengthGeneratedLoopContinue_of_nat
    (σ := σ) (I := I) (len := len) (i := i)
    (currentLength_endp_toNat_of_len_lt_sign hlenLt)
    (by
      intro j hj
      exact currentLengthConcreteFuel_add32
        (σ := σ) (I := I) (len := len) hlenLt j
        (Nat.le_trans hj (Nat.le_of_lt hi)))
    (currentLengthFuel_continue_nat (by omega : 0 < len.toNat) hi)

theorem currentLengthConcreteFuel_done
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr) =
        ⟨0⟩ := by
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  exact currentLengthGeneratedLoopDone_of_nat
    (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
    (currentLength_endp_toNat_of_len_lt_sign hlenLt)
    (currentLengthConcreteFuel_add32 (σ := σ) (I := I) (len := len) hlenLt)
    (currentLengthFuel_done_nat (by omega : 0 < len.toNat))

theorem currentLengthConcreteFuel_finalMload128
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).mem
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (ByteArray.readWithPadding
              (currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).mem
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).slot))
              (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact currentLengthGeneratedFinalCopy_mload128_of_add32_fuelBound
    (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
    (currentLengthConcreteFuel_add32 (σ := σ) (I := I) (len := len) hlenLt)
    (currentLengthFuel_bound hlenLt)

theorem currentLengthCeilWords_eq {n : Nat} (hn : 0 < n) :
    (31 + n) / 32 = (n - 1) / 32 + 1 := by
  omega

theorem currentLengthFreePtr_toNat_of_len_lt_sign_pos {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) (hpos : 0 < len.toNat) :
    (currentLengthFreePtr len).toNat = 160 + 32 * ((len.toNat - 1) / 32) + 32 := by
  let q := (len.toNat - 1) / 32
  have h31 :
      (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
    rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    rw [Nat.add_comm 31 len.toNat]
    exact Nat.mod_eq_of_lt (by
      have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
        norm_num [UInt256.size]
      nlinarith)
  have hdivNat :
      (((⟨31⟩ : UInt256) + len) / ⟨32⟩).toNat = q + 1 := by
    change (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat = q + 1
    rw [udiv_toNat, h31, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    exact currentLengthCeilWords_eq hpos
  have hmulBound : (q + 1) * 32 < UInt256.size := by
    have hle : ((31 + len.toNat) / 32) * 32 ≤ 31 + len.toNat := by
      exact Nat.div_mul_le_self (31 + len.toNat) 32
    rw [currentLengthCeilWords_eq hpos] at hle
    have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
      norm_num [UInt256.size]
    change (((len.toNat - 1) / 32 + 1) * 32 < UInt256.size)
    nlinarith
  have hmulNat :
      ((((⟨31⟩ : UInt256) + len) / ⟨32⟩) * ⟨32⟩).toNat = (q + 1) * 32 := by
    simpa [hdivNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := (((⟨31⟩ : UInt256) + len) / ⟨32⟩))
        (b := (⟨32⟩ : UInt256)) (by simpa [hdivNat] using hmulBound)
  have halloc :
      (currentLengthAllocSize len).toNat = 32 + (q + 1) * 32 := by
    rw [currentLengthAllocSize]
    have hadd := uadd_lit32_toNat
      (a := ((((⟨31⟩ : UInt256) + len) / ⟨32⟩) * ⟨32⟩)) (by
        rw [hmulNat]
        have hfuel := currentLengthFuel_bound hlenLt
        dsimp [q] at hfuel ⊢
        omega)
    rw [hadd, hmulNat]
    omega
  rw [currentLengthFreePtr, uadd_toNat,
    show (⟨128⟩ : UInt256).toNat = 128 from by decide, halloc]
  have hmod :
      (128 + (32 + (q + 1) * 32)) % UInt256.size =
        128 + (32 + (q + 1) * 32) :=
    Nat.mod_eq_of_lt (by
      have hfuel := currentLengthFuel_bound hlenLt
      change 128 + (32 + ((len.toNat - 1) / 32 + 1) * 32) < UInt256.size
      omega)
  rw [hmod]
  change 128 + (32 + (((len.toNat - 1) / 32) + 1) * 32) =
    160 + 32 * ((len.toNat - 1) / 32) + 32
  omega

theorem currentLengthConcreteFuel_finalCopy_size_eq_freePtr
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    (currentLengthCopyMem
      (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).mem
      (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr
      (currentLengthStorageWord σ I
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).slot)).size =
      (currentLengthFreePtr len).toNat := by
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hadd32 := currentLengthConcreteFuel_add32
    (σ := σ) (I := I) (len := len) hlenLt
  have hsize :=
    currentLengthGeneratedFinalCopy_size_eq_ptr_add32_of_add32
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32) hadd32
  have hptr :
      (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat =
        160 + 32 * ((len.toNat - 1) / 32) :=
    currentLengthGeneratedLoopState_ptr_toNat_eq_of_bound
      (σ := σ) (I := I) (len := len) ((len.toNat - 1) / 32)
      (by
        have hfuel := currentLengthFuel_bound hlenLt
        omega)
  rw [hsize, hptr, currentLengthFreePtr_toNat_of_len_lt_sign_pos hlenLt (by omega)]

theorem currentLengthFreePtr_ge96_of_long {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    96 ≤ (currentLengthFreePtr len).toNat := by
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  rw [currentLengthFreePtr_toNat_of_len_lt_sign_pos hlenLt (by omega)]
  omega

theorem currentLengthFreePtr_add32_toNat_of_len_lt_sign_pos {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) (hpos : 0 < len.toNat) :
    (currentLengthFreePtr len + (⟨32⟩ : UInt256)).toNat =
      (currentLengthFreePtr len).toNat + 32 := by
  exact uadd_word_lit32_toNat (a := currentLengthFreePtr len) (by
    rw [currentLengthFreePtr_toNat_of_len_lt_sign_pos hlenLt hpos]
    have hdiv : 32 * ((len.toNat - 1) / 32) ≤ len.toNat - 1 := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (len.toNat - 1) 32
    have hsize : (2 : Nat) ^ 255 + 223 < UInt256.size := by
      norm_num [UInt256.size]
    omega)

theorem currentLengthFreePtr_retLen_of_len_lt_sign_pos {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) (hpos : 0 < len.toNat) :
    (UInt256.sub (currentLengthFreePtr len + ⟨32⟩) (currentLengthFreePtr len)).toNat = 32 := by
  have hadd := currentLengthFreePtr_add32_toNat_of_len_lt_sign_pos hlenLt hpos
  rw [usub_toNat (by rw [hadd]; omega)]
  rw [hadd]
  omega

theorem currentLengthFreePtr_add63_lt_size_of_len_lt_sign_pos {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255) (hpos : 0 < len.toNat) :
    (currentLengthFreePtr len).toNat + 32 + 31 < UInt256.size := by
  rw [currentLengthFreePtr_toNat_of_len_lt_sign_pos hlenLt hpos]
  have hdiv : 32 * ((len.toNat - 1) / 32) ≤ len.toNat - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (len.toNat - 1) 32
  have hsize : (2 : Nat) ^ 255 + 254 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem currentLengthConcreteWrapperStore_aw_mul32_lt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    (UInt256.ofNat
      (MachineState.M
        (UInt256.ofNat
          (MachineState.M
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
            32)).toNat
        (currentLengthFreePtr len).toNat 32)).toNat * 32 < UInt256.size := by
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hadd32 := currentLengthConcreteFuel_add32
    (σ := σ) (I := I) (len := len) hlenLt
  have hptrBound :
      (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat + 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
      hadd32 (currentLengthFuel_bound hlenLt)
  have hawStoreNoWrap :
      MachineState.M
          (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
          (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
          32 * 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
      hadd32 hptrBound
  exact machineState_M_word_mul32_lt_of_bounds
    (aw := UInt256.ofNat
      (MachineState.M
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
        32))
    (off := currentLengthFreePtr len) (len := (⟨32⟩ : UInt256))
    (by
      have hMSize :
          MachineState.M
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
              32 < UInt256.size := by
        have hle :
            MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32 ≤
              MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32 * 32 := by
          simpa using Nat.mul_le_mul_left
            (MachineState.M
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
              32) (by decide : 1 ≤ 32)
        exact lt_of_le_of_lt hle hawStoreNoWrap
      rw [ulit_toNat' _ hMSize]
      exact hawStoreNoWrap)
    (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
        currentLengthFreePtr_add63_lt_size_of_len_lt_sign_pos hlenLt (by omega))

theorem currentLengthConcreteWrapperStore_aw_ge3
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    3 ≤
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
              32)).toNat
          (currentLengthFreePtr len).toNat 32)).toNat := by
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hadd32 := currentLengthConcreteFuel_add32
    (σ := σ) (I := I) (len := len) hlenLt
  have hptrBound :
      (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat + 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
      hadd32 (currentLengthFuel_bound hlenLt)
  have hawStoreNoWrap :
      MachineState.M
          (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
          (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
          32 * 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
      hadd32 hptrBound
  have hawStoreGe5 :
      5 ≤
        (UInt256.ofNat
          (MachineState.M
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
            32)).toNat :=
    currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
      (σ := σ) (I := I) (len := len) (fuel := (len.toNat - 1) / 32)
      hawStoreNoWrap
  have hM2Size :
      MachineState.M
          (UInt256.ofNat
            (MachineState.M
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
              32)).toNat
          (currentLengthFreePtr len).toNat 32 < UInt256.size := by
    have hM2Mul :
        MachineState.M
            (UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32)).toNat
            (currentLengthFreePtr len).toNat 32 * 32 < UInt256.size :=
      machineState_M_mul32_lt_of_bounds
        (s := (UInt256.ofNat
          (MachineState.M
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
            (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
            32)).toNat)
        (f := (currentLengthFreePtr len).toNat) (l := 32)
        (by
          have hMSize :
              MachineState.M
                  (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                  (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                  32 < UInt256.size := by
            have hle :
                MachineState.M
                    (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                    (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                    32 ≤
                  MachineState.M
                    (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                    (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                    32 * 32 := by
              simpa using Nat.mul_le_mul_left
                (MachineState.M
                  (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                  (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                  32) (by decide : 1 ≤ 32)
            exact lt_of_le_of_lt hle hawStoreNoWrap
          rw [ulit_toNat' _ hMSize]
          exact hawStoreNoWrap)
        (by
          simpa using currentLengthFreePtr_add63_lt_size_of_len_lt_sign_pos hlenLt (by omega))
    have hle :
        MachineState.M
            (UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32)).toNat
            (currentLengthFreePtr len).toNat 32 ≤
          MachineState.M
            (UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32)).toNat
            (currentLengthFreePtr len).toNat 32 * 32 := by
      simpa using Nat.mul_le_mul_left
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32)).toNat
            (currentLengthFreePtr len).toNat 32) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hM2Mul
  rw [ulit_toNat' _ hM2Size]
  exact le_trans (by omega : 3 ≤
    (UInt256.ofNat
      (MachineState.M
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
        (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
        32)).toNat)
    (machineState_M_ge_left)

theorem currentLengthConcreteWrapperStore_aw64
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlenLt : len.toNat < 2 ^ 255)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ¬ (⟨64⟩ : UInt256) ≥
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
              (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
              32)).toNat
          (currentLengthFreePtr len).toNat 32)) * ⟨32⟩ := by
  have hNoWrap := currentLengthConcreteWrapperStore_aw_mul32_lt
    (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hge3 :
      3 ≤
        (UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).aw.toNat
                (currentLengthGeneratedLoopState σ I len ((len.toNat - 1) / 32)).ptr.toNat
                32)).toNat
            (currentLengthFreePtr len).toNat 32)).toNat :=
    currentLengthConcreteWrapperStore_aw_ge3
      (σ := σ) (I := I) (len := len) hlenLt hgt31
  exact wordMul32_not_le64_of_ge3 hge3 hNoWrap

theorem stringStoreLiteX_clearCurrentLongReachCopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨351⟩
      [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        ⟨153⟩, stringStoreLiteSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      [⟨160⟩, bytesLikeDataBase ⟨0⟩, (⟨160⟩ : UInt256) + len, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
      (currentLengthLongScratchMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd351⟩ := hreach
  have rd357 := evm_run rd351 with [jumpdest, dup1, iszero, push2 ⟨426⟩]
  have rd358 := rd357.jumpiNT (by decide) (isZero_eq_zero_of_ne hnonzero) (by evm_ov)
  have rd365 := evm_run rd358 with [dup1, push1 ⟨31⟩, lt, push2 ⟨385⟩]
  have rd385 := rd365.jumpiT (by decide) hgt31 (by jump_dest) (by evm_ov)
  have rd395 := evm_run rd385 with [
    jumpdest, dup3, add, swap2, swap1, push0,
    raw mstore 0 (currentLengthLongScratchMem len) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd396 := rd395.keccak256 0 (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 5)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
        List.getElem!_cons_zero, List.getElem!_cons_succ,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      native_decide)
    (currentLengthLongScratchMem_keccak0 len)
    (by decide)
    (by evm_ov)
  exact ⟨_, _, evm_run rd396 with [swap1]⟩

theorem stringStoreLiteX_clearCurrentLongFinalCopyToDelete {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore awLoad : UInt256} {m memout : ByteArray}
    {mstoreCost mloadCost : Nat}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
        stringStoreLiteSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) = ⟨0⟩)
    (hmemout :
      (currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hloadVal : (if (⟨128⟩ : UInt256).toNat ≥ memout.size
        ∨ (⟨128⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memout.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad : UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32) =
      awLoad) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, stringStoreLiteSelWord I]
      memout awLoad ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd397⟩ := hreach
  have rd399 := evm_run rd397 with [jumpdest, dup2]
  obtain ⟨_, _, rd400₀⟩ := rd399.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd400⟩ : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨400⟩
      [currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthStorageWord, initState] using rd400₀⟩
  have rd401 := evm_run rd400 with [dup2]
  have rd402 := rd401.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd416 := evm_run rd402 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨397⟩]
  have rd417 := rd416.jumpiNT (by decide) hdone (by evm_ov)
  have rd435 := evm_run rd417 with [
    dup3, swap1, sub, push1 ⟨31⟩, and, dup3, add, swap2,
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd436 := rd435.mload mloadCost len awLoad
    (by native_decide) hmloadCost hloadVal hawLoad (by evm_ov)
  exact ⟨_, _, evm_run rd436 with [
    swap2, pop, push0, push0, push2 ⟨449⟩, swap2, swap1, push2 ⟨453⟩,
    jump (by jump_dest)]⟩

theorem stringStoreLiteX_clearCurrentLongCopyContinue {cA gh bl σ σ₀ A I}
    {g : Sat256} {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
        stringStoreLiteSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) ≠ ⟨0⟩)
    (hmemout :
      (currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      [(⟨32⟩ : UInt256) + ptr, (⟨1⟩ : UInt256) + slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
      memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd397⟩ := hreach
  have rd399 := evm_run rd397 with [jumpdest, dup2]
  obtain ⟨_, _, rd400₀⟩ := rd399.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd400⟩ : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨400⟩
      [currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthStorageWord, initState] using rd400₀⟩
  have rd401 := evm_run rd400 with [dup2]
  have rd402 := rd401.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd416 := evm_run rd402 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨397⟩]
  have rd397' := rd416.jumpiT (by decide) hcontinue (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd397'⟩

theorem stringStoreLiteX_clearCurrentLongCopyLoopSchedule {cA gh bl σ σ₀ A I}
    {g : Sat256} {endp len : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : CurrentLengthLoopFinal σ I endp len (st fuel))
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      ((st 0).stack endp len I) (st 0).mem (st 0).aw ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, stringStoreLiteSelWord I]
      hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  induction fuel generalizing st with
  | zero =>
      simpa [CurrentLengthLoopState.stack] using
        stringStoreLiteX_clearCurrentLongFinalCopyToDelete
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp)
          (len := len) (aw := (st 0).aw) (m := (st 0).mem)
          (memout := hfinal.memout) (awStore := hfinal.awStore)
          (awLoad := hfinal.awLoad) (mstoreCost := hfinal.mstoreCost)
          (mloadCost := hfinal.mloadCost)
          hreach hfinal.hdone hfinal.hmemout hfinal.hmstoreCost
          hfinal.hawStore hfinal.hmloadCost hfinal.hloadVal hfinal.hawLoad
  | succ fuel ih =>
      have hs : CurrentLengthLoopStep σ I endp len (st 0) (st 1) := by
        simpa using hsteps 0 (Nat.zero_lt_succ fuel)
      have hnext₀ := stringStoreLiteX_clearCurrentLongCopyContinue
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp)
        (len := len) (aw := (st 0).aw) (m := (st 0).mem)
        (memout := (st 1).mem) (awStore := (st 1).aw)
        (mstoreCost := hs.mstoreCost)
        hreach hs.hcontinue hs.hmemout hs.hmstoreCost hs.hawStore
      have hnext : ∃ k C, RD stringStoreLiteBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨397⟩
          (((fun i => st i.succ) 0).stack endp len I)
          ((fun i => st i.succ) 0).mem ((fun i => st i.succ) 0).aw
          ByteArray.empty (cA, σ) k C := by
        obtain ⟨k, C, rd⟩ := hnext₀
        exact ⟨k, C, by
          simpa [CurrentLengthLoopState.stack, hs.hptrNext, hs.hslotNext] using rd⟩
      have hsteps' : ∀ i, i < fuel →
          CurrentLengthLoopStep σ I endp len ((fun j => st j.succ) i)
            ((fun j => st j.succ) (i + 1)) := by
        intro i hi
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          hsteps i.succ (Nat.succ_lt_succ hi)
      exact ih (fun i => st i.succ) hsteps' hfinal hnext

theorem stringStoreLiteX_clearCurrentLongReachDeleteWithSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hinit : st 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 })
    (hsteps : ∀ i, i < fuel →
      CurrentLengthLoopStep σ I ((⟨160⟩ : UInt256) + len) len (st i) (st (i + 1)))
    (hfinal :
      CurrentLengthLoopFinal σ I ((⟨160⟩ : UInt256) + len) len (st fuel)) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, stringStoreLiteSelWord I]
      hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  have hdecoded₀ := stringStoreLiteX_bytesLengthDecoderLongValid
    (hreach := stringStoreLiteX_clearCurrentReachDecoder hreach)
    (header := currentLengthHeaderWord σ I) (ret := ⟨307⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I])
    hflag hvalid
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd307₀⟩ := hdecoded₀
  obtain ⟨_, _, rd307⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨307⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd307₀⟩
  have rd330 := evm_run rd307 with [
    jumpdest, dup1, push1 ⟨31⟩, add, push1 ⟨32⟩, dup1, swap2, div, mul,
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd340 := evm_run rd330 with [
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, dup3]
  have rd343 := evm_run rd340 with [dup1]
  obtain ⟨_, _, rd343₀⟩ := rd343.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd343'⟩ : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨343⟩
      [currentLengthHeaderWord σ I, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd343₀⟩
  have hdecodedCopy := stringStoreLiteX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd343' with [
      push2 ⟨351⟩, swap1, push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨351⟩)
    (rest := [⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨153⟩,
      stringStoreLiteSelWord I])
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5)
    (rdata := ByteArray.empty)
    hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd351₀⟩ := hdecodedCopy
  obtain ⟨_, _, rd351⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨351⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨153⟩, stringStoreLiteSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd351₀⟩
  have hloop := stringStoreLiteX_clearCurrentLongReachCopyLoop
    (g := g) ⟨_, _, rd351⟩ hnonzero hgt31
  exact stringStoreLiteX_clearCurrentLongCopyLoopSchedule
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (endp := (⟨160⟩ : UInt256) + len) (len := len) fuel st
    hsteps hfinal (by
      simpa [CurrentLengthLoopState.stack, hinit] using hloop)

theorem stringStoreLiteX_clearCurrentLongReachDeleteGenerated
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    let fuel := (len.toNat - 1) / 32
    let awStore := UInt256.ofNat
      (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
        (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)
    let finalMloadCost :=
      Cₘ (UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
        Cₘ awStore
    let awLoad := UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32)
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, stringStoreLiteSelWord I]
      (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        (currentLengthConcreteFuel_done
          (σ := σ) (I := I) (len := len)
          (clearCurrent_len_toNat_lt_sign_of_div2 (header := currentLengthHeaderWord σ I) hlen)
          hgt31)
        (by
          intro st haw hstk
          simpa [finalMloadCost, awStore] using
            (mloadCostSpec
              (aw := awStore) (off := (⟨128⟩ : UInt256))
              (stk := [⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]) st haw hstk))
        (currentLengthConcreteFuel_finalMload128
          (σ := σ) (I := I) (len := len)
          (clearCurrent_len_toNat_lt_sign_of_div2 (header := currentLengthHeaderWord σ I) hlen))
        (by rfl)).memout
      (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        (currentLengthConcreteFuel_done
          (σ := σ) (I := I) (len := len)
          (clearCurrent_len_toNat_lt_sign_of_div2 (header := currentLengthHeaderWord σ I) hlen)
          hgt31)
        (by
          intro st haw hstk
          simpa [finalMloadCost, awStore] using
            (mloadCostSpec
              (aw := awStore) (off := (⟨128⟩ : UInt256))
              (stk := [⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]) st haw hstk))
        (currentLengthConcreteFuel_finalMload128
          (σ := σ) (I := I) (len := len)
          (clearCurrent_len_toNat_lt_sign_of_div2 (header := currentLengthHeaderWord σ I) hlen))
        (by rfl)).awLoad
      ByteArray.empty (cA, σ) k C := by
  dsimp only
  let fuel := (len.toNat - 1) / 32
  let awStore := UInt256.ofNat
    (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)
  let finalMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
      Cₘ awStore
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32)
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ I) hlen
  have hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_continue
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_done
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hmloadCost : ∀ st : State, st.machineState.activeWords = awStore →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = finalMloadCost := by
    intro st haw hstk
    simpa [finalMloadCost, awStore] using
      (mloadCostSpec
        (aw := awStore) (off := (⟨128⟩ : UInt256))
        (stk := [⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]) st haw hstk)
  have hloadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
    simpa [fuel, awStore] using
      currentLengthConcreteFuel_finalMload128
        (σ := σ) (I := I) (len := len) hlenLt
  have hawLoad :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32) = awLoad := by
    rfl
  exact stringStoreLiteX_clearCurrentLongReachDeleteWithSchedule
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) fuel (currentLengthGeneratedLoopState σ I len)
    hreach hflag hvalid hlen hnonzero hgt31
    currentLengthGeneratedLoopState_zero
    (currentLengthGeneratedLoopSteps
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) hcontinue)
    (currentLengthGeneratedLoopFinal
      (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
      hdone hmloadCost hloadVal hawLoad)

theorem stringStoreLiteX_clearCurrentReturnFromWrapperGeneric
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {len freePtr aw awLoad awStore awFinal : UInt256}
    {mem memret rdata : ByteArray}
    {mloadCost mstoreCost finalMloadCost retCost : Nat}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨153⟩
      [len, stringStoreLiteSelWord I] mem aw rdata (cA, τ) k C)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = [⟨64⟩, len, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      awLoad)
    (hmemret : len.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨763⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨166⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M awLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
      awStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = finalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        awFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = awFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreLiteSelWord I] →
      memoryExpansionCost s .RETURN = retCost) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, τ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd153⟩ := hreach
  have rd155 := evm_run rd153 with [jumpdest, push1 ⟨64⟩]
  have rd156 := rd155.mload mloadCost freePtr awLoad
    (by native_decide) hmloadCost hfreePtr hawLoad (by simp)
  have rd744 := evm_run rd156 with [
    push2 ⟨166⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763₀ := evm_run rd738 with [jumpdest, dup3]
  have rd764 := rd763₀.mstore mstoreCost memret awStore
    (by native_decide) hmstoreCost hmemret hawStore (by simp)
  have rd763 := evm_run rd764 with [pop, pop, jump (by jump_dest)]
  have rd166 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd168 := evm_run rd166 with [jumpdest, push1 ⟨64⟩]
  have rd169 := rd168.mload finalMloadCost freePtr awFinal
    (by native_decide) hfinalMloadCost hfinalFreePtr hawFinal (by simp)
  have rd172 := evm_run rd169 with [dup1, swap2, sub, swap1]
  exact rd172.ret retCost (UInt256.toByteArray len)
    (by native_decide) hretCost hretBytes (by evm_ov)

theorem activeWordsMstore0_eq_self {aw : UInt256} (hge : 1 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 32 = aw.toNat := by
    simp only [MachineState.M]
    have hceil : (0 + 32 + 31) / 32 = 1 := by decide
    rw [hceil]
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem clearCurrentBaseAw_eq_self_of_ge1 {aw : UInt256} (hge : 1 ≤ aw.toNat) :
    clearCurrentBaseAw aw = aw := by
  simpa [clearCurrentBaseAw] using activeWordsMstore0_eq_self (aw := aw) hge

theorem clearCurrentHashAw_eq_self_of_ge1 {aw : UInt256} (hge : 1 ≤ aw.toNat) :
    clearCurrentHashAw aw = aw := by
  have hbase : clearCurrentBaseAw aw = aw := clearCurrentBaseAw_eq_self_of_ge1 hge
  rw [clearCurrentHashAw, hbase]
  exact activeWordsMstore0_eq_self (aw := aw) hge

theorem clearCurrentBaseMemFrom_read64 {mem : ByteArray}
    (hsize : 96 ≤ mem.size) :
    (clearCurrentBaseMemFrom mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  rw [clearCurrentBaseMemFrom]
  exact write32_read_above (UInt256.toByteArray ⟨0⟩) mem 0 64
    (by rw [toByteArray_size])
    (by omega)
    (by decide)
    (by omega)

theorem clearCurrentBaseMemFrom_size_eq {mem : ByteArray}
    (hsize : 32 ≤ mem.size) :
    (clearCurrentBaseMemFrom mem).size = mem.size := by
  rw [clearCurrentBaseMemFrom,
    write32_eq (UInt256.toByteArray ⟨0⟩) mem 0
      (by rw [toByteArray_size]) (by omega)]
  have htail : (mem.extract (0 + 32) mem.size).size = mem.size - 32 := by
    rw [ByteArray.size_extract]
    omega
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, toByteArray_size, htail]
  omega

theorem stringStoreLiteX_clearCurrentLongValidGenerated {cA gh bl σ σ₀ A I}
    {g : Sat256} {len : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨145⟩ [stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, clearDataWordsForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
        clearCurrentBaseWord ⟨0⟩
        (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
      (UInt256.toByteArray len) := by
  let fuel := (len.toNat - 1) / 32
  let copyAwStore := UInt256.ofNat
    (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32)
  let copyMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
      Cₘ copyAwStore
  let copyAwLoad := UInt256.ofNat
    (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32)
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ I) hlen
  have hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_continue
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_done
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hcopyMloadCost : ∀ st : State, st.machineState.activeWords = copyAwStore →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost st .MLOAD = copyMloadCost := by
    intro st haw hstk
    simpa [copyMloadCost, copyAwStore] using
      (mloadCostSpec
        (aw := copyAwStore) (off := (⟨128⟩ : UInt256))
        (stk := [⟨128⟩, ⟨0⟩, ⟨153⟩, stringStoreLiteSelWord I]) st haw hstk)
  have hcopyLoadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ I len fuel).mem
            (currentLengthGeneratedLoopState σ I len fuel).ptr
            (currentLengthStorageWord σ I
              (currentLengthGeneratedLoopState σ I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥ copyAwStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ I len fuel).mem
              (currentLengthGeneratedLoopState σ I len fuel).ptr
              (currentLengthStorageWord σ I
                (currentLengthGeneratedLoopState σ I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
    simpa [fuel, copyAwStore] using
      currentLengthConcreteFuel_finalMload128
        (σ := σ) (I := I) (len := len) hlenLt
  have hcopyAwLoad :
      UInt256.ofNat (MachineState.M copyAwStore.toNat (⟨128⟩ : UInt256).toNat 32) =
        copyAwLoad := by
    rfl
  let copyFinal := currentLengthGeneratedLoopFinal
    (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
    (fuel := fuel) (finalMloadCost := copyMloadCost) (awLoad := copyAwLoad)
    hdone hcopyMloadCost hcopyLoadVal hcopyAwLoad
  have hreadStart : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨453⟩
      [⟨0⟩, ⟨0⟩, ⟨449⟩, ⟨128⟩, len, ⟨153⟩, stringStoreLiteSelWord I]
      copyFinal.memout copyFinal.awLoad ByteArray.empty (cA, σ) k C := by
    simpa [copyFinal, fuel, copyAwStore, copyMloadCost, copyAwLoad] using
      stringStoreLiteX_clearCurrentLongReachDeleteGenerated
        (g := g) (len := len) hreach hflag hvalid hlen hnonzero hgt31
  have hdelReach := stringStoreLiteX_clearCurrentDeleteLongValid
    (g := g) (len := len) (mem := copyFinal.memout) (aw := copyFinal.awLoad)
    hperm hreadStart hflag hvalid hlen hgt31
  have hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ I len i).ptr.toNat + 32) := by
    simpa [fuel] using
      currentLengthConcreteFuel_add32
        (σ := σ) (I := I) (len := len) hlenLt
  have hptrBound :
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat + 32 < UInt256.size := by
    simpa [fuel] using
      currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
        (σ := σ) (I := I) (len := len) (fuel := fuel)
        hadd32 (by simpa [fuel] using currentLengthFuel_bound hlenLt)
  have hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32 * 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ) (I := I) (len := len) (fuel := fuel) hadd32 hptrBound
  have hcopyAwLoadEq : copyFinal.awLoad = copyAwStore := by
    simpa [copyFinal, copyAwStore, copyAwLoad] using
      currentLengthGeneratedFinalCopy_mload128_aw_eq_awStore_of_mNoWrap
        (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hcopyAwGe5 : 5 ≤ copyFinal.awLoad.toNat := by
    rw [hcopyAwLoadEq]
    simpa [copyAwStore] using
      currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
        (σ := σ) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hdeleteAwEq : clearCurrentHashAw copyFinal.awLoad = copyFinal.awLoad :=
    clearCurrentHashAw_eq_self_of_ge1 (by omega : 1 ≤ copyFinal.awLoad.toNat)
  let deleteMem := clearCurrentBaseMemFrom copyFinal.memout
  let deleteAw := clearCurrentHashAw copyFinal.awLoad
  let freePtr := currentLengthFreePtr len
  have hcopyRead64 :
      copyFinal.memout.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [copyFinal, freePtr] using
      currentLengthGeneratedLoopFinal_read64_of_add32
        (σ := σ) (I := I) (len := len) (fuel := fuel)
        (finalMloadCost := copyMloadCost) (awLoad := copyAwLoad)
        hcontinue hdone hcopyMloadCost hcopyLoadVal hcopyAwLoad hadd32
  have hcopySize : copyFinal.memout.size = freePtr.toNat := by
    simpa [copyFinal, fuel, freePtr] using
      currentLengthConcreteFuel_finalCopy_size_eq_freePtr
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hfreeGe96 : 96 ≤ freePtr.toNat :=
    currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hdeleteRead64 : deleteMem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [deleteMem, hcopyRead64] using
      clearCurrentBaseMemFrom_read64 (mem := copyFinal.memout) (by omega)
  have hdeleteSize : deleteMem.size = copyFinal.memout.size := by
    simpa [deleteMem] using
      clearCurrentBaseMemFrom_size_eq (mem := copyFinal.memout) (by omega : 32 ≤ copyFinal.memout.size)
  have hcopyAwStoreNoWrap : copyAwStore.toNat * 32 < UInt256.size := by
    let m := MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
      (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32
    have hmSize : m < UInt256.size := by
      have hle : m ≤ m * 32 := by
        simpa using Nat.mul_le_mul_left m (by decide : 1 ≤ 32)
      exact lt_of_le_of_lt hle (by simpa [m] using hMNoWrap)
    simpa [copyAwStore, m, ulit_toNat' m hmSize] using hMNoWrap
  have hdeleteAwNoWrap : deleteAw.toNat * 32 < UInt256.size := by
    simpa [deleteAw, hdeleteAwEq, hcopyAwLoadEq] using hcopyAwStoreNoWrap
  have hdeleteAw64 : ¬ (⟨64⟩ : UInt256) ≥ deleteAw * ⟨32⟩ :=
    wordMul32_not_le64_of_ge3
      (by simpa [deleteAw, hdeleteAwEq] using (show 3 ≤ copyFinal.awLoad.toNat from by omega))
      hdeleteAwNoWrap
  have hfreePtrVal :
      (if (⟨64⟩ : UInt256).toNat ≥ deleteMem.size
          ∨ (⟨64⟩ : UInt256) ≥ deleteAw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (deleteMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact mloadWordValue_of_readWithPadding
      (mem := deleteMem) (aw := deleteAw) (off := (⟨64⟩ : UInt256)) (v := freePtr)
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hdeleteSize, hcopySize]; omega)
      hdeleteAw64
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hdeleteRead64)
  have hwrapperAwLoad :
      UInt256.ofNat (MachineState.M deleteAw.toNat (⟨64⟩ : UInt256).toNat 32) =
        deleteAw :=
    activeWordsMload64_eq_self
      (aw := deleteAw)
      (by simpa [deleteAw, hdeleteAwEq] using (show 3 ≤ copyFinal.awLoad.toNat from by omega))
  let wrapperMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M deleteAw.toNat (⟨64⟩ : UInt256).toNat 32)) -
      Cₘ deleteAw
  let wrapperAwStore := UInt256.ofNat (MachineState.M deleteAw.toNat freePtr.toNat 32)
  let wrapperMstoreCost := Cₘ wrapperAwStore - Cₘ deleteAw
  let returnMem := len.toByteArray.write 0 deleteMem (freePtr + ⟨0⟩).toNat 32
  have hreturnMem : len.toByteArray.write 0 deleteMem (freePtr + ⟨0⟩).toNat 32 = returnMem := rfl
  have hmstoreCost : ∀ s : State, s.machineState.activeWords = deleteAw →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨763⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨166⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MSTORE =
        wrapperMstoreCost := by
    intro s haw hstk
    simpa [wrapperMstoreCost, wrapperAwStore, currentLength_add_zero_toNat] using
      (mstoreCostSpec (aw := deleteAw) (off := freePtr + ⟨0⟩)
        (stk := [len, len, freePtr + ⟨0⟩, ⟨763⟩, freePtr + ⟨32⟩, freePtr, len,
          ⟨166⟩, stringStoreLiteSelWord I]) s haw hstk)
  have hwrapperAwStore :
      UInt256.ofNat (MachineState.M deleteAw.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore := by
    simp [wrapperAwStore, currentLength_add_zero_toNat]
  have hfreePtrLeMem : freePtr.toNat ≤ deleteMem.size := by
    rw [hdeleteSize, hcopySize]
  have hreturnRead64 : returnMem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [returnMem] using
      currentLengthReturnWrite_preserves_read64_zero
        (mem := deleteMem) (len := len) (freePtr := freePtr)
        hfreeGe96 hfreePtrLeMem hdeleteRead64
  have hreturnSizeGe64 : 64 < returnMem.size := by
    have hge := writeWord_size_gt64_of_mem
      (mem := deleteMem) (off := (freePtr + ⟨0⟩).toNat) (word := len)
      (by rw [hdeleteSize, hcopySize]; omega)
      (by simpa [currentLength_add_zero_toNat] using hfreePtrLeMem)
    simpa [returnMem] using hge
  have hwrapperAwStoreNoWrap :
      wrapperAwStore.toNat * 32 < UInt256.size := by
    simpa [wrapperAwStore, deleteAw, hdeleteAwEq, hcopyAwLoadEq, freePtr] using
      currentLengthConcreteWrapperStore_aw_mul32_lt
        (σ := σ) (I := I) (len := len) hlenLt hgt31
  have hwrapperAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ :=
    wordMul32_not_le64_of_ge3
      (by
        simpa [wrapperAwStore, deleteAw, hdeleteAwEq, hcopyAwLoadEq, freePtr] using
          currentLengthConcreteWrapperStore_aw_ge3
            (σ := σ) (I := I) (len := len) hlenLt hgt31)
      hwrapperAwStoreNoWrap
  have hfinalFreePtrVal :
      (if (⟨64⟩ : UInt256).toNat ≥ returnMem.size
          ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (returnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnMem) (aw := wrapperAwStore) (off := (⟨64⟩ : UInt256)) (v := freePtr)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnSizeGe64)
      hwrapperAw64
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let wrapperAwFinal := UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32)
  let wrapperFinalMloadCost := Cₘ wrapperAwFinal - Cₘ wrapperAwStore
  have hwrapperAwFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal := rfl
  have hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32 :=
    currentLengthFreePtr_retLen_of_len_lt_sign_pos
      (len := len) hlenLt (by
        have hgtNat : 31 < len.toNat := by
          simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
            ult_ne_zero_toNat_lt hgt31
        omega)
  have hretBytes :
      returnMem.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat =
          UInt256.toByteArray len := by
    simpa [returnMem] using
      currentLengthReturnWrite_retBytes
        (mem := deleteMem) (len := len) (freePtr := freePtr)
        hfreePtrLeMem hretLen
  let wrapperRetCost :=
    Cₘ (UInt256.ofNat (MachineState.M wrapperAwFinal.toNat freePtr.toNat
      (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat)) - Cₘ wrapperAwFinal
  have hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreLiteSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost := by
    intro s haw hstk
    simpa [wrapperRetCost] using
      (returnCostSpec
        (aw := wrapperAwFinal) (off := freePtr)
        (len := UInt256.sub (freePtr + ⟨32⟩) freePtr)
        (stk := [stringStoreLiteSelWord I]) s haw hstk)
  exact stringStoreLiteX_clearCurrentReturnFromWrapperGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g)
    (τ := clearDataWordsForwardFrom I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      clearCurrentBaseWord ⟨0⟩
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat)
    (len := len) (freePtr := freePtr) (aw := deleteAw) (awLoad := deleteAw)
    (awStore := wrapperAwStore) (awFinal := wrapperAwFinal)
    (mem := deleteMem) (memret := returnMem) (rdata := ByteArray.empty)
    (mloadCost := wrapperMloadCost)
    (mstoreCost := wrapperMstoreCost)
    (finalMloadCost := wrapperFinalMloadCost)
    (retCost := wrapperRetCost)
    (by simpa [deleteMem, deleteAw] using hdelReach)
    (by
      intro s haw hstk
      simpa [wrapperMloadCost] using
        (mloadCostSpec (aw := deleteAw) (off := (⟨64⟩ : UInt256))
          (stk := [len, stringStoreLiteSelWord I]) s haw hstk))
    hfreePtrVal
    hwrapperAwLoad
    hreturnMem
    hmstoreCost
    hwrapperAwStore
    (by
      intro s haw hstk
      simpa [wrapperFinalMloadCost, wrapperAwFinal] using
        (mloadCostSpec (aw := wrapperAwStore) (off := (⟨64⟩ : UInt256))
          (stk := [freePtr + ⟨32⟩, stringStoreLiteSelWord I]) s haw hstk))
    hfinalFreePtrVal
    hwrapperAwFinal
    hretBytes
    hretCost
