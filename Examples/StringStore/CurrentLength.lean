import Examples.StringStore.Getters

/-!
# StringStore — `currentLength()` long-string branch work

This module extends the getter proof with the valid long-string path.  It imports the completed
getter/shared facts but keeps new loop-heavy proof work out of `Getters.lean`, so iteration on the
remaining storage-copy loop does not force that module to re-elaborate.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

def currentLengthStorageWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

structure CurrentLengthLoopState where
  ptr : UInt256
  slot : UInt256
  mem : ByteArray
  aw : UInt256

def CurrentLengthLoopState.stack (s : CurrentLengthLoopState) (endp len : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [s.ptr, s.slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]

noncomputable def currentLengthLongScratchMem (len : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (currentLengthMem len) 0 32

noncomputable def currentLengthCopyMem (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  word.toByteArray.write 0 mem ptr.toNat 32

def currentLengthLoopMstoreStack (σ : AccountMap) (I : ExecutionEnv) (endp len : UInt256)
    (s : CurrentLengthLoopState) : List UInt256 :=
  [s.ptr, currentLengthStorageWord σ I s.slot, s.ptr, s.slot, endp, len, ⟨0⟩,
    ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]

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
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
    memoryExpansionCost st .MSTORE = mstoreCost
  hawStore : UInt256.ofNat (MachineState.M s.aw.toNat s.ptr.toNat 32) = awStore
  hmloadCost : ∀ st : State, st.machineState.activeWords = awStore →
    st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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

theorem stringStoreX_currentLengthLongReachCopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [currentLengthHeaderWord σ I, ⟨1954⟩, ⟨0⟩, ⟨160⟩, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
      [⟨160⟩, bytesLikeDataBase ⟨0⟩, (⟨160⟩ : UInt256) + len, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      (currentLengthLongScratchMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hdecoded := stringStoreX_bytesLengthDecoderLongValidMem
    (mem := currentLengthMem len) (aw := UInt256.ofNat 5) (rdata := ByteArray.empty)
    hreach hflag hvalid (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1954₀⟩ := hdecoded
  obtain ⟨_, _, rd1954⟩ :
      ∃ k C, RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1954⟩
        [len, ⟨0⟩, ⟨160⟩, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          ⟨420⟩, stringStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hlen] using rd1954₀⟩
  have rd1960 := evm_run rd1954 with [jumpdest, dup1, iszero, push2 ⟨2029⟩]
  have rd1961 := rd1960.jumpiNT (by decide) (isZero_eq_zero_of_ne hnonzero) (by evm_ov)
  have rd1968 := evm_run rd1961 with [dup1, push1 ⟨31⟩, lt, push2 ⟨1988⟩]
  have rd1988 := rd1968.jumpiT (by decide) hgt31 (by jump_dest) (by evm_ov)
  have rd1995 := evm_run rd1988 with [
    jumpdest, dup3, add, swap2, swap1, push0,
    raw mstore 0 (currentLengthLongScratchMem len) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have rd1999 := rd1995.keccak256 0 (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 5)
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
  exact ⟨_, _, evm_run rd1999 with [swap1]⟩

theorem stringStoreX_currentLengthLongFinalCopyToWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr slot endp len aw awStore awLoad : UInt256} {m memout : ByteArray}
    {mstoreCost mloadCost : Nat}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩,
        stringStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hdone : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) = ⟨0⟩)
    (hmemout :
      (currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hloadVal : (if (⟨128⟩ : UInt256).toNat ≥ memout.size
        ∨ (⟨128⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memout.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = len)
    (hawLoad : UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32) =
      awLoad) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I] memout awLoad ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2000⟩ := hreach
  have rd2002 := evm_run rd2000 with [jumpdest, dup2]
  obtain ⟨_, _, rd2003₀⟩ := rd2002.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2003⟩ : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2003⟩
      [currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthStorageWord, initState] using rd2003₀⟩
  have rd2004 := evm_run rd2003 with [dup2]
  have rd2005 := rd2004.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd2019 := evm_run rd2005 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨2000⟩]
  have rd2020 := rd2019.jumpiNT (by decide) hdone (by evm_ov)
  have rd2038 := evm_run rd2020 with [
    dup3, swap1, sub, push1 ⟨31⟩, and, dup3, add, swap2,
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, dup1]
  have rd2039 := rd2038.mload mloadCost len awLoad
    (by native_decide) hmloadCost hloadVal hawLoad (by evm_ov)
  exact ⟨_, _, evm_run rd2039 with [
    swap2, pop, pop, swap1, jump (by jump_dest)]⟩

theorem stringStoreX_currentLengthLongCopyContinue {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr slot endp len aw awStore : UInt256} {m memout : ByteArray}
    {mstoreCost : Nat}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
      [ptr, slot, endp, len, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩,
        stringStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C)
    (hcontinue : UInt256.gt endp ((⟨32⟩ : UInt256) + ptr) ≠ ⟨0⟩)
    (hmemout :
      (currentLengthStorageWord σ I slot).toByteArray.write 0 m ptr.toNat 32 = memout)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr, currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
          ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = awStore) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
      [(⟨32⟩ : UInt256) + ptr, (⟨1⟩ : UInt256) + slot, endp, len, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      memout awStore ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2000⟩ := hreach
  have rd2002 := evm_run rd2000 with [jumpdest, dup2]
  obtain ⟨_, _, rd2003₀⟩ := rd2002.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2003⟩ : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2003⟩
      [currentLengthStorageWord σ I slot, ptr, slot, endp, len, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      m aw ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthStorageWord, initState] using rd2003₀⟩
  have rd2004 := evm_run rd2003 with [dup2]
  have rd2005 := rd2004.mstore mstoreCost memout awStore
    (by native_decide) hmstoreCost hmemout hawStore (by evm_ov)
  have rd2019 := evm_run rd2005 with [
    swap1, push1 ⟨1⟩, add, swap1, push1 ⟨32⟩, add, dup1, dup4, gt, push2 ⟨2000⟩]
  have rd2000' := rd2019.jumpiT (by decide) hcontinue (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd2000'⟩

theorem stringStoreX_currentLengthLongCopyLoopSchedule {cA gh bl σ σ₀ A I} {g : Sat256}
    {endp len : UInt256} (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hsteps : ∀ i, i < fuel → CurrentLengthLoopStep σ I endp len (st i) (st (i + 1)))
    (hfinal : CurrentLengthLoopFinal σ I endp len (st fuel))
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
      ((st 0).stack endp len I) (st 0).mem (st 0).aw ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I] hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  induction fuel generalizing st with
  | zero =>
      simpa [CurrentLengthLoopState.stack] using
        stringStoreX_currentLengthLongFinalCopyToWrapper
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
      have hnext₀ := stringStoreX_currentLengthLongCopyContinue
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (ptr := (st 0).ptr) (slot := (st 0).slot) (endp := endp)
        (len := len) (aw := (st 0).aw) (m := (st 0).mem)
        (memout := (st 1).mem) (awStore := (st 1).aw)
        (mstoreCost := hs.mstoreCost)
        hreach hs.hcontinue hs.hmemout hs.hmstoreCost hs.hawStore
      have hnext : ∃ k C, RD stringStoreBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨2000⟩
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

theorem stringStoreX_currentLengthLongValidToWrapperWithSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
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
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I] hfinal.memout hfinal.awLoad ByteArray.empty (cA, σ) k C := by
  have hdecoded₀ := stringStoreX_currentLengthDecoderLongValid hreach hflag hvalid
  have hdecoded : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1910⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using hdecoded₀
  have hcopy := stringStoreX_currentLengthReachCopyDecoder hdecoded
  have hloop := stringStoreX_currentLengthLongReachCopyLoop
    (g := g) hcopy hflag hvalid hlen hnonzero hgt31
  exact stringStoreX_currentLengthLongCopyLoopSchedule
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (endp := (⟨160⟩ : UInt256) + len) (len := len) fuel st
    hsteps hfinal (by
      simpa [CurrentLengthLoopState.stack, hinit] using hloop)

theorem stringStoreX_currentLengthLongValidGeneratedToWrapper
    {cA gh bl σ σ₀ A I} {g : Sat256} {len awLoad : UInt256}
    {fuel finalMloadCost : Nat}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ I len fuel).ptr) = ⟨0⟩)
    (hmloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
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
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I]
      (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).memout
      (currentLengthGeneratedLoopFinal
        (σ := σ) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
        (fuel := fuel) (finalMloadCost := finalMloadCost) (awLoad := awLoad)
        hdone hmloadCost hloadVal hawLoad).awLoad
      ByteArray.empty (cA, σ) k C := by
  exact stringStoreX_currentLengthLongValidToWrapperWithSchedule
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

theorem stringStoreX_currentLengthReturnFromWrapperGeneric
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len freePtr aw awLoad awStore awFinal : UInt256}
    {mem memret : ByteArray}
    {mloadCost mstoreCost finalMloadCost retCost : Nat}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [len, stringStoreSelWord I] mem aw ByteArray.empty (cA, σ) k C)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
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
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M awLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
      awStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = finalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr)
    (hawFinal : UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) =
      awFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = awFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = retCost) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd420⟩ := hreach
  have rd422 := evm_run rd420 with [jumpdest, push1 ⟨64⟩]
  have rd423 := rd422.mload mloadCost freePtr awLoad
    (by native_decide) hmloadCost hfreePtr hawLoad (by simp)
  have rd2523 := evm_run rd423 with [
    push2 ⟨433⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542₀ := evm_run rd2517 with [jumpdest, dup3]
  have rd2543 := rd2542₀.mstore mstoreCost memret awStore
    (by native_decide) hmstoreCost hmemret hawStore (by simp)
  have rd2542 := evm_run rd2543 with [pop, pop, jump (by jump_dest)]
  have rd433 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd435 := evm_run rd433 with [jumpdest, push1 ⟨64⟩]
  have rd436 := rd435.mload finalMloadCost freePtr awFinal
    (by native_decide) hfinalMloadCost hfinalFreePtr hawFinal (by simp)
  have rd439 := evm_run rd436 with [dup1, swap2, sub, swap1]
  exact rd439.ret retCost (UInt256.toByteArray len)
    (by native_decide) hretCost hretBytes (by evm_ov)

theorem stringStoreX_currentLengthLongValidWithSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    {freePtr wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {memret : ByteArray}
    {wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost wrapperRetCost : Nat}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨412⟩ [stringStoreSelWord I]
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
      CurrentLengthLoopFinal σ I ((⟨160⟩ : UInt256) + len) len (st fuel))
    (hmloadCost : ∀ s : State, s.machineState.activeWords = hfinal.awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ hfinal.memout.size
        ∨ (⟨64⟩ : UInt256) ≥ hfinal.awLoad * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (hfinal.memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawLoad :
      UInt256.ofNat (MachineState.M hfinal.awLoad.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwLoad)
    (hmemret :
      len.toByteArray.write 0 hfinal.memout (freePtr + ⟨0⟩).toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray len) := by
  have htoWrapper := stringStoreX_currentLengthLongValidToWrapperWithSchedule
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) fuel st hreach hflag hvalid hlen hnonzero hgt31
    hinit hsteps hfinal
  exact stringStoreX_currentLengthReturnFromWrapperGeneric
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (freePtr := freePtr) (aw := hfinal.awLoad)
    (awLoad := wrapperAwLoad) (awStore := wrapperAwStore) (awFinal := wrapperAwFinal)
    (mem := hfinal.memout) (memret := memret)
    (mloadCost := wrapperMloadCost) (mstoreCost := wrapperMstoreCost)
    (finalMloadCost := wrapperFinalMloadCost) (retCost := wrapperRetCost)
    htoWrapper hmloadCost hfreePtr hawLoad hmemret hmstoreCost hawStore
    hfinalMloadCost hfinalFreePtr hawFinal hretBytes hretCost

theorem stringStoreCurrentLengthLongValidWithScheduleBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    {freePtr wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {memret : ByteArray}
    {wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost wrapperRetCost : Nat}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hcode : I.code = stringStoreBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hreach : ∃ k C, RD stringStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hinit : st 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 })
    (hsteps : ∀ i, i < fuel →
      CurrentLengthLoopStep σ_evm I ((⟨160⟩ : UInt256) + len) len (st i) (st (i + 1)))
    (hfinal :
      CurrentLengthLoopFinal σ_evm I ((⟨160⟩ : UInt256) + len) len (st fuel))
    (hmloadCost : ∀ s : State, s.machineState.activeWords = hfinal.awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ hfinal.memout.size
        ∨ (⟨64⟩ : UInt256) ≥ hfinal.awLoad * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (hfinal.memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawLoad :
      UInt256.ofNat (MachineState.M hfinal.awLoad.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwLoad)
    (hmemret :
      len.toByteArray.write 0 hfinal.memout (freePtr + ⟨0⟩).toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := currentLengthSelector_size hsel
  have hd := stringStoreDispatch_currentLength (cd := I.calldata) hsel'
  have hdec := stringStoreDecode_currentLength (I := I) hsz
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simp [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage,
      currentLengthHeaderWord, hslot]
  have hload' :
      Solm.EVM.storageLoad
        { (default : EVM.State) with
          accountMap := σ_solm
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          machineState.gasAvailable := .ofUInt256 g
          blocks := bl
          genesisBlockHeader := gh }
        I.codeOwner ⟨0⟩ = currentLengthHeaderWord σ_evm I := by
    simpa [initState] using hload
  have hvalidLen :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hlenRes :
      bytesLikeLength? stringStoreConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok len.toNat := by
    simp [bytesLikeLength?, stringStoreConfig, stringStoreStorageLayout,
      solidityReadBytesLength?, solidityDecodeBytesLengthHeader, stringStoreLayout, initState,
      hload', hflag, hvalidLen, ← hlen, pure]
  have hbody :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        currentLengthGetter.body
        (.returned { contract := stringStoreContract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat len.toNat)))) := by
    exact currentLengthBodyReturnsOfLength
      (by simp only [initState]; exact hwv) hlenRes
  exact (stringStoreX_currentLengthLongValidWithSchedule
      (g := Sat256.ofUInt256 g) fuel st hreach hflag hvalid hlen hnonzero hgt31
      hinit hsteps hfinal hmloadCost hfreePtr hawLoad hmemret hmstoreCost hawStore
      hfinalMloadCost hfinalFreePtr hawFinal hretBytes hretCost)
    |>.reEquivExecution hcode hd hdec hbody hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding len))

theorem stringStoreCurrentLengthLongValidWithScheduleRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    {freePtr wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {memret : ByteArray}
    {wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost wrapperRetCost : Nat}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hinit : st 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 })
    (hsteps : ∀ i, i < fuel →
      CurrentLengthLoopStep σ_evm I ((⟨160⟩ : UInt256) + len) len (st i) (st (i + 1)))
    (hfinal :
      CurrentLengthLoopFinal σ_evm I ((⟨160⟩ : UInt256) + len) len (st fuel))
    (hmloadCost : ∀ s : State, s.machineState.activeWords = hfinal.awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ hfinal.memout.size
        ∨ (⟨64⟩ : UInt256) ≥ hfinal.awLoad * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (hfinal.memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawLoad :
      UInt256.ofNat (MachineState.M hfinal.awLoad.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwLoad)
    (hmemret :
      len.toByteArray.write 0 hfinal.memout (freePtr + ⟨0⟩).toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthLongValidWithScheduleBodyCore
    (g := g) fuel st hcode hsize hperm hwv hsel
    (stringStoreReachCurrentLength (g := Sat256.ofUInt256 g) hcode hwv
      (currentLengthSelector_size hsel) hsize hsel)
    hAccounts hflag hvalid hlen hnonzero hgt31 hinit hsteps hfinal
    hmloadCost hfreePtr hawLoad hmemret hmstoreCost hawStore
    hfinalMloadCost hfinalFreePtr hawFinal hretBytes hretCost

theorem stringStoreCurrentLengthLongValidWithScheduleRuntimeFromMemoryFacts
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    {freePtr wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost wrapperRetCost : Nat}
    (fuel : Nat) (st : Nat → CurrentLengthLoopState)
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hinit : st 0 =
      { ptr := ⟨160⟩
        slot := bytesLikeDataBase ⟨0⟩
        mem := currentLengthLongScratchMem len
        aw := UInt256.ofNat 5 })
    (hsteps : ∀ i, i < fuel →
      CurrentLengthLoopStep σ_evm I ((⟨160⟩ : UInt256) + len) len (st i) (st (i + 1)))
    (hfinal :
      CurrentLengthLoopFinal σ_evm I ((⟨160⟩ : UInt256) + len) len (st fuel))
    (hmloadCost : ∀ s : State, s.machineState.activeWords = hfinal.awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfinalRead64 :
      hfinal.memout.readWithPadding 64 32 = UInt256.toByteArray freePtr)
    (hfinalSize64 : 64 < hfinal.memout.size)
    (hfinalAw64 : ¬ (⟨64⟩ : UInt256) ≥ hfinal.awLoad * ⟨32⟩)
    (hawLoad :
      UInt256.ofNat (MachineState.M hfinal.awLoad.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwLoad)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hfreePtrGe96 : 96 ≤ freePtr.toNat)
    (hfreePtrInMem : freePtr.toNat ≤ hfinal.memout.size)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hretMemSize64 :
      64 < (len.toByteArray.write 0 hfinal.memout (freePtr + ⟨0⟩).toNat 32).size)
    (hretAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let memret := len.toByteArray.write 0 hfinal.memout (freePtr + ⟨0⟩).toNat 32
  have hfreePtrVal :
      (if (⟨64⟩ : UInt256).toNat ≥ hfinal.memout.size
          ∨ (⟨64⟩ : UInt256) ≥ hfinal.awLoad * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (hfinal.memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr :=
    currentLength_mload64_of_read64 hfinalSize64 hfinalAw64 hfinalRead64
  have hretRead64 :
      memret.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [memret] using
      currentLengthReturnWrite_preserves_read64_zero
        (mem := hfinal.memout) (len := len) (freePtr := freePtr)
        hfreePtrGe96 hfreePtrInMem hfinalRead64
  have hfinalFreePtr :
      (if (⟨64⟩ : UInt256).toNat ≥ memret.size
          ∨ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact currentLength_mload64_of_read64
      (mem := memret) (aw := wrapperAwStore) (freePtr := freePtr)
      (by simpa [memret] using hretMemSize64) hretAw64 hretRead64
  have hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray len := by
    simpa [memret] using
      currentLengthReturnWrite_retBytes
        (mem := hfinal.memout) (len := len) (freePtr := freePtr)
        hfreePtrInMem hretLen
  exact stringStoreCurrentLengthLongValidWithScheduleRuntime
    (g := g) (len := len) (freePtr := freePtr) (wrapperAwLoad := wrapperAwLoad)
    (wrapperAwStore := wrapperAwStore) (wrapperAwFinal := wrapperAwFinal)
    (memret := memret) (wrapperMloadCost := wrapperMloadCost)
    (wrapperMstoreCost := wrapperMstoreCost)
    (wrapperFinalMloadCost := wrapperFinalMloadCost) (wrapperRetCost := wrapperRetCost)
    fuel st hcode hsize hperm hwv hsel hAccounts hflag hvalid hlen hnonzero hgt31
    hinit hsteps hfinal hmloadCost hfreePtrVal hawLoad rfl hmstoreCost hawStore
    hfinalMloadCost hfinalFreePtr hawFinal hretBytes hretCost

theorem stringStoreCurrentLengthLongValidGeneratedRuntimeFromMemoryFacts
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256}
    {freePtr generatedAwLoad wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {generatedFinalMloadCost wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost
      wrapperRetCost fuel : Nat}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ_evm I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ_evm I len fuel).ptr) = ⟨0⟩)
    (hgeneratedMloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost st .MLOAD = generatedFinalMloadCost)
    (hgeneratedLoadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ_evm I len fuel).mem
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
            (currentLengthStorageWord σ_evm I
              (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ_evm I len fuel).mem
              (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
              (currentLengthStorageWord σ_evm I
                (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hgeneratedAwLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = generatedAwLoad)
    (hmloadCost : ∀ s : State, s.machineState.activeWords =
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfinalRead64 :
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.readWithPadding
        64 32 = UInt256.toByteArray freePtr)
    (hfinalSize64 : 64 <
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size)
    (hfinalAw64 : ¬ (⟨64⟩ : UInt256) ≥
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad * ⟨32⟩)
    (hawLoad :
      UInt256.ofNat (MachineState.M
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad.toNat
        (⟨64⟩ : UInt256).toNat 32) = wrapperAwLoad)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hfreePtrGe96 : 96 ≤ freePtr.toNat)
    (hfreePtrInMem : freePtr.toNat ≤
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hretMemSize64 : 64 <
      (len.toByteArray.write 0
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout
        (freePtr + ⟨0⟩).toNat 32).size)
    (hretAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthLongValidWithScheduleRuntimeFromMemoryFacts
    (g := g) (len := len) (freePtr := freePtr) (wrapperAwLoad := wrapperAwLoad)
    (wrapperAwStore := wrapperAwStore) (wrapperAwFinal := wrapperAwFinal)
    (wrapperMloadCost := wrapperMloadCost) (wrapperMstoreCost := wrapperMstoreCost)
    (wrapperFinalMloadCost := wrapperFinalMloadCost) (wrapperRetCost := wrapperRetCost)
    fuel (currentLengthGeneratedLoopState σ_evm I len)
    hcode hsize hperm hwv hsel hAccounts hflag hvalid hlen hnonzero hgt31
    currentLengthGeneratedLoopState_zero
    (currentLengthGeneratedLoopSteps
      (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) hcontinue)
    (currentLengthGeneratedLoopFinal
      (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
      (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
      (awLoad := generatedAwLoad)
      hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad)
    hmloadCost hfinalRead64 hfinalSize64 hfinalAw64 hawLoad hmstoreCost hfreePtrGe96
    hfreePtrInMem hawStore hfinalMloadCost hretMemSize64 hretAw64 hawFinal hretLen hretCost

theorem stringStoreCurrentLengthLongValidGeneratedRuntimeFromAdd32
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len freePtr : UInt256}
    {generatedAwLoad wrapperAwLoad wrapperAwStore wrapperAwFinal : UInt256}
    {generatedFinalMloadCost wrapperMloadCost wrapperMstoreCost wrapperFinalMloadCost
      wrapperRetCost fuel : Nat}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hnonzero : len ≠ ⟨0⟩)
    (hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.gt ((⟨160⟩ : UInt256) + len)
        ((⟨32⟩ : UInt256) +
          (currentLengthGeneratedLoopState σ_evm I len i).ptr) ≠ ⟨0⟩)
    (hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ_evm I len fuel).ptr) = ⟨0⟩)
    (hgeneratedMloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost st .MLOAD = generatedFinalMloadCost)
    (hgeneratedLoadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ_evm I len fuel).mem
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
            (currentLengthStorageWord σ_evm I
              (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ_evm I len fuel).mem
              (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
              (currentLengthStorageWord σ_evm I
                (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len)
    (hgeneratedAwLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = generatedAwLoad)
    (hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ_evm I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ_evm I len i).ptr.toNat + 32))
    (hfreePtr : freePtr = currentLengthFreePtr len)
    (hmloadCost : ∀ s : State, s.machineState.activeWords =
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost)
    (hfinalSize64 : 64 <
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size)
    (hfinalAw64 : ¬ (⟨64⟩ : UInt256) ≥
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad * ⟨32⟩)
    (hawLoad :
      UInt256.ofNat (MachineState.M
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad.toNat
        (⟨64⟩ : UInt256).toNat 32) = wrapperAwLoad)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost)
    (hfreePtrGe96 : 96 ≤ freePtr.toNat)
    (hfreePtrInMem : freePtr.toNat ≤
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size)
    (hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost)
    (hretMemSize64 : 64 <
      (len.toByteArray.write 0
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout
        (freePtr + ⟨0⟩).toNat 32).size)
    (hretAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩)
    (hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal)
    (hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32)
    (hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthLongValidGeneratedRuntimeFromMemoryFacts
    (g := g) (len := len) (freePtr := freePtr) (wrapperAwLoad := wrapperAwLoad)
    (wrapperAwStore := wrapperAwStore) (wrapperAwFinal := wrapperAwFinal)
    (wrapperMloadCost := wrapperMloadCost) (wrapperMstoreCost := wrapperMstoreCost)
    (wrapperFinalMloadCost := wrapperFinalMloadCost) (wrapperRetCost := wrapperRetCost)
    hcode hsize hperm hwv hsel hAccounts hflag hvalid hlen hnonzero hgt31
    hcontinue hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad
    hmloadCost
    (by
      have hread := currentLengthGeneratedLoopFinal_read64_of_add32
        (σ := σ_evm) (I := I) (len := len) (fuel := fuel)
        (finalMloadCost := generatedFinalMloadCost) (awLoad := generatedAwLoad)
        hcontinue hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad hadd32
      simpa [hfreePtr] using hread)
    hfinalSize64 hfinalAw64 hawLoad hmstoreCost hfreePtrGe96 hfreePtrInMem hawStore
    hfinalMloadCost hretMemSize64 hretAw64 hawFinal hretLen hretCost

theorem stringStoreCurrentLengthLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let header := currentLengthHeaderWord σ_evm I
  let len := UInt256.div header ⟨2⟩
  let fuel := (len.toNat - 1) / 32
  let loopState := currentLengthGeneratedLoopState σ_evm I len fuel
  let awStore :=
    UInt256.ofNat (MachineState.M loopState.aw.toNat loopState.ptr.toNat 32)
  let generatedAwLoad := awStore
  let freePtr := currentLengthFreePtr len
  let wrapperAwLoad := awStore
  let wrapperAwStore :=
    UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32)
  let wrapperAwFinal := wrapperAwStore
  let generatedFinalMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M awStore.toNat (⟨128⟩ : UInt256).toNat 32)) -
      Cₘ awStore
  let wrapperMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)) -
      Cₘ awStore
  let wrapperMstoreCost :=
    Cₘ (UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32)) -
      Cₘ wrapperAwLoad
  let wrapperFinalMloadCost :=
    Cₘ (UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32)) -
      Cₘ wrapperAwStore
  let wrapperRetCost :=
    Cₘ (UInt256.ofNat
        (MachineState.M wrapperAwFinal.toNat freePtr.toNat
          (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat)) -
      Cₘ wrapperAwFinal
  have hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [len, header]
  have hvalidLen :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [len, header] using hvalid
  have hlenLt : len.toNat < 2 ^ 255 :=
    currentLength_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) (len := len) hlen
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    currentLengthLongValid_gt31
      (header := currentLengthHeaderWord σ_evm I) (len := len) hflag hvalidLen
  have hnonzero : len ≠ ⟨0⟩ :=
    currentLengthLongValid_nonzero
      (header := currentLengthHeaderWord σ_evm I) (len := len) hflag hvalidLen
  have hpos : 0 < len.toNat := by
    have hgtNat : 31 < len.toNat := by
      simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
        ult_ne_zero_toNat_lt hgt31
    omega
  have hcontinue :
      ∀ i, i < fuel →
        UInt256.gt ((⟨160⟩ : UInt256) + len)
          ((⟨32⟩ : UInt256) +
            (currentLengthGeneratedLoopState σ_evm I len i).ptr) ≠ ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_continue
        (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
  have hdone : UInt256.gt ((⟨160⟩ : UInt256) + len)
      ((⟨32⟩ : UInt256) +
        (currentLengthGeneratedLoopState σ_evm I len fuel).ptr) = ⟨0⟩ := by
    simpa [fuel] using
      currentLengthConcreteFuel_done
        (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
  have hadd32 : ∀ i, i ≤ fuel →
      (((⟨32⟩ : UInt256) + (currentLengthGeneratedLoopState σ_evm I len i).ptr).toNat =
        (currentLengthGeneratedLoopState σ_evm I len i).ptr.toNat + 32) := by
    simpa [fuel] using
      currentLengthConcreteFuel_add32
        (σ := σ_evm) (I := I) (len := len) hlenLt
  have hgeneratedLoadVal :
      (if (⟨128⟩ : UInt256).toNat ≥
          (currentLengthCopyMem
            (currentLengthGeneratedLoopState σ_evm I len fuel).mem
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
            (currentLengthStorageWord σ_evm I
              (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).size
          ∨ (⟨128⟩ : UInt256) ≥
            UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((currentLengthCopyMem
              (currentLengthGeneratedLoopState σ_evm I len fuel).mem
              (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
              (currentLengthStorageWord σ_evm I
                (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).readWithPadding
                (⟨128⟩ : UInt256).toNat 32))) = len := by
    simpa [fuel] using
      currentLengthConcreteFuel_finalMload128
        (σ := σ_evm) (I := I) (len := len) hlenLt
  have hptrBound :
      (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat + 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_ptrBound_of_fuelBound
      (σ := σ_evm) (I := I) (len := len) (fuel := fuel)
      hadd32 (by simpa [fuel] using currentLengthFuel_bound hlenLt)
  have hMNoWrap :
      MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
          (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32 * 32 <
        UInt256.size :=
    currentLengthGeneratedFinalCopy_mNoWrap_of_ptr_add32
      (σ := σ_evm) (I := I) (len := len) (fuel := fuel) hadd32 hptrBound
  have hgeneratedMloadCost : ∀ st : State,
      st.machineState.activeWords =
        UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32) →
      st.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I] →
      memoryExpansionCost st .MLOAD = generatedFinalMloadCost := by
    intro st haw hstk
    simpa [generatedFinalMloadCost, awStore, loopState] using
      (mloadCostSpec
        (aw := UInt256.ofNat
          (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
            (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32))
        (off := (⟨128⟩ : UInt256))
        (stk := [⟨128⟩, ⟨0⟩, ⟨420⟩, stringStoreSelWord I]) st haw hstk)
  have hgeneratedAwLoad :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat
              (MachineState.M (currentLengthGeneratedLoopState σ_evm I len fuel).aw.toNat
                (currentLengthGeneratedLoopState σ_evm I len fuel).ptr.toNat 32)).toNat
            (⟨128⟩ : UInt256).toNat 32) = generatedAwLoad := by
    simpa [generatedAwLoad, awStore, loopState] using
      currentLengthGeneratedFinalCopy_mload128_aw_eq_awStore_of_mNoWrap
        (σ := σ_evm) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hfinalSize64 : 64 <
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size := by
    change 64 <
      (currentLengthCopyMem
        (currentLengthGeneratedLoopState σ_evm I len fuel).mem
        (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
        (currentLengthStorageWord σ_evm I
          (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).size
    have hsz := currentLengthConcreteFuel_finalCopy_size_eq_freePtr
      (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
    have hge := currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
    rw [show fuel = (len.toNat - 1) / 32 from rfl, hsz]
    omega
  have hfinalAw64 : ¬ (⟨64⟩ : UInt256) ≥
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad * ⟨32⟩ := by
    simpa [currentLengthGeneratedLoopFinal, generatedAwLoad, awStore, loopState] using
      currentLengthGeneratedFinalCopy_aw64_of_mNoWrap
        (σ := σ_evm) (I := I) (len := len) (fuel := fuel) hMNoWrap
  have hawLoad :
      UInt256.ofNat (MachineState.M
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad.toNat
        (⟨64⟩ : UInt256).toNat 32) = wrapperAwLoad := by
    have hawStoreGe5 :
        5 ≤ awStore.toNat := by
      simpa [awStore, loopState] using
        currentLengthGeneratedFinalCopy_awStore_ge5_of_mNoWrap
          (σ := σ_evm) (I := I) (len := len) (fuel := fuel) hMNoWrap
    simpa [currentLengthGeneratedLoopFinal, generatedAwLoad, wrapperAwLoad] using
      activeWordsMload64_eq_self (aw := awStore) (by omega)
  have hmloadCost : ∀ s : State, s.machineState.activeWords =
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).awLoad →
      s.machineState.stack = [⟨64⟩, len, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperMloadCost := by
    intro st haw hstk
    simpa [wrapperMloadCost, currentLengthGeneratedLoopFinal, generatedAwLoad,
      wrapperAwLoad, awStore] using
      (mloadCostSpec (aw := awStore) (off := (⟨64⟩ : UInt256))
        (stk := [len, stringStoreSelWord I]) st (by simpa [currentLengthGeneratedLoopFinal,
          generatedAwLoad, awStore] using haw) hstk)
  have hmstoreCost : ∀ s : State, s.machineState.activeWords = wrapperAwLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, len, ⟨433⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = wrapperMstoreCost := by
    intro st haw hstk
    simpa [wrapperMstoreCost, wrapperAwLoad] using
      (mstoreCostSpec (aw := wrapperAwLoad) (off := freePtr + ⟨0⟩)
        (stk := [len, len, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩, freePtr, len,
          ⟨433⟩, stringStoreSelWord I]) st haw hstk)
  have hfreePtrGe96 : 96 ≤ freePtr.toNat := by
    simpa [freePtr] using currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hfreePtrInMem : freePtr.toNat ≤
      (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size := by
    change freePtr.toNat ≤
      (currentLengthCopyMem
        (currentLengthGeneratedLoopState σ_evm I len fuel).mem
        (currentLengthGeneratedLoopState σ_evm I len fuel).ptr
        (currentLengthStorageWord σ_evm I
          (currentLengthGeneratedLoopState σ_evm I len fuel).slot)).size
    have hsz := currentLengthConcreteFuel_finalCopy_size_eq_freePtr
      (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
    rw [show fuel = (len.toNat - 1) / 32 from rfl, hsz]
  have hawStore :
      UInt256.ofNat (MachineState.M wrapperAwLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
        wrapperAwStore := rfl
  have hfinalMloadCost : ∀ s : State, s.machineState.activeWords = wrapperAwStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = wrapperFinalMloadCost := by
    intro st haw hstk
    simpa [wrapperFinalMloadCost] using
      (mloadCostSpec (aw := wrapperAwStore) (off := (⟨64⟩ : UInt256))
        (stk := [freePtr + ⟨32⟩, stringStoreSelWord I]) st haw hstk)
  have hretMemSize64 : 64 <
      (len.toByteArray.write 0
        (currentLengthGeneratedLoopFinal
          (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
          (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
          (awLoad := generatedAwLoad)
          hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout
        (freePtr + ⟨0⟩).toNat 32).size := by
    have hfreePtrInMem0 :
        (freePtr + ⟨0⟩).toNat ≤
          (currentLengthGeneratedLoopFinal
            (σ := σ_evm) (I := I) (endp := (⟨160⟩ : UInt256) + len) (len := len)
            (fuel := fuel) (finalMloadCost := generatedFinalMloadCost)
            (awLoad := generatedAwLoad)
            hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad).memout.size := by
      simpa [currentLength_add_zero_toNat] using hfreePtrInMem
    exact writeWord_size_gt64_of_mem hfinalSize64 hfreePtrInMem0
  have hretAw64 : ¬ (⟨64⟩ : UInt256) ≥ wrapperAwStore * ⟨32⟩ := by
    simpa [wrapperAwStore, wrapperAwLoad, awStore, loopState, freePtr,
      currentLength_add_zero_toNat] using
      currentLengthConcreteWrapperStore_aw64
        (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
  have hawFinal :
      UInt256.ofNat (MachineState.M wrapperAwStore.toNat (⟨64⟩ : UInt256).toNat 32) =
        wrapperAwFinal := by
    have hge3 : 3 ≤ wrapperAwStore.toNat := by
      simpa [wrapperAwStore, wrapperAwLoad, awStore, loopState, freePtr,
        currentLength_add_zero_toNat] using
        currentLengthConcreteWrapperStore_aw_ge3
          (σ := σ_evm) (I := I) (len := len) hlenLt hgt31
    simpa [wrapperAwFinal] using
      activeWordsMload64_eq_self (aw := wrapperAwStore) hge3
  have hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32 := by
    simpa [freePtr] using currentLengthFreePtr_retLen_of_len_lt_sign_pos
      (len := len) hlenLt hpos
  have hretCost : ∀ s : State, s.machineState.activeWords = wrapperAwFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = wrapperRetCost := by
    intro st haw hstk
    simpa [wrapperRetCost, wrapperAwFinal] using
      (returnCostSpec (aw := wrapperAwFinal) (off := freePtr)
        (len := UInt256.sub (freePtr + ⟨32⟩) freePtr)
        (stk := [stringStoreSelWord I]) st haw hstk)
  exact stringStoreCurrentLengthLongValidGeneratedRuntimeFromAdd32
    (g := g) (len := len) (freePtr := freePtr)
    (generatedAwLoad := generatedAwLoad) (wrapperAwLoad := wrapperAwLoad)
    (wrapperAwStore := wrapperAwStore) (wrapperAwFinal := wrapperAwFinal)
    (generatedFinalMloadCost := generatedFinalMloadCost)
    (wrapperMloadCost := wrapperMloadCost) (wrapperMstoreCost := wrapperMstoreCost)
    (wrapperFinalMloadCost := wrapperFinalMloadCost) (wrapperRetCost := wrapperRetCost)
    (fuel := fuel)
    hcode hsize hperm hwv hsel hAccounts hflag hvalid hlen hnonzero hgt31
    hcontinue hdone hgeneratedMloadCost hgeneratedLoadVal hgeneratedAwLoad hadd32
    (by simp [freePtr])
    hmloadCost hfinalSize64 hfinalAw64 hawLoad hmstoreCost hfreePtrGe96 hfreePtrInMem
    hawStore hfinalMloadCost hretMemSize64 hretAw64 hawFinal hretLen hretCost

theorem stringStoreCurrentLengthRuntime_of_longValid
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlongValid : ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
      I.code = stringStoreBytecode →
      I.calldata.size < UInt256.size →
      I.perm = true →
      I.weiValue = ⟨0⟩ →
      selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ →
      accountMapEquiv σ_evm σ_solm →
      UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ →
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ →
      runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
        σ_evm σ_solm σ₀ g A I) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · by_cases hzero :
          UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩ = ⟨0⟩
      · exact stringStoreCurrentLengthShortZeroValidRuntime
          hcode hsize hperm hwv hsel hAccounts hflag hvalid hzero
      · exact stringStoreCurrentLengthShortNonzeroValidRuntime
          (len := UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          hcode hsize hperm hwv hsel hAccounts hflag hvalid rfl hzero
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreCurrentLengthShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact hlongValid hcode hsize hperm hwv hsel hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreCurrentLengthLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hflag hbad

theorem stringStoreCurrentLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreCurrentLengthRuntime_of_longValid
    hcode hsize hperm hwv hsel hAccounts stringStoreCurrentLengthLongValidRuntime

end StringStore
