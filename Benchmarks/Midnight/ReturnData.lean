import Benchmarks.Midnight.AllocationArithmetic

/-! The shared return-data extraction routine at PC 22728. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def returnDataAllocation (size : Nat) : Nat := (size + 63) / 32 * 32

def returnDataPtr (ptr : UInt256) (size : Nat) : UInt256 :=
  ptr + UInt256.ofNat (returnDataAllocation size)

def returnDataMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  out.write 0 (writeWord (writeWord mem 64 (returnDataPtr ptr out.size)) ptr.toNat
    (UInt256.ofNat out.size)) (ptr.toNat + 32) out.size

theorem returnDataAllocation_word {size : Nat} (hb : size + 94 < UInt256.size) :
    UInt256.ofNat 32 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat 31 + UInt256.ofNat size) = UInt256.ofNat (returnDataAllocation size) := by
  rw [u256_land_comm, u256_add_comm (UInt256.ofNat 31),
    u256_add_comm (UInt256.ofNat 32)]
  have hr : (UInt256.land (UInt256.ofNat size + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31))).toNat = (size + 31) / 32 * 32 := by
    change (UInt256.land (UInt256.ofNat size + UInt256.ofNat 31) (UInt256.lnot ⟨31⟩)).toNat = _
    rw [longDataCutoff_toNat, uadd_word_ofNat_toNat _ 31 (by
      rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega), UInt256.toNat_ofNat_of_lt (by omega)]
  apply u256_inj
  rw [uadd_word_ofNat_toNat _ 32 (by rw [hr]; omega), hr,
    UInt256.toNat_ofNat_of_lt (by dsimp [returnDataAllocation]; omega)]
  dsimp [returnDataAllocation]
  omega

theorem returnDataAllocation_end {ptr : UInt256} {size : Nat}
    (hfit : ptr.toNat + returnDataAllocation size < 2 ^ 64) :
    allocationEnd ptr (UInt256.ofNat (returnDataAllocation size)) = returnDataPtr ptr size := by
  apply u256_inj
  have hs : returnDataAllocation size < UInt256.size := by change _ < 2 ^ 256; omega
  have hr : (returnDataAllocation size + 31) / 32 * 32 = returnDataAllocation size := by
    dsimp only [returnDataAllocation]
    omega
  rw [allocationEnd_toNat (by rw [UInt256.toNat_ofNat_of_lt hs]; change _ < 2 ^ 256; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hs, hr]; change _ < 2 ^ 256; omega),
    UInt256.toNat_ofNat_of_lt hs, hr, returnDataPtr,
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)]

theorem midnightReturnDataEmptyCharge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hout : out.size = 0) (hstack : R.length + 3 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ k' C', MemoryCharge 0 aw aw C C' ∧ RD midnightBytecode I g s0 ret (UInt256.ofNat 96 :: R) mem aw out σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_22728_taken
    (by simp only [List.length_cons]; omega) (by rw [hout]; decide) (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_22770 (by omega) hret rd1
  have h0 := MemoryCharge.refl aw C
  have hc2 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd2 (by memory_charge h0)
  exact ⟨_, _, hc2, rd2⟩

theorem midnightReturnDataEmpty {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hout : out.size = 0) (hstack : R.length + 3 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.ofNat 96 :: R) mem aw out σ k' C' := by
  obtain ⟨k', C', _, rd'⟩ := midnightReturnDataEmptyCharge hout hstack hret rd
  exact ⟨k', C', rd'⟩

theorem midnightReturnDataOversize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hsize : out.size < UInt256.size) (hb : 2 ^ 64 ≤ out.size) (hstack : R.length + 7 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    RDrev midnightBytecode g s0 := by
  have hn : UInt256.ofNat out.size ≠ (⟨0⟩ : UInt256) := by
    intro he
    have hn := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt hsize] at hn
    change out.size = 0 at hn
    omega
  have rd1 := midnightBlocks.midnight_block_22728_fallthrough
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
  have rd2 := midnightBlocks.midnight_block_22735 (by omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_22735_stack] at rd2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hlarge : UInt256.gt (UInt256.ofNat out.size) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨1⟩ := by
    apply ugt_one
    rw [UInt256.toNat_ofNat_of_lt hsize]
    change 18446744073709551615 < out.size
    omega
  have rd3 := midnightBlocks.midnight_block_19016_taken
    (by simp only [List.length_cons]; omega)
    (by rw [hmask, hlarge]; decide)
    (by jump_dest) rd2
  exact midnightBlocks.midnight_block_15087 (by simp only [List.length_cons]; omega) rd3

theorem midnightReturnDataPrepareCharge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 7 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', MemoryCharge (0) aw aw' C C' ∧ RD midnightBytecode I g s0 ⟨18444⟩
      (ptr :: UInt256.ofNat (returnDataAllocation out.size) :: UInt256.ofNat 22759 ::
        UInt256.ofNat out.size :: ret :: ptr :: R) mem aw' out σ k' C' := by
  have hsize : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hnw : UInt256.ofNat out.size ≠ (⟨0⟩ : UInt256) := by
    intro he
    have he := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt hsize] at he
    exact hn he
  have rd1 := midnightBlocks.midnight_block_22728_fallthrough
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnw) rd
  have rd2 := midnightBlocks.midnight_block_22735 (by omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_22735_stack] at rd2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hsmall : UInt256.gt (UInt256.ofNat out.size) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hsize]
    change out.size ≤ 18446744073709551615
    omega
  have rd3 := midnightBlocks.midnight_block_19016_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hmask, hsmall]; rfl) rd2
  have rd4 := midnightBlocks.midnight_block_19031
    (by simp only [List.length_cons]; omega) (by jump_dest) rd3
  simp only [midnightBlocks.midnight_block_19031_stack,
    returnDataAllocation_word (by change out.size + 94 < 2 ^ 256; omega)] at rd4
  have rd5 := midnightBlocks.midnight_block_22745 (by omega) (by jump_dest) rd4
  simp only [midnightBlocks.midnight_block_22745_stack, hfree] at rd5
  have h0 := MemoryCharge.refl aw C
  have hc5 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd5 (by memory_charge h0)
  exact ⟨_, _, _, hc5, rd5⟩

theorem midnightReturnDataPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 7 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨18444⟩
      (ptr :: UInt256.ofNat (returnDataAllocation out.size) :: UInt256.ofNat 22759 ::
        UInt256.ofNat out.size :: ret :: ptr :: R) mem aw' out σ k' C' := by
  obtain ⟨aw', k', C', _, rd'⟩ := midnightReturnDataPrepareCharge hb hn hfree hstack rd
  exact ⟨aw', k', C', rd'⟩

theorem midnightReturnDataCopyCharge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 9 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hfit : ptr.toNat + returnDataAllocation out.size < 2 ^ 64)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', MemoryCharge (3 * ((out.size + 31) / 32)) aw aw' C C' ∧
      (96 ≤ mem.size → MemoryCovered mem aw → MemoryCovered (returnDataMem mem out ptr) aw') ∧
      RD midnightBytecode I g s0 ret (ptr :: R)
      (returnDataMem mem out ptr) aw' out σ k' C' := by
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := midnightReturnDataPrepareCharge hb hn hfree (by omega) rd
  have hend := returnDataAllocation_end hfit
  have hp := uadd_word_ofNat_toNat ptr (returnDataAllocation out.size)
    (by change _ < 2 ^ 256; omega)
  have hc : allocationCheck ptr (allocationEnd ptr (UInt256.ofNat (returnDataAllocation out.size))) =
      ⟨0⟩ := by
    rw [hend]
    apply allocationCheck_ok
    · rw [returnDataPtr, hp]; exact hfit
    · rw [returnDataPtr, hp]; omega
  obtain ⟨aw2, k2, C2, hc2, rd2⟩ := midnightAllocateCharge (by simp only [List.length_cons]; omega)
    hc (by jump_dest) rd1
  have hsize : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have rd3 := midnightBlocks.midnight_block_22759 (by omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; change 0 + out.size ≤ out.size; omega) hret rd2
  have hc12 := hc1.trans hc2
  have hc3 := memoryChargeAt (work := 3 * ((out.size + 31) / 32))
    (aw₀ := aw) (C₀ := C) rd3 (by
      simp only [UInt256.toNat_ofNat_of_lt hsize]
      memory_charge hc12)
  have hadd : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; dsimp [returnDataAllocation] at hfit; omega)
  simp only [midnightBlocks.midnight_block_22759_stack,
    midnightBlocks.midnight_block_22759_memory, hend, UInt256.toNat_ofNat_of_lt hsize, hadd] at rd3 hc3
  refine ⟨_, _, _, hc3, ?_, rd3⟩
  intro hm ha
  have hbase : MemoryCovered (writeWord mem 64 (returnDataPtr ptr out.size)) aw2 := by
    have hcover := ha.mono hc12.active_le
    unfold MemoryCovered at hcover ⊢
    rw [writeWord_sparse_size]
    omega
  have hfinal := (hbase.write32 (UInt256.ofNat out.size).toByteArray 0 ptr).write
    out 0 (ptr + UInt256.ofNat 32) (UInt256.ofNat out.size)
  simpa only [returnDataMem, Reasoning.Theory.writeWord,
    UInt256.toNat_ofNat_of_lt hsize, hadd] using hfinal

theorem midnightReturnDataCopy {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hstack : R.length + 9 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hfit : ptr.toNat + returnDataAllocation out.size < 2 ^ 64)
    (rd : RD midnightBytecode I g s0 ⟨22728⟩ (ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ret (ptr :: R)
      (returnDataMem mem out ptr) aw' out σ k' C' := by
  obtain ⟨aw', k', C', _, _, rd'⟩ := midnightReturnDataCopyCharge hb hn hfree hstack hret hfit rd
  exact ⟨aw', k', C', rd'⟩

end Benchmarks.Midnight
