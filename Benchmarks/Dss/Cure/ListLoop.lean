import Benchmarks.Dss.Cure.ListBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

set_option maxHeartbeats 1000000 in
theorem cureListNonemptyToLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (h929 : ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨929⟩
      [⟨369⟩, cureSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hlen_ne : cureSlotWord ⟨2⟩ σ I ≠ ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨987⟩
      (listArrayDataPtr :: srcsDataSlot :: listArrayEndPtr (cureSlotWord ⟨2⟩ σ I) ::
        cureSlotWord ⟨2⟩ σ I :: (⟨2⟩ : UInt256) :: listArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ⟨369⟩ :: cureSelWord I :: [])
      (listArrayHashMem (cureSlotWord ⟨2⟩ σ I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h929⟩ := h929
  obtain ⟨_, _, h936raw⟩ :=
    (evm_run h929 with [jumpdest, push1 ⟨96⟩, push1 ⟨2⟩, dup1]).sload
      (by decide +native) (by evm_ov)
  obtain ⟨_, _, h936⟩ : ∃ k C, RD cureBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨936⟩
      [cureSlotWord ⟨2⟩ σ I, ⟨2⟩, ⟨96⟩, ⟨369⟩, cureSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [cureSlotWord, initState] using h936raw⟩
  let len := cureSlotWord ⟨2⟩ σ I
  have h963 := evm_run h936 with [
    dup1, push1 ⟨32⟩, mul, push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (listArrayAllocMem len) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (listRoutineMem len) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, add, dup3, dup1]
  obtain ⟨_, _, h965raw⟩ := h963.sload (by decide +native) (by evm_ov)
  have hload :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        len := by
    simp [len, cureSlotWord, solcSlotWord]
  have h965 := by
    simpa [initState, hload, len] using h965raw
  have hcond : UInt256.isZero (cureSlotWord ⟨2⟩ σ I) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hlen_ne
  have h966 := h965.dup1 (by decide +native) (by evm_ov)
  have h967raw := h966.iszero (by decide +native) (by evm_ov)
  have h967 := by
    simpa [len, hcond] using h967raw
  have h970 := h967.push2 ⟨1017⟩ (by decide +native) (by evm_ov)
  have h971 := h970.jumpiNT (by decide +native) rfl (by evm_ov)
  have h986 := evm_run h971 with [
    push1 ⟨32⟩, mul, dup3, add, swap2, swap1, push1 ⟨0⟩,
    raw mstore 0 (listArrayHashMem len) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨0⟩,
    raw keccak256 0 srcsDataSlot (UInt256.ofNat 5) (by decide +native)
      mem_cost (listArrayHashMem_keccak_slot len) (by decide +native) (by evm_ov),
    swap1]
  exact ⟨_, _, by
    simpa [len, listArrayDataPtr, listArrayEndPtr] using h986⟩

set_option maxHeartbeats 1000000 in
theorem cureListArrayLoopStepToBranch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 (⟨987⟩ : UInt256) (dest :: slot :: endp :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 (⟨1016⟩ : UInt256)
      ((⟨987⟩ : UInt256) :: UInt256.gt endp ((⟨32⟩ : UInt256) + dest) ::
        ((⟨32⟩ : UInt256) + dest) :: ((⟨1⟩ : UInt256) + slot) :: endp :: R)
      (listArrayCopyStepMem σ ee slot dest mem) (listArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  have hmaskLiteral :
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        solcAddrMask := by
    decide +native
  have rd988 := h.jumpdest (by decide +native) (by evm_ov)
  have rd989 := rd988.dup2 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd990raw⟩ := rd989.sload (by decide +native) (by evm_ov)
  have rd990 := by
    simpa [solcSlotWord] using rd990raw
  have rd992 := rd990.push1 ⟨1⟩ (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd994 := rd992.push1 ⟨1⟩ (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd996 := rd994.push1 ⟨160⟩ (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd997 := rd996.shl (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd998 := rd997.sub (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd999raw := rd998.and (by decide +native)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd999⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨999⟩
      (UInt256.land (solcSlotWord σ ee slot) solcAddrMask :: dest :: slot :: endp :: R)
      mem aw rdata (cA, σ) k' C' :=
    ⟨_, _, by simpa [solcSlotWord, hmaskLiteral, u256_land_comm] using rd999raw⟩
  have rd1000 := rd999.dup2 (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rd1001 := rd1000.mstore (Cₘ (listArrayCopyStepAw aw dest) - Cₘ aw)
    (listArrayCopyStepMem σ ee slot dest mem) (listArrayCopyStepAw aw dest)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := aw) (off := dest)
        (val := UInt256.land (solcSlotWord σ ee slot) solcAddrMask)
        (t := dest :: slot :: endp :: R) haw hstk (by rfl))
    (by
      unfold listArrayCopyStepMem
      rfl)
    (by rfl) (by evm_ov)
  have rd1016 := evm_run rd1001 with [
    push1 ⟨1⟩, swap1, swap2, add, swap1, push1 ⟨32⟩, add,
    dup1, dup4, gt, push2 ⟨987⟩]
  exact ⟨_, _, by
    simpa [listArrayCopyStepMem, listArrayCopyStepAw, u256_add_comm slot (⟨1⟩ : UInt256)]
      using rd1016⟩

theorem cureListArrayCleanup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b c d e base ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 (⟨1017⟩ : UInt256)
      (a :: b :: c :: d :: e :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret (base :: R) mem aw rdata acc k' C' := by
  have rd1018 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1019 := rd1018.pop (by decide +native) (by evm_ov)
  have rd1020 := rd1019.pop (by decide +native) (by evm_ov)
  have rd1021 := rd1020.pop (by decide +native) (by evm_ov)
  have rd1022 := rd1021.pop (by decide +native) (by evm_ov)
  have rd1023 := rd1022.pop (by decide +native) (by evm_ov)
  have rd1024 := rd1023.swap1 (by decide +native) (by evm_ov)
  have rd1025 := rd1024.pop (by decide +native) (by evm_ov)
  have rd1026 := rd1025.swap1 (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1026.jump (by decide +native) hret (by evm_ov)⟩

theorem cureListArrayLoopStepBack {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {a b base ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 (⟨987⟩ : UInt256)
      (dest :: slot :: endp :: a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hcond : UInt256.gt endp ((⟨32⟩ : UInt256) + dest) ≠ ⟨0⟩)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 (⟨987⟩ : UInt256)
      (((⟨32⟩ : UInt256) + dest) :: ((⟨1⟩ : UInt256) + slot) :: endp ::
        a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      (listArrayCopyStepMem σ ee slot dest mem) (listArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd1016⟩ :=
    cureListArrayLoopStepToBranch
      (R := a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      h (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1016.jumpiT (by decide +native) hcond (by jump_dest) (by evm_ov)⟩

theorem cureListArrayLoopStepExit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {a b base ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 (⟨987⟩ : UInt256)
      (dest :: slot :: endp :: a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hcond : UInt256.gt endp ((⟨32⟩ : UInt256) + dest) = ⟨0⟩)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret (base :: R)
      (listArrayCopyStepMem σ ee slot dest mem) (listArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd1016⟩ :=
    cureListArrayLoopStepToBranch
      (R := a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      h (by simp only [List.length_cons]; omega)
  have rd1017 := rd1016.jumpiNT (by decide +native) hcond (by evm_ov)
  exact cureListArrayCleanup rd1017 hret (by omega)

set_option maxHeartbeats 1000000 in
theorem cureListArrayLoopRunAux {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {rdata : ByteArray}
    (hwf : cureStorageWF σ ee) :
    ∀ rem idx,
      idx + (rem + 1) = (cureSlotWord ⟨2⟩ σ ee).toNat →
      RD cureBytecode ee g s0 (⟨987⟩ : UInt256)
        (listArrayDest idx :: listArraySlot idx ::
          listArrayEndPtr (cureSlotWord ⟨2⟩ σ ee) ::
          cureSlotWord ⟨2⟩ σ ee :: (⟨2⟩ : UInt256) :: listArrayBasePtr ::
          (⟨96⟩ : UInt256) :: (⟨369⟩ : UInt256) :: cureSelWord ee :: [])
        (listArrayCopiedMem σ ee (cureSlotWord ⟨2⟩ σ ee) idx)
        (listArrayCopiedAw idx) rdata (cA, σ) k C →
      ∃ k' C', RD cureBytecode ee g s0 (⟨369⟩ : UInt256)
        [listArrayBasePtr, cureSelWord ee]
        (listArrayCopiedMem σ ee (cureSlotWord ⟨2⟩ σ ee)
          (cureSlotWord ⟨2⟩ σ ee).toNat)
        (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ ee).toNat)
        rdata (cA, σ) k' C'
  | 0, idx, hsum, h => by
      have hguard :
          UInt256.gt (listArrayEndPtr (cureSlotWord ⟨2⟩ σ ee))
              ((⟨32⟩ : UInt256) + listArrayDest idx) = ⟨0⟩ :=
        listArrayLoopGuard_false_of_wf hwf hsum
      obtain ⟨_, _, h369⟩ :=
        cureListArrayLoopStepExit (σ := σ) h
          (by jump_dest) hguard (by simp)
      exact ⟨_, _, by
        rw [← hsum]
        simpa [listArrayCopiedAw,
          listArrayCopyStepMem_eq_copied_succ_of_wf hwf (n := idx) (by omega)]
          using h369⟩
  | rem + 1, idx, hsum, h => by
      have hguard :
          UInt256.gt (listArrayEndPtr (cureSlotWord ⟨2⟩ σ ee))
              ((⟨32⟩ : UInt256) + listArrayDest idx) ≠ ⟨0⟩ := by
        rw [listArrayLoopGuard_true_of_wf hwf (n := idx) (by omega)]
        decide
      obtain ⟨k1, C1, hnext⟩ :=
        cureListArrayLoopStepBack (σ := σ) h hguard (by simp)
      have hnext' : RD cureBytecode ee g s0 (⟨987⟩ : UInt256)
          (listArrayDest (idx + 1) :: listArraySlot (idx + 1) ::
            listArrayEndPtr (cureSlotWord ⟨2⟩ σ ee) ::
            cureSlotWord ⟨2⟩ σ ee :: (⟨2⟩ : UInt256) :: listArrayBasePtr ::
            (⟨96⟩ : UInt256) :: (⟨369⟩ : UInt256) :: cureSelWord ee :: [])
          (listArrayCopiedMem σ ee (cureSlotWord ⟨2⟩ σ ee) (idx + 1))
          (listArrayCopiedAw (idx + 1)) rdata (cA, σ) k1 C1 := by
        simpa [listArrayDest_succ_eq, listArraySlot_succ_eq, listArrayCopiedAw,
          listArrayCopyStepMem_eq_copied_succ_of_wf hwf (n := idx) (by omega)]
          using hnext
      exact cureListArrayLoopRunAux hwf rem (idx + 1) (by omega) hnext'

theorem listMloadCost_of_stack {s : State} {aw off : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MLOAD = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

theorem listReturnCost_of_stack {s : State} {aw off len : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: len :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) -
        Cₘ aw = mcost) :
    memoryExpansionCost s .RETURN = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have h0 : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  have h1 : s.machineState.stack[1]! = len := by
    rw [hstk]
    rfl
  rw [h0, h1, haw]
  exact hcost


end Benchmarks.Dss.Cure
