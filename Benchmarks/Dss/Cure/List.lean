import Benchmarks.Dss.Cure.ListLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

noncomputable def listReturnOffsetMem (fmp : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem fmp.toNat 32

noncomputable def listReturnLengthMem (len fmp : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray len).write 0 (listReturnOffsetMem fmp mem)
    (fmp + (⟨32⟩ : UInt256)).toNat 32

abbrev listReturnMload64Aw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)

abbrev listReturnOffsetAw (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (listReturnMload64Aw aw).toNat fmp.toNat 32)

abbrev listReturnArrayMloadAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (listReturnOffsetAw aw fmp).toNat arrPtr.toNat 32)

abbrev listReturnLengthAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (listReturnArrayMloadAw aw fmp arrPtr).toNat
      (fmp + (⟨32⟩ : UInt256)).toNat 32)

abbrev listReturnFinalAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (listReturnLengthAw aw fmp arrPtr).toNat arrPtr.toNat 32)

abbrev listReturnCopyMloadAw (aw src i : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (i + src).toNat 32)

abbrev listReturnCopyStepAw (aw src dst i : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (listReturnCopyMloadAw aw src i).toNat
    (i + dst).toNat 32)

noncomputable def listReturnCopyStepMem
    (word dst i : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem (i + dst).toNat 32

abbrev listReturnDataDst (len : UInt256) : UInt256 :=
  listArrayFreePtr len + (⟨64⟩ : UInt256)

def listReturnCopyOffset : Nat → UInt256
  | 0 => ⟨0⟩
  | n + 1 => (⟨32⟩ : UInt256) + listReturnCopyOffset n

def listReturnDataWord (σ : AccountMap) (I : ExecutionEnv) (idx : Nat) : UInt256 :=
  UInt256.land (solcSlotWord σ I (listArraySlot idx)) solcAddrMask

noncomputable def listReturnBaseMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  listReturnLengthMem (cureSlotWord ⟨2⟩ σ I)
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
    (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
      (cureSlotWord ⟨2⟩ σ I).toNat)

noncomputable def listReturnCopiedMem (σ : AccountMap) (I : ExecutionEnv) : Nat → ByteArray
  | 0 => listReturnBaseMem σ I
  | n + 1 =>
      (UInt256.toByteArray (listReturnDataWord σ I n)).write 0
        (listReturnCopiedMem σ I n)
        ((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat 32

def listReturnCopiedAw (σ : AccountMap) (I : ExecutionEnv) (n : Nat) : UInt256 :=
  UInt256.ofNat (7 + (cureSlotWord ⟨2⟩ σ I).toNat + n)

theorem listReturnCopyOffset_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopyOffset n).toNat = 32 * n
  | 0, _ => by
      rfl
  | n + 1, hn => by
      rw [listReturnCopyOffset, uadd_toNat,
        listReturnCopyOffset_toNat_of_wf hwf (n := n) (by omega),
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [show 32 + 32 * n = 32 * (n + 1) by omega]
      apply Nat.mod_eq_of_lt
      have hmul := cureStorageWF_mul32_lt hwf
      nlinarith

theorem listReturnDataDst_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat =
      224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  exact listReturnDst_toNat_of_wf hwf

theorem listReturnCopyDest_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    ((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat =
      224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n := by
  rw [uadd_toNat, listReturnCopyOffset_toNat_of_wf hwf hn,
    listReturnDataDst_toNat_of_wf hwf]
  rw [show 32 * n + (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
    224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n by omega]
  apply Nat.mod_eq_of_lt
  have hret := cureStorageWF_returnEnd_lt hwf
  nlinarith

theorem listReturnCopySrc_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    ((listReturnCopyOffset n) + listArrayDataPtr).toNat = 160 + 32 * n := by
  rw [uadd_toNat, listReturnCopyOffset_toNat_of_wf hwf hn, listArrayDataPtr_toNat]
  rw [show 32 * n + 160 = 160 + 32 * n by omega]
  apply Nat.mod_eq_of_lt
  have hfree := cureStorageWF_freePtr_lt hwf
  nlinarith

theorem listReturnCopiedAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listReturnCopiedAw σ I n).toNat =
      7 + (cureSlotWord ⟨2⟩ σ I).toNat + n := by
  unfold listReturnCopiedAw
  rw [UInt256.toNat_ofNat_of_lt]
  have hret := cureStorageWF_returnEnd_lt hwf
  omega

theorem listReturnCopiedAw_mul32_lt_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listReturnCopiedAw σ I n).toNat * 32 < UInt256.size := by
  rw [listReturnCopiedAw_toNat_of_wf hwf hn]
  have hret := cureStorageWF_returnEnd_lt hwf
  nlinarith

theorem listReturnMload64Aw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnMload64Aw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)).toNat =
      5 + (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnMload64Aw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listArrayCopiedAw_toNat_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)]
    rw [machineState_M_inBounds (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      omega)]
  · rw [listArrayCopiedAw_toNat_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)]
    rw [machineState_M_inBounds (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      omega)]
    have hfree := cureStorageWF_freePtr_lt hwf
    omega

theorem listReturnOffsetAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnOffsetAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))).toNat =
      6 + (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnOffsetAw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listReturnMload64Aw_toNat_of_wf hwf, listArrayFreePtr_toNat_of_wf hwf]
    rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat =
      32 * (5 + (cureSlotWord ⟨2⟩ σ I).toNat) by omega]
    rw [machineState_M_endWrite]
    omega
  · rw [listReturnMload64Aw_toNat_of_wf hwf, listArrayFreePtr_toNat_of_wf hwf]
    rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat =
      32 * (5 + (cureSlotWord ⟨2⟩ σ I).toNat) by omega]
    rw [machineState_M_endWrite]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listReturnArrayMloadAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnArrayMloadAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) listArrayBasePtr).toNat =
      6 + (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnArrayMloadAw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listReturnOffsetAw_toNat_of_wf hwf]
    rw [show listArrayBasePtr.toNat = 128 from by decide]
    rw [machineState_M_inBounds (by omega)]
  · rw [listReturnOffsetAw_toNat_of_wf hwf]
    rw [show listArrayBasePtr.toNat = 128 from by decide]
    rw [machineState_M_inBounds (by omega)]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listReturnLengthAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnLengthAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) listArrayBasePtr).toNat =
      7 + (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnLengthAw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listReturnArrayMloadAw_toNat_of_wf hwf, uadd_toNat,
      listArrayFreePtr_toNat_of_wf hwf, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
      192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
      rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
      apply Nat.mod_eq_of_lt
      have hret := cureStorageWF_returnEnd_lt hwf
      omega]
    rw [show 192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat =
      32 * (6 + (cureSlotWord ⟨2⟩ σ I).toNat) by omega]
    rw [machineState_M_endWrite]
    omega
  · rw [listReturnArrayMloadAw_toNat_of_wf hwf, uadd_toNat,
      listArrayFreePtr_toNat_of_wf hwf, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
      192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
      rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
      apply Nat.mod_eq_of_lt
      have hret := cureStorageWF_returnEnd_lt hwf
      omega]
    rw [show 192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat =
      32 * (6 + (cureSlotWord ⟨2⟩ σ I).toNat) by omega]
    rw [machineState_M_endWrite]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listReturnFinalAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnFinalAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) listArrayBasePtr).toNat =
      7 + (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnFinalAw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listReturnLengthAw_toNat_of_wf hwf]
    rw [show listArrayBasePtr.toNat = 128 from by decide]
    rw [machineState_M_inBounds (by omega)]
  · rw [listReturnLengthAw_toNat_of_wf hwf]
    rw [show listArrayBasePtr.toNat = 128 from by decide]
    rw [machineState_M_inBounds (by omega)]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listReturnFinalAw_eq_copied_zero_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    listReturnFinalAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) listArrayBasePtr =
      listReturnCopiedAw σ I 0 := by
  apply u256_inj
  rw [listReturnFinalAw_toNat_of_wf hwf,
    listReturnCopiedAw_toNat_of_wf hwf (n := 0) (by omega)]
  omega

theorem listReturnOffsetMem_read128_of_copied
    (σ : AccountMap) (ee : ExecutionEnv) (len fmp : UInt256) (n : Nat)
    (hbelow : listArrayBasePtr.toNat + 32 ≤ fmp.toNat)
    (hgap : fmp.toNat - (listArrayCopiedMem σ ee len n).size < USize.size) :
    (listReturnOffsetMem fmp (listArrayCopiedMem σ ee len n)).readWithPadding
        listArrayBasePtr.toNat 32 =
      UInt256.toByteArray len := by
  unfold listReturnOffsetMem
  rw [toByteArray_write_read_below_of_gap
    (⟨32⟩ : UInt256) (listArrayCopiedMem σ ee len n) fmp.toNat listArrayBasePtr.toNat
    (by
      rw [listArrayCopiedMem_size]
      have hbase : listArrayBasePtr.toNat = 128 := by decide +native
      omega)
    hbelow hgap]
  exact listArrayCopiedMem_read128 σ ee len n

theorem listReturnLengthMem_read128_of_copied
    (σ : AccountMap) (ee : ExecutionEnv) (len fmp : UInt256) (n : Nat)
    (hbelow0 : listArrayBasePtr.toNat + 32 ≤ fmp.toNat)
    (hbelow1 : listArrayBasePtr.toNat + 32 ≤ (fmp + (⟨32⟩ : UInt256)).toNat)
    (hread :
      listArrayBasePtr.toNat + 32 ≤
        (listReturnOffsetMem fmp (listArrayCopiedMem σ ee len n)).size)
    (hgap0 : fmp.toNat - (listArrayCopiedMem σ ee len n).size < USize.size)
    (hgap1 : (fmp + (⟨32⟩ : UInt256)).toNat -
        (listReturnOffsetMem fmp (listArrayCopiedMem σ ee len n)).size < USize.size) :
    (listReturnLengthMem len fmp (listArrayCopiedMem σ ee len n)).readWithPadding
        listArrayBasePtr.toNat 32 =
      UInt256.toByteArray len := by
  unfold listReturnLengthMem
  rw [toByteArray_write_read_below_of_gap len
    (listReturnOffsetMem fmp (listArrayCopiedMem σ ee len n))
    (fmp + (⟨32⟩ : UInt256)).toNat listArrayBasePtr.toNat
    hread
    hbelow1 hgap1]
  exact listReturnOffsetMem_read128_of_copied σ ee len fmp n hbelow0 hgap0

theorem listReturnOffsetMem_size_of_copied_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
        (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
          (cureSlotWord ⟨2⟩ σ I).toNat)).size =
      192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnOffsetMem
  rw [toByteArray_write32_size_of_ge
    (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
      (cureSlotWord ⟨2⟩ σ I).toNat)
    (⟨32⟩ : UInt256)
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
    (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
    (192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
    (by rw [listArrayCopiedMem_size])
    (by rw [listArrayFreePtr_toNat_of_wf hwf])
    (by
      rw [listArrayFreePtr_toNat_of_wf hwf]
      have hU : 0 < USize.size := by decide +native
      omega)
    (by
      rw [listArrayFreePtr_toNat_of_wf hwf]
      omega)]

theorem listReturnLengthMem_size_of_copied_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (listReturnLengthMem (cureSlotWord ⟨2⟩ σ I)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
        (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
          (cureSlotWord ⟨2⟩ σ I).toNat)).size =
      224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listReturnLengthMem
  rw [toByteArray_write32_size_of_ge
    (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
      (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
        (cureSlotWord ⟨2⟩ σ I).toNat))
    (cureSlotWord ⟨2⟩ σ I)
    ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat
    (192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
    (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
    (listReturnOffsetMem_size_of_copied_wf hwf)
    (by
      rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [show (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat =
        160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat from
        listArrayFreePtr_toNat_of_wf hwf]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega])
    (by
      rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega]
      have hU : 0 < USize.size := by decide +native
      omega)
    (by
      rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega]
      omega)]

theorem listReturnCopiedMem_size_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopiedMem σ I n).size =
        224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n
  | 0, _ => by
      rw [listReturnCopiedMem, listReturnBaseMem, listReturnLengthMem_size_of_copied_wf hwf]
      omega
  | n + 1, hn => by
      rw [listReturnCopiedMem]
      exact toByteArray_write32_size_of_ge
        (listReturnCopiedMem σ I n) (listReturnDataWord σ I n)
        (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
        (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n)
        (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * (n + 1))
        (listReturnCopiedMem_size_of_wf hwf (n := n) (by omega))
        (by rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)])
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
          have hU : 0 < USize.size := by decide +native
          omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
          omega)

theorem listReturnCopiedMem_read64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopiedMem σ I n).readWithPadding 64 32 =
        UInt256.toByteArray (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
  | 0, _ => by
      unfold listReturnCopiedMem listReturnBaseMem listReturnLengthMem
      rw [toByteArray_write_read_below_of_gap
        (cureSlotWord ⟨2⟩ σ I)
        (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
          (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
            (cureSlotWord ⟨2⟩ σ I).toNat))
        ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat 64
        (by rw [listReturnOffsetMem_size_of_copied_wf hwf]; omega)
        (by
          rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
            show (⟨32⟩ : UInt256).toNat = 32 from by decide]
          rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
            rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
            apply Nat.mod_eq_of_lt
            have hret := cureStorageWF_returnEnd_lt hwf
            omega]
          omega)
        (by
          rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
            show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            listReturnOffsetMem_size_of_copied_wf hwf]
          rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
            rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
            apply Nat.mod_eq_of_lt
            have hret := cureStorageWF_returnEnd_lt hwf
            omega]
          have hU : 0 < USize.size := by decide +native
          omega)]
      unfold listReturnOffsetMem
      rw [toByteArray_write_read_below_of_gap
        (⟨32⟩ : UInt256)
        (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
          (cureSlotWord ⟨2⟩ σ I).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat 64
        (by rw [listArrayCopiedMem_size]; omega)
        (by rw [listArrayFreePtr_toNat_of_wf hwf]; omega)
        (by
          rw [listArrayFreePtr_toNat_of_wf hwf, listArrayCopiedMem_size]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listArrayCopiedMem_read64 σ I (cureSlotWord ⟨2⟩ σ I)
        (cureSlotWord ⟨2⟩ σ I).toNat
  | n + 1, hn => by
      rw [listReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (listReturnDataWord σ I n) (listReturnCopiedMem σ I n)
        (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
        64
        (by rw [listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]; omega)
        (by rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]; omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
            listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listReturnCopiedMem_read64_of_wf hwf (n := n) (by omega)

theorem listReturnBaseMem_read_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {k : Nat}
    (hk : k < (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listReturnBaseMem σ I).readWithPadding (160 + 32 * k) 32 =
      UInt256.toByteArray (listReturnDataWord σ I k) := by
  unfold listReturnBaseMem listReturnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (cureSlotWord ⟨2⟩ σ I)
    (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
      (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
        (cureSlotWord ⟨2⟩ σ I).toNat))
    ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat
    (160 + 32 * k)
    (by rw [listReturnOffsetMem_size_of_copied_wf hwf]; omega)
    (by
      have hfmp :
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat =
            160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat :=
        listArrayFreePtr_toNat_of_wf hwf
      have hnext :
          ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
        rw [uadd_toNat, hfmp, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
          rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
          apply Nat.mod_eq_of_lt
          have hret := cureStorageWF_returnEnd_lt hwf
          omega]
      rw [hnext]
      omega)
    (by
      rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        listReturnOffsetMem_size_of_copied_wf hwf]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega]
      have hU : 0 < USize.size := by decide +native
      omega)]
  unfold listReturnOffsetMem
  rw [toByteArray_write_read_below_of_gap
    (⟨32⟩ : UInt256)
    (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
      (cureSlotWord ⟨2⟩ σ I).toNat)
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
    (160 + 32 * k)
    (by rw [listArrayCopiedMem_size]; omega)
    (by rw [listArrayFreePtr_toNat_of_wf hwf]; omega)
    (by
      rw [listArrayFreePtr_toNat_of_wf hwf, listArrayCopiedMem_size]
      have hU : 0 < USize.size := by decide +native
      omega)]
  simpa [listReturnDataWord] using
    listArrayCopiedMem_read_elem σ I (cureSlotWord ⟨2⟩ σ I)
      (cureSlotWord ⟨2⟩ σ I).toNat k hk

theorem listReturnCopiedMem_read_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n k}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      k < (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopiedMem σ I n).readWithPadding (160 + 32 * k) 32 =
        UInt256.toByteArray (listReturnDataWord σ I k)
  | 0, k, _, hk => by
      exact listReturnBaseMem_read_src_of_wf hwf hk
  | n + 1, k, hn, hk => by
      rw [listReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (listReturnDataWord σ I n) (listReturnCopiedMem σ I n)
        (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
        (160 + 32 * k)
        (by rw [listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]; omega)
        (by rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]; omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
            listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listReturnCopiedMem_read_src_of_wf hwf (n := n) (k := k) (by omega) hk

theorem listReturnCopiedMem_mload_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n < (cureSlotWord ⟨2⟩ σ I).toNat) :
    (if ((listReturnCopyOffset n) + listArrayDataPtr).toNat ≥
          (listReturnCopiedMem σ I n).size
        ∨ ((listReturnCopyOffset n) + listArrayDataPtr) ≥
          listReturnCopiedAw σ I n * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((listReturnCopiedMem σ I n).readWithPadding
            ((listReturnCopyOffset n) + listArrayDataPtr).toNat 32)))
      = listReturnDataWord σ I n := by
  exact mloadWordValue_of_readWithPadding
    (by
      rw [listReturnCopySrc_toNat_of_wf hwf (n := n) (by omega),
        listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
      omega)
    (wordMul32_not_ge_of_lt
      (by
        rw [listReturnCopySrc_toNat_of_wf hwf (n := n) (by omega),
          listReturnCopiedAw_toNat_of_wf hwf (n := n) (by omega)]
        omega)
      (listReturnCopiedAw_mul32_lt_of_wf hwf (n := n) (by omega)))
    (by
      rw [listReturnCopySrc_toNat_of_wf hwf (n := n) (by omega)]
      exact listReturnCopiedMem_read_src_of_wf hwf (n := n) (k := n) (by omega) hn)

theorem listReturnBaseMem_read_offset_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnBaseMem σ I).readWithPadding
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat 32 =
      UInt256.toByteArray (⟨32⟩ : UInt256) := by
  unfold listReturnBaseMem listReturnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (cureSlotWord ⟨2⟩ σ I)
    (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
      (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
        (cureSlotWord ⟨2⟩ σ I).toNat))
    ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
    (by rw [listReturnOffsetMem_size_of_copied_wf hwf, listArrayFreePtr_toNat_of_wf hwf]; omega)
    (by
      have hfmp :
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat =
            160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat :=
        listArrayFreePtr_toNat_of_wf hwf
      have hnext :
          ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
        rw [uadd_toNat, hfmp, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
          rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
          apply Nat.mod_eq_of_lt
          have hret := cureStorageWF_returnEnd_lt hwf
          omega]
      rw [hfmp, hnext]
      omega)
    (by
      rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        listReturnOffsetMem_size_of_copied_wf hwf]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega]
      have hU : 0 < USize.size := by decide +native
      omega)]
  unfold listReturnOffsetMem
  exact toByteArray_write_read_back_of_gap (⟨32⟩ : UInt256)
    (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
      (cureSlotWord ⟨2⟩ σ I).toNat)
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
    (by
      rw [listArrayFreePtr_toNat_of_wf hwf, listArrayCopiedMem_size]
      have hU : 0 < USize.size := by decide +native
      omega)

theorem listReturnBaseMem_read_length_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listReturnBaseMem σ I).readWithPadding
        ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat 32 =
      UInt256.toByteArray (cureSlotWord ⟨2⟩ σ I) := by
  unfold listReturnBaseMem listReturnLengthMem
  exact toByteArray_write_read_back_of_gap (cureSlotWord ⟨2⟩ σ I)
    (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
      (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
        (cureSlotWord ⟨2⟩ σ I).toNat))
    ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat
    (by
      rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        listReturnOffsetMem_size_of_copied_wf hwf]
      rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
        192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
        rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
          192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
        apply Nat.mod_eq_of_lt
        have hret := cureStorageWF_returnEnd_lt hwf
        omega]
      have hU : 0 < USize.size := by decide +native
      omega)

theorem listReturnCopiedMem_read_offset_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopiedMem σ I n).readWithPadding
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat 32 =
        UInt256.toByteArray (⟨32⟩ : UInt256)
  | 0, _ => listReturnBaseMem_read_offset_of_wf hwf
  | n + 1, hn => by
      rw [listReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (listReturnDataWord σ I n) (listReturnCopiedMem σ I n)
        (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
        (by
          rw [listReturnCopiedMem_size_of_wf hwf (n := n) (by omega),
            listArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by
          rw [listArrayFreePtr_toNat_of_wf hwf,
            listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
          omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
            listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listReturnCopiedMem_read_offset_of_wf hwf (n := n) (by omega)

theorem listReturnCopiedMem_read_length_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listReturnCopiedMem σ I n).readWithPadding
          ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat 32 =
        UInt256.toByteArray (cureSlotWord ⟨2⟩ σ I)
  | 0, _ => listReturnBaseMem_read_length_of_wf hwf
  | n + 1, hn => by
      rw [listReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (listReturnDataWord σ I n) (listReturnCopiedMem σ I n)
        (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
        ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat
        (by
          rw [listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
          have hnext :
              ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat =
                192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
            rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
              show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
              rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
                192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
              apply Nat.mod_eq_of_lt
              have hret := cureStorageWF_returnEnd_lt hwf
              omega]
          rw [hnext]
          omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
          have hnext :
              ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256))).toNat =
                192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
            rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
              show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
              rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
                192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
              apply Nat.mod_eq_of_lt
              have hret := cureStorageWF_returnEnd_lt hwf
              omega]
          rw [hnext]
          omega)
        (by
          rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
            listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listReturnCopiedMem_read_length_of_wf hwf (n := n) (by omega)

theorem listReturnCopiedMem_read_data_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n k}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat → k < n →
      (listReturnCopiedMem σ I n).readWithPadding
          (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * k) 32 =
        UInt256.toByteArray (listReturnDataWord σ I k)
  | 0, k, _, hk => by omega
  | n + 1, k, hn, hk => by
      rw [listReturnCopiedMem]
      by_cases hlast : k = n
      · subst k
        rw [← listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
        exact toByteArray_write_read_back_of_gap (listReturnDataWord σ I n)
          (listReturnCopiedMem σ I n)
          (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
          (by
            rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
              listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
            have hU : 0 < USize.size := by decide +native
            omega)
      · have hk' : k < n := by omega
        rw [toByteArray_write_read_below_of_gap
          (listReturnDataWord σ I n) (listReturnCopiedMem σ I n)
          (((listReturnCopyOffset n) + listReturnDataDst (cureSlotWord ⟨2⟩ σ I)).toNat)
          (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * k)
          (by rw [listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]; omega)
          (by rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]; omega)
          (by
            rw [listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega),
              listReturnCopiedMem_size_of_wf hwf (n := n) (by omega)]
            have hU : 0 < USize.size := by decide +native
            omega)]
        exact listReturnCopiedMem_read_data_of_wf hwf (n := n) (k := k) (by omega) hk'

theorem byteArray_toList_toByteArray (b : ByteArray) :
    b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [byteArray_toList_eq]

theorem natBytes_toByteArray (n : Nat) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) := by
  show (EVM.Word.toBytesBE (UInt256.ofNat n)).toByteArray = _
  exact word_toBytesBE_toByteArray_eq_toByteArray _

theorem listSrcsWordBytesFrom_toByteArray {σ : AccountMap} {I : ExecutionEnv} :
    ∀ idx n,
      (listSrcsWordBytesFrom σ I idx n).toByteArray =
        wordConcat
          (fun i => UInt256.land
            (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat i)))) solcAddrMask)
          idx n
  | _, 0 => by
      simp [listSrcsWordBytesFrom, wordConcat]
  | idx, n + 1 => by
      rw [listSrcsWordBytesFrom, wordConcat_succ, list_toByteArray_append,
        byteArray_toList_toByteArray, listSrcsWordBytesFrom_toByteArray (idx + 1) n]

theorem listReturnDataWord_eq_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {idx : Nat}
    (hidx : idx ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    listReturnDataWord σ I idx =
      UInt256.land (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx)))) solcAddrMask := by
  unfold listReturnDataWord
  rw [listArraySlot_eq_srcElemSlot_of_wf hwf hidx]

theorem wordConcat_listReturnDataWord_eq_listSrcsWordBytesFrom
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    ∀ idx n, idx + n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      wordConcat (listReturnDataWord σ I) idx n =
        (listSrcsWordBytesFrom σ I idx n).toByteArray
  | idx, n, hle => by
      rw [listSrcsWordBytesFrom_toByteArray]
      apply wordConcat_congr
      intro k hk
      exact listReturnDataWord_eq_src_of_wf hwf (idx := idx + k) (by omega)

theorem listReturnCopiedMem_read_data_span_of_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
        (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
        (32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
      (listSrcsWordBytesFrom σ I 0 (cureSlotWord ⟨2⟩ σ I).toNat).toByteArray := by
  have hconcat := readWithPadding_wordConcat
    (mem := listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat)
    (f := listReturnDataWord σ I)
    (base := 224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
    (n := (cureSlotWord ⟨2⟩ σ I).toNat) (idx := 0)
    (by
      have hret := cureStorageWF_returnEnd_lt_u64 hwf
      omega)
    (by
      rw [listReturnCopiedMem_size_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat)
        (by omega)]
      omega)
    (by
      intro k hk
      simpa using listReturnCopiedMem_read_data_of_wf hwf
        (n := (cureSlotWord ⟨2⟩ σ I).toNat) (k := k) (by omega) hk)
  have hbytes := wordConcat_listReturnDataWord_eq_listSrcsWordBytesFrom hwf 0
    (cureSlotWord ⟨2⟩ σ I).toNat (by omega)
  simpa using hconcat.trans hbytes

theorem listReturnCopiedMem_read_return_of_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I)
    (hlenpos : 0 < (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
        (UInt256.sub
          (((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) +
            listReturnDataDst (cureSlotWord ⟨2⟩ σ I))
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))).toNat =
      listSrcsReturnBytes σ I := by
  rw [listReturnSize_toNat_of_wf hwf]
  have hsplitHead :
      (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat
          (64 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
        (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat 32 ++
          (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
            ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 32)
            (32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) := by
    rw [show 64 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat =
      32 + (32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) by omega]
    exact byteArray_readWithPadding_split
      (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat)
      (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat 32
      (32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat)
      (by norm_num) (by omega) (by norm_num)
      (by
        have hret := cureStorageWF_returnEnd_lt_u64 hwf
        omega)
      (by
        have hret := cureStorageWF_returnEnd_lt_u64 hwf
        omega)
      (by
        rw [listArrayFreePtr_toNat_of_wf hwf,
          listReturnCopiedMem_size_of_wf hwf
            (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)]
        omega)
  have hsplitTail :
      (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
          ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 32)
          (32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
        (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
            ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 32) 32 ++
          (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
            ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 64)
            (32 * (cureSlotWord ⟨2⟩ σ I).toNat) := by
    exact byteArray_readWithPadding_split
      (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat)
      ((listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 32) 32
      (32 * (cureSlotWord ⟨2⟩ σ I).toNat)
      (by norm_num) (by omega) (by norm_num)
      (by
        have hret := cureStorageWF_returnEnd_lt_u64 hwf
        omega)
      (by
        have hret := cureStorageWF_returnEnd_lt_u64 hwf
        omega)
      (by
        rw [listArrayFreePtr_toNat_of_wf hwf,
          listReturnCopiedMem_size_of_wf hwf
            (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)]
        omega)
  rw [hsplitHead, hsplitTail]
  rw [listReturnCopiedMem_read_offset_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat)
      (by omega)]
  rw [show (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 32 =
      (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨32⟩ : UInt256)).toNat by
      conv_rhs => rw [uadd_toNat]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      exact (Nat.mod_eq_of_lt (by
        rw [listArrayFreePtr_toNat_of_wf hwf]
        have hret := cureStorageWF_returnDst_lt hwf
        omega)).symm]
  rw [listReturnCopiedMem_read_length_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat)
      (by omega)]
  rw [show (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat + 64 =
      224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
      rw [listArrayFreePtr_toNat_of_wf hwf]; omega]
  rw [listReturnCopiedMem_read_data_span_of_wf hwf]
  unfold listSrcsReturnBytes
  rw [show (⟨(ABI.natBytes 32 ++
      (ABI.natBytes (listSrcsValues σ I).length ++
        listSrcsWordBytesFrom σ I 0 (cureSlotWord ⟨2⟩ σ I).toNat)).toArray⟩ : ByteArray) =
      (ABI.natBytes 32 ++
        (ABI.natBytes (listSrcsValues σ I).length ++
          listSrcsWordBytesFrom σ I 0 (cureSlotWord ⟨2⟩ σ I).toNat)).toByteArray by
    rw [← List.data_toByteArray]]
  rw [list_toByteArray_append, list_toByteArray_append, natBytes_toByteArray,
    natBytes_toByteArray, listSrcsValues_length, u256_ofNat_toNat]
  rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) by rfl]

theorem listReturnCopyMloadAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listReturnCopyMloadAw (listReturnCopiedAw σ I n) listArrayDataPtr
        (listReturnCopyOffset n)).toNat =
      7 + (cureSlotWord ⟨2⟩ σ I).toNat + n := by
  unfold listReturnCopyMloadAw
  rw [UInt256.toNat_ofNat_of_lt]
  · rw [listReturnCopiedAw_toNat_of_wf hwf hn,
      listReturnCopySrc_toNat_of_wf hwf hn]
    rw [machineState_M_inBounds (by omega)]
  · rw [listReturnCopiedAw_toNat_of_wf hwf hn,
      listReturnCopySrc_toNat_of_wf hwf hn]
    rw [machineState_M_inBounds (by omega)]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listReturnCopyStepAw_eq_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n + 1 ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    listReturnCopyStepAw (listReturnCopiedAw σ I n) listArrayDataPtr
        (listReturnDataDst (cureSlotWord ⟨2⟩ σ I)) (listReturnCopyOffset n) =
      listReturnCopiedAw σ I (n + 1) := by
  apply u256_inj
  unfold listReturnCopyStepAw
  rw [UInt256.toNat_ofNat_of_lt, listReturnCopiedAw_toNat_of_wf hwf (n := n + 1) hn]
  · rw [listReturnCopyMloadAw_toNat_of_wf hwf (n := n) (by omega),
      listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
    rw [show 224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n =
      32 * (7 + (cureSlotWord ⟨2⟩ σ I).toNat + n) by omega]
    rw [machineState_M_endWrite]
    omega
  · rw [listReturnCopyMloadAw_toNat_of_wf hwf (n := n) (by omega),
      listReturnCopyDest_toNat_of_wf hwf (n := n) (by omega)]
    rw [show 224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 * n =
      32 * (7 + (cureSlotWord ⟨2⟩ σ I).toNat + n) by omega]
    rw [machineState_M_endWrite]
    have hret := cureStorageWF_returnEnd_lt hwf
    omega

theorem listArrayCopiedMem_mload64_of_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
            (cureSlotWord ⟨2⟩ σ I).toNat).size
        ∨ (⟨64⟩ : UInt256) ≥
          listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
            (cureSlotWord ⟨2⟩ σ I).toNat).readWithPadding
              (⟨64⟩ : UInt256).toNat 32)))
      = listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) := by
  exact listArrayCopiedMem_mload64 σ I (cureSlotWord ⟨2⟩ σ I)
    (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
    (cureSlotWord ⟨2⟩ σ I).toNat
    (wordMul32_not_ge_of_lt
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          listArrayCopiedAw_toNat_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)]
        omega)
      (listArrayCopiedAw_mul32_lt_of_wf hwf (n := (cureSlotWord ⟨2⟩ σ I).toNat) (by omega)))

theorem listReturnOffsetMem_mload128_of_copied_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (if listArrayBasePtr.toNat ≥
          (listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
            (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
              (cureSlotWord ⟨2⟩ σ I).toNat)).size
        ∨ listArrayBasePtr ≥
          listReturnOffsetAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((listReturnOffsetMem (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
            (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
              (cureSlotWord ⟨2⟩ σ I).toNat)).readWithPadding
                listArrayBasePtr.toNat 32)))
      = cureSlotWord ⟨2⟩ σ I := by
  exact mloadWordValue_of_readWithPadding
    (by
      rw [show listArrayBasePtr.toNat = 128 from by decide,
        listReturnOffsetMem_size_of_copied_wf hwf]
      omega)
    (wordMul32_not_ge_of_lt
      (by
        rw [show listArrayBasePtr.toNat = 128 from by decide,
          listReturnOffsetAw_toNat_of_wf hwf]
        omega)
      (by
        rw [listReturnOffsetAw_toNat_of_wf hwf]
        have hret := cureStorageWF_returnEnd_lt hwf
        omega))
    (by
      exact listReturnOffsetMem_read128_of_copied σ I
        (cureSlotWord ⟨2⟩ σ I) (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
        (cureSlotWord ⟨2⟩ σ I).toNat
        (by
          rw [show listArrayBasePtr.toNat = 128 from by decide,
            listArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by
          rw [listArrayFreePtr_toNat_of_wf hwf, listArrayCopiedMem_size]
          have hU : 0 < USize.size := by decide +native
          omega))

theorem listReturnLengthMem_mload128_of_copied_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) :
    (if listArrayBasePtr.toNat ≥
          (listReturnLengthMem (cureSlotWord ⟨2⟩ σ I)
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
            (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
              (cureSlotWord ⟨2⟩ σ I).toNat)).size
        ∨ listArrayBasePtr ≥
          listReturnLengthAw (listArrayCopiedAw (cureSlotWord ⟨2⟩ σ I).toNat)
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)) listArrayBasePtr * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((listReturnLengthMem (cureSlotWord ⟨2⟩ σ I)
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
            (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I)
              (cureSlotWord ⟨2⟩ σ I).toNat)).readWithPadding
                listArrayBasePtr.toNat 32)))
      = cureSlotWord ⟨2⟩ σ I := by
  exact mloadWordValue_of_readWithPadding
    (by
      rw [show listArrayBasePtr.toNat = 128 from by decide,
        listReturnLengthMem_size_of_copied_wf hwf]
      omega)
    (wordMul32_not_ge_of_lt
      (by
        rw [show listArrayBasePtr.toNat = 128 from by decide,
          listReturnLengthAw_toNat_of_wf hwf]
        omega)
      (by
        rw [listReturnLengthAw_toNat_of_wf hwf]
        have hret := cureStorageWF_returnEnd_lt hwf
        omega))
    (by
      exact listReturnLengthMem_read128_of_copied σ I
        (cureSlotWord ⟨2⟩ σ I) (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))
        (cureSlotWord ⟨2⟩ σ I).toNat
        (by
          rw [show listArrayBasePtr.toNat = 128 from by decide,
            listArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by
          rw [show listArrayBasePtr.toNat = 128 from by decide,
            uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
            show (⟨32⟩ : UInt256).toNat = 32 from by decide]
          rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
            rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
            apply Nat.mod_eq_of_lt
            have hret := cureStorageWF_returnEnd_lt hwf
            omega]
          omega)
        (by
          rw [show listArrayBasePtr.toNat = 128 from by decide,
            listReturnOffsetMem_size_of_copied_wf hwf]
          omega)
        (by
          rw [listArrayFreePtr_toNat_of_wf hwf, listArrayCopiedMem_size]
          have hU : 0 < USize.size := by decide +native
          omega)
        (by
          rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
            show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            listReturnOffsetMem_size_of_copied_wf hwf]
          rw [show (160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32) % UInt256.size =
            192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by
            rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 32 =
              192 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
            apply Nat.mod_eq_of_lt
            have hret := cureStorageWF_returnEnd_lt hwf
            omega]
          have hU : 0 < USize.size := by decide +native
          omega))

set_option maxHeartbeats 1000000 in
theorem cureListReturnFromMemToCopyLoop {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {arrPtr fmp len : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 (⟨369⟩ : UInt256) (arrPtr :: R) mem aw rdata acc k C)
    (hload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fmp)
    (hloadArr :
      (if arrPtr.toNat ≥ (listReturnOffsetMem fmp mem).size
          ∨ arrPtr ≥ listReturnOffsetAw aw fmp * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((listReturnOffsetMem fmp mem).readWithPadding arrPtr.toNat 32)))
        = len)
    (hloadArrTail :
      (if arrPtr.toNat ≥ (listReturnLengthMem len fmp mem).size
          ∨ arrPtr ≥ listReturnLengthAw aw fmp arrPtr * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((listReturnLengthMem len fmp mem).readWithPadding arrPtr.toNat 32)))
        = len)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 (⟨405⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: ((⟨32⟩ : UInt256) + arrPtr) ::
        (fmp + (⟨64⟩ : UInt256)) :: (len * (⟨32⟩ : UInt256)) ::
        (len * (⟨32⟩ : UInt256)) :: ((⟨32⟩ : UInt256) + arrPtr) ::
        (fmp + (⟨64⟩ : UInt256)) :: fmp :: fmp :: arrPtr :: R)
      (listReturnLengthMem len fmp mem) (listReturnFinalAw aw fmp arrPtr)
      rdata acc k' C' := by
  have rd370 := h.jumpdest (by decide +native) (by evm_ov)
  have rd372 := rd370.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd373 := rd372.dup1 (by decide +native) (by evm_ov)
  have rd374 := rd373.mload (Cₘ (listReturnMload64Aw aw) - Cₘ aw) fmp
    (listReturnMload64Aw aw) (by decide +native)
    (by
      intro s haw hstk
      exact listMloadCost_of_stack (aw := aw) (off := (⟨64⟩ : UInt256))
        (t := (⟨64⟩ : UInt256) :: arrPtr :: R) haw hstk (by rfl))
    hload64 (by rfl) (by evm_ov)
  have rd376 := rd374.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd377 := rd376.dup1 (by decide +native) (by evm_ov)
  have rd378 := rd377.dup3 (by decide +native) (by evm_ov)
  have rd379 := rd378.mstore
    (Cₘ (listReturnOffsetAw aw fmp) - Cₘ (listReturnMload64Aw aw))
    (listReturnOffsetMem fmp mem) (listReturnOffsetAw aw fmp) (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := listReturnMload64Aw aw) (off := fmp)
        (val := (⟨32⟩ : UInt256))
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd380 := rd379.dup4 (by decide +native) (by evm_ov)
  have rd381 := rd380.mload
    (Cₘ (listReturnArrayMloadAw aw fmp arrPtr) -
      Cₘ (listReturnOffsetAw aw fmp))
    len (listReturnArrayMloadAw aw fmp arrPtr) (by decide +native)
    (by
      intro s haw hstk
      exact listMloadCost_of_stack (aw := listReturnOffsetAw aw fmp) (off := arrPtr)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    hloadArr (by rfl) (by evm_ov)
  have rd382 := rd381.dup2 (by decide +native) (by evm_ov)
  have rd383 := rd382.dup4 (by decide +native) (by evm_ov)
  have rd384 := rd383.add (by decide +native) (by evm_ov)
  have rd385 := rd384.mstore
    (Cₘ (listReturnLengthAw aw fmp arrPtr) -
      Cₘ (listReturnArrayMloadAw aw fmp arrPtr))
    (listReturnLengthMem len fmp mem) (listReturnLengthAw aw fmp arrPtr)
    (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := listReturnArrayMloadAw aw fmp arrPtr)
        (off := fmp + (⟨32⟩ : UInt256)) (val := len)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd386 := rd385.dup4 (by decide +native) (by evm_ov)
  have rd387 := rd386.mload
    (Cₘ (listReturnFinalAw aw fmp arrPtr) -
      Cₘ (listReturnLengthAw aw fmp arrPtr))
    len (listReturnFinalAw aw fmp arrPtr) (by decide +native)
    (by
      intro s haw hstk
      exact listMloadCost_of_stack (aw := listReturnLengthAw aw fmp arrPtr)
        (off := arrPtr)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    hloadArrTail (by rfl) (by evm_ov)
  have rd405 := evm_run rd387 with [
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, dup2, add, swap2,
    mul, dup1, dup4, dup4, push1 ⟨0⟩]
  exact ⟨_, _, by
    simpa [listReturnOffsetMem, listReturnLengthMem] using rd405⟩

set_option maxHeartbeats 1000000 in
theorem cureListReturnCopyLoopStep {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {i src dst bound word : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 (⟨405⟩ : UInt256) (i :: src :: dst :: bound :: R)
      mem aw rdata acc k C)
    (hcont : UInt256.isZero (UInt256.lt i bound) = ⟨0⟩)
    (hload :
      (if (i + src).toNat ≥ mem.size ∨ (i + src) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (i + src).toNat 32))) = word)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 (⟨405⟩ : UInt256)
      (((⟨32⟩ : UInt256) + i) :: src :: dst :: bound :: R)
      (listReturnCopyStepMem word dst i mem)
      (listReturnCopyStepAw aw src dst i) rdata acc k' C' := by
  have rd406 := h.jumpdest (by decide +native) (by evm_ov)
  have rd407 := rd406.dup4 (by decide +native) (by evm_ov)
  have rd408 := rd407.dup2 (by decide +native) (by evm_ov)
  have rd409 := rd408.lt (by decide +native) (by evm_ov)
  have rd410raw := rd409.iszero (by decide +native) (by evm_ov)
  have rd410 := by
    simpa [hcont] using rd410raw
  have rd413 := rd410.push2 ⟨429⟩ (by decide +native) (by evm_ov)
  have rd414 := rd413.jumpiNT (by decide +native) rfl (by evm_ov)
  have rd415 := rd414.dup2 (by decide +native) (by evm_ov)
  have rd416 := rd415.dup2 (by decide +native) (by evm_ov)
  have rd417 := rd416.add (by decide +native) (by evm_ov)
  have rd418 := rd417.mload (Cₘ (listReturnCopyMloadAw aw src i) - Cₘ aw)
    word (listReturnCopyMloadAw aw src i) (by decide +native)
    (by
      intro s haw hstk
      exact listMloadCost_of_stack (aw := aw) (off := i + src)
        (t := i :: src :: dst :: bound :: R) haw hstk (by rfl))
    hload (by rfl) (by evm_ov)
  have rd419 := rd418.dup4 (by decide +native) (by evm_ov)
  have rd420 := rd419.dup3 (by decide +native) (by evm_ov)
  have rd421 := rd420.add (by decide +native) (by evm_ov)
  have rd422 := rd421.mstore
    (Cₘ (listReturnCopyStepAw aw src dst i) -
      Cₘ (listReturnCopyMloadAw aw src i))
    (listReturnCopyStepMem word dst i mem)
    (listReturnCopyStepAw aw src dst i) (by decide +native)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := listReturnCopyMloadAw aw src i)
        (off := i + dst) (val := word) (t := i :: src :: dst :: bound :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd424 := rd422.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd425 := rd424.add (by decide +native) (by evm_ov)
  have rd428 := rd425.push2 ⟨405⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [listReturnCopyStepMem, listReturnCopyMloadAw, listReturnCopyStepAw]
      using rd428.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem listReturnCopyLoopContinueCond_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n < (cureSlotWord ⟨2⟩ σ I).toNat) :
    UInt256.isZero
        (UInt256.lt (listReturnCopyOffset n)
          ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256))) = ⟨0⟩ := by
  have hlt : UInt256.lt (listReturnCopyOffset n)
      ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) = ⟨1⟩ := by
    apply ult_one
    rw [listReturnCopyOffset_toNat_of_wf hwf (n := n) (by omega),
      listReturnBound_toNat_of_wf hwf]
    omega
  rw [hlt]
  decide

theorem cureListReturnCopyLoopStepWf {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {n : Nat}
    (hwf : cureStorageWF σ I)
    (hn : n < (cureSlotWord ⟨2⟩ σ I).toNat)
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨405⟩ : UInt256)
      (listReturnCopyOffset n :: listArrayDataPtr ::
        listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
        ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
        ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
        listArrayDataPtr :: listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
        listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) ::
        listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) :: listArrayBasePtr ::
        cureSelWord I :: [])
      (listReturnCopiedMem σ I n) (listReturnCopiedAw σ I n) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨405⟩ : UInt256)
      (listReturnCopyOffset (n + 1) :: listArrayDataPtr ::
        listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
        ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
        ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
        listArrayDataPtr :: listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
        listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) ::
        listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) :: listArrayBasePtr ::
        cureSelWord I :: [])
      (listReturnCopiedMem σ I (n + 1)) (listReturnCopiedAw σ I (n + 1))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, hstep⟩ :=
    cureListReturnCopyLoopStep
      (word := listReturnDataWord σ I n)
      h
      (listReturnCopyLoopContinueCond_of_wf hwf hn)
      (listReturnCopiedMem_mload_src_of_wf hwf hn)
      (by simp)
  exact ⟨_, _, by
    simpa [listReturnCopyOffset, listReturnDataDst, listReturnCopiedMem,
      listReturnCopyStepMem, listReturnCopyStepAw_eq_of_wf hwf (n := n) (by omega)]
      using hstep⟩

theorem cureListReturnCopyLoopRunAux {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwf : cureStorageWF σ I) :
    ∀ rem n k C,
      n + rem = (cureSlotWord ⟨2⟩ σ I).toNat →
      RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨405⟩ : UInt256)
        (listReturnCopyOffset n :: listArrayDataPtr ::
          listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
          ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
          ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
          listArrayDataPtr :: listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) :: listArrayBasePtr ::
          cureSelWord I :: [])
        (listReturnCopiedMem σ I n) (listReturnCopiedAw σ I n) ByteArray.empty
        (cA, σ) k C →
      ∃ k' C', RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨405⟩ : UInt256)
        (listReturnCopyOffset (cureSlotWord ⟨2⟩ σ I).toNat :: listArrayDataPtr ::
          listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
          ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
          ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) ::
          listArrayDataPtr :: listReturnDataDst (cureSlotWord ⟨2⟩ σ I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) :: listArrayBasePtr ::
          cureSelWord I :: [])
        (listReturnCopiedMem σ I (cureSlotWord ⟨2⟩ σ I).toNat)
        (listReturnCopiedAw σ I (cureSlotWord ⟨2⟩ σ I).toNat) ByteArray.empty
        (cA, σ) k' C'
  | 0, n, k, C, hsum, h => by
      have hn : n = (cureSlotWord ⟨2⟩ σ I).toNat := by omega
      subst hn
      exact ⟨k, C, h⟩
  | rem + 1, n, k, C, hsum, h => by
      have hn : n < (cureSlotWord ⟨2⟩ σ I).toNat := by omega
      obtain ⟨k1, C1, hnext⟩ :=
        cureListReturnCopyLoopStepWf (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (n := n) hwf hn h
      exact cureListReturnCopyLoopRunAux hwf rem (n + 1) k1 C1 (by omega) hnext

set_option maxHeartbeats 1000000 in
theorem cureListReturnCopyLoopExit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {i src dst bound fmp arrPtr : UInt256}
    {R : List UInt256} {mem rdata oval : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 (⟨405⟩ : UInt256)
      (i :: src :: dst :: bound :: bound :: src :: dst :: fmp :: fmp :: arrPtr :: R)
      mem aw rdata acc k C)
    (hdone : UInt256.isZero (UInt256.lt i bound) ≠ ⟨0⟩)
    (hload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fmp)
    (hreturn :
      mem.readWithPadding fmp.toNat (UInt256.sub (bound + dst) fmp).toNat = oval)
    (hov : R.length + 12 ≤ 1024) :
    RDret cureBytecode g s0 acc oval := by
  have rd406 := h.jumpdest (by decide +native) (by evm_ov)
  have rd407 := rd406.dup4 (by decide +native) (by evm_ov)
  have rd408 := rd407.dup2 (by decide +native) (by evm_ov)
  have rd409 := rd408.lt (by decide +native) (by evm_ov)
  have rd410 := rd409.iszero (by decide +native) (by evm_ov)
  have rd413 := rd410.push2 ⟨429⟩ (by decide +native) (by evm_ov)
  have rd429 := rd413.jumpiT (by decide +native) hdone (by jump_dest) (by evm_ov)
  have rd430 := rd429.jumpdest (by decide +native) (by evm_ov)
  have rd431 := rd430.pop (by decide +native) (by evm_ov)
  have rd432 := rd431.pop (by decide +native) (by evm_ov)
  have rd433 := rd432.pop (by decide +native) (by evm_ov)
  have rd434 := rd433.pop (by decide +native) (by evm_ov)
  have rd435 := rd434.swap1 (by decide +native) (by evm_ov)
  have rd436 := rd435.pop (by decide +native) (by evm_ov)
  have rd437 := rd436.add (by decide +native) (by evm_ov)
  have rd438 := rd437.swap3 (by decide +native) (by evm_ov)
  have rd439 := rd438.pop (by decide +native) (by evm_ov)
  have rd440 := rd439.pop (by decide +native) (by evm_ov)
  have rd441 := rd440.pop (by decide +native) (by evm_ov)
  have rd443 := rd441.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd444 := rd443.mload (Cₘ (listReturnMload64Aw aw) - Cₘ aw) fmp
    (listReturnMload64Aw aw) (by decide +native)
    (by
      intro s haw hstk
      exact listMloadCost_of_stack (aw := aw) (off := (⟨64⟩ : UInt256))
        (t := (bound + dst) :: R) haw hstk (by rfl))
    hload64 (by rfl) (by evm_ov)
  have rd445 := rd444.dup1 (by decide +native) (by evm_ov)
  have rd446 := rd445.swap2 (by decide +native) (by evm_ov)
  have rd447 := rd446.sub (by decide +native) (by evm_ov)
  have rd448 := rd447.swap1 (by decide +native) (by evm_ov)
  exact rd448.ret
    (Cₘ (UInt256.ofNat
          (MachineState.M (listReturnMload64Aw aw).toNat fmp.toNat
            (UInt256.sub (bound + dst) fmp).toNat)) -
        Cₘ (listReturnMload64Aw aw))
    oval (by decide +native)
    (by
      intro s haw hstk
      exact listReturnCost_of_stack (aw := listReturnMload64Aw aw) (off := fmp)
        (len := UInt256.sub (bound + dst) fmp) (t := R) haw hstk (by rfl))
    hreturn (by omega)

theorem storageLocLoad_addrLoc (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  unfold storageLocLoad addrLoc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE_solcAddrMask]

theorem readStorage_srcsElem_address_ok
    {cA gh bl σ σ₀ A I} {g : Sat256} (idx : Nat) :
    readStorage? config (initState cA gh bl σ σ₀ g A I)
      ({ base := "srcs", steps := [.aindex (.int (Int.ofNat idx))] } : EvaledStorageRef)
      (.elem .address) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx)))) solcAddrMask).toNat)) := by
  simp [readStorage?, config, storageLayout, storageLayoutRaw, solidityStorageLayout,
    storageLocLoad_addrLoc, solcSlotWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem readArrayElems_srcs_address_ok
    {cA gh bl σ σ₀ A I} {g : Sat256} (idx n : Nat) :
    readArrayElems? config (initState cA gh bl σ σ₀ g A I)
      ({ base := "srcs", steps := [] } : EvaledStorageRef) (.elem .address) idx n =
        .ok (listSrcsValuesFrom σ I idx n) := by
  induction n generalizing idx with
  | zero =>
      simp [readArrayElems?, listSrcsValuesFrom]
  | succ n ih =>
      rw [readArrayElems?]
      change
        (do
          let v ← readStorage? config (initState cA gh bl σ σ₀ g A I)
            ({ base := "srcs", steps := [.aindex (.int (Int.ofNat idx))] } : EvaledStorageRef)
            (.elem .address)
          let vrest ← readArrayElems? config (initState cA gh bl σ σ₀ g A I)
            ({ base := "srcs", steps := [] } : EvaledStorageRef) (.elem .address) (idx + 1) n
          pure (v :: vrest)) = .ok (listSrcsValuesFrom σ I idx (n + 1))
      rw [readStorage_srcsElem_address_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) idx]
      rw [ih (idx + 1)]
      rfl

theorem readStorage_srcs_ok {cA gh bl σ σ₀ A I} {g : Sat256} :
    readStorage? config (initState cA gh bl σ σ₀ g A I)
      ({ base := "srcs", steps := [] } : EvaledStorageRef) (.dynamicArray (.elem .address)) =
        .ok (.array (listSrcsValues σ I)) := by
  rw [readStorage?]
  simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
    cureStorageLocLoad_uint256, initState]
  change
    (do
      let vs ← readArrayElems? config (initState cA gh bl σ σ₀ g A I)
        ({ base := "srcs", steps := [] } : EvaledStorageRef) (.elem .address) 0
        (cureSlotWord ⟨2⟩ σ I).toNat
      pure (Value.array vs)) = .ok (Value.array (listSrcsValues σ I))
  rw [readArrayElems_srcs_address_ok]
  rfl

theorem evalExpr_listSrcs_ok {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I) (.storage srcsRef) =
        .ok (.array (listSrcsValues σ I)) := by
  simp [evalExpr?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps,
    srcsRef, config, contract, storageDecls, storageTypeAt?, EvalResult.ofOption,
    EvalResult.bind, bind]
  exact readStorage_srcs_ok (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)

theorem cureListSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256} :
    I.weiValue = ⟨0⟩ →
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ listTransition.body
      (.returned { contract := contract, locals := ∅ }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.array (listSrcsValues σ I)])) := by
  intro hwv
  apply nonpayableReturnExprBodyReturns
  · simp only [initState]
    exact hwv
  · simpa [listTransition] using
      (evalExpr_listSrcs_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g))

theorem listSrcsValuesFrom_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (idx n : Nat) :
    listSrcsValuesFrom σ I idx n = listSrcsValuesFrom τ I idx n := by
  induction n generalizing idx with
  | zero =>
      simp [listSrcsValuesFrom]
  | succ n ih =>
      have hword :
          solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx))) =
            solcSlotWord τ I (srcElemSlot (.int (Int.ofNat idx))) :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner
          (srcElemSlot (.int (Int.ofNat idx))) ⟨0⟩
      simp [listSrcsValuesFrom, ih (idx + 1)]
      exact congrArg
        (fun w => AccountAddress.ofNat ((UInt256.land w solcAddrMask).toNat)) hword

theorem listSrcsValues_eq_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    listSrcsValues σ I = listSrcsValues τ I := by
  have hlen : cureSlotWord ⟨2⟩ σ I = cureSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [listSrcsValues, hlen, listSrcsValuesFrom_eq_of_accountMapEquiv hAccounts]

theorem cureDispatchList {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 7)) :
    dispatchMsg contract I.calldata = some listTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some listTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes]
  decide +native

theorem cureDecode_list {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (listTransition.params.map Param.name)
      (transitionSignature listTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

set_option maxHeartbeats 8000000 in
theorem cureListEmptyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (h929 : ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨929⟩
      [⟨369⟩, cureSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hlen0 : cureSlotWord ⟨2⟩ σ I = ⟨0⟩) :
    RDret cureBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) listEmptyArrayAbi := by
  obtain ⟨_, _, h929⟩ := h929
  obtain ⟨_, _, h936raw⟩ :=
    (evm_run h929 with [jumpdest, push1 ⟨96⟩, push1 ⟨2⟩, dup1]).sload
      (by decide +native) (by evm_ov)
  obtain ⟨_, _, h936⟩ : ∃ k C, RD cureBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨936⟩
      [cureSlotWord ⟨2⟩ σ I, ⟨2⟩, ⟨96⟩, ⟨369⟩, cureSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
    ⟨_, _, by simpa [cureSlotWord, initState] using h936raw⟩
  rw [hlen0] at h936
  have h963 := evm_run h936 with [
    dup1, push1 ⟨32⟩, mul, push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0
      ((UInt256.toByteArray (listRoutineNewFp (⟨0⟩ : UInt256))).write 0 solcFreePtrMem
        (⟨64⟩ : UInt256).toNat 32)
      (UInt256.ofNat 3) (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    dup1, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (listRoutineMem (⟨0⟩ : UInt256)) (UInt256.ofNat 5)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    push1 ⟨32⟩, add, dup3, dup1]
  obtain ⟨_, _, h965raw⟩ := h963.sload (by decide +native) (by evm_ov)
  have hload0 :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) =
        (⟨0⟩ : UInt256) := by
    simpa [cureSlotWord, solcSlotWord] using hlen0
  have h965 := by
    simpa [initState, hload0] using h965raw
  have h369 := evm_run h965 with [
    dup1, iszero, push2 ⟨1017⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, swap1, pop, swap1, jump (by jump_dest)]
  have h400 := evm_run h369 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 _ (UInt256.ofNat 6) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 _ (UInt256.ofNat 7) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, dup2, add, swap2, mul,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have hret := evm_run h400 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨429⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, swap1, pop, add, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run hret with [
    raw ret 0 listEmptyArrayAbi (by decide +native) mem_cost (by decide +native) (by evm_ov)]

theorem cureListBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (_hStorageWF : cureStorageWF σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some listTransition :=
    cureDispatchList hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (listTransition.params.map Param.name)
        (transitionSignature listTransition).paramTypes I.calldata = some ∅ :=
    cureDecode_list hsz
  have hreach := cureReachListBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hentry : solcGetterEntryWf cureBytecode ⟨361⟩ ⟨369⟩ ⟨929⟩ := by
    unfold solcGetterEntryWf
    repeat' first | apply And.intro | decide +native
  obtain ⟨_, _, hroutine⟩ := RD.solcGetterThunk hreach hentry (by jump_dest)
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ listTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.array (listSrcsValues σ_solm I)])) :=
    cureListSourceBodyOk (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
  have hvalues : listSrcsValues σ_evm I = listSrcsValues σ_solm I :=
    listSrcsValues_eq_of_accountMapEquiv hAccounts
  by_cases hlen0 : cureSlotWord ⟨2⟩ σ_evm I = ⟨0⟩
  · have hret := cureListEmptyReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      ⟨_, _, hroutine⟩ hlen0
    have hval :
        some [Value.array (listSrcsValues σ_solm I)] =
          some [Value.array (listSrcsValues σ_evm I)] := by
      rw [hvalues]
    have henc :
        returnEquiv listEmptyArrayAbi (some [Value.array (listSrcsValues σ_evm I)])
          listTransition.returnType := by
      rw [show listTransition.returnType = [addrArray] by rfl]
      rw [listSrcsValues_nil_of_len_zero hlen0]
      exact returnEquiv_of_encode listEmptyArrayReturnEncoding
    exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc
  · have hlenpos : 0 < (cureSlotWord ⟨2⟩ σ_evm I).toNat := by
      by_contra hnot
      have hnat : (cureSlotWord ⟨2⟩ σ_evm I).toNat = 0 := by omega
      apply hlen0
      rw [← u256_ofNat_toNat (cureSlotWord ⟨2⟩ σ_evm I), hnat]
      rfl
    obtain ⟨_, _, h987⟩ := cureListNonemptyToLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      ⟨_, _, hroutine⟩ hlen0
    obtain ⟨_, _, h369⟩ :=
      cureListArrayLoopRunAux
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA := cA) (σ := σ_evm) (_hStorageWF)
        ((cureSlotWord ⟨2⟩ σ_evm I).toNat - 1) 0
        (by omega) h987
    obtain ⟨_, _, h405raw⟩ :=
      cureListReturnFromMemToCopyLoop
        (arrPtr := listArrayBasePtr)
        (fmp := listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I))
        (len := cureSlotWord ⟨2⟩ σ_evm I)
        (R := [cureSelWord I])
        h369
        (listArrayCopiedMem_mload64_of_wf _hStorageWF)
        (listReturnOffsetMem_mload128_of_copied_wf _hStorageWF)
        (listReturnLengthMem_mload128_of_copied_wf _hStorageWF)
        (by simp)
    have h405 : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨405⟩ : UInt256)
        (listReturnCopyOffset 0 :: listArrayDataPtr ::
          listReturnDataDst (cureSlotWord ⟨2⟩ σ_evm I) ::
          ((cureSlotWord ⟨2⟩ σ_evm I) * (⟨32⟩ : UInt256)) ::
          ((cureSlotWord ⟨2⟩ σ_evm I) * (⟨32⟩ : UInt256)) ::
          listArrayDataPtr :: listReturnDataDst (cureSlotWord ⟨2⟩ σ_evm I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I) ::
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I) :: listArrayBasePtr ::
          cureSelWord I :: [])
        (listReturnCopiedMem σ_evm I 0) (listReturnCopiedAw σ_evm I 0)
        ByteArray.empty (cA, σ_evm) k C := by
      exact ⟨_, _, by
        simpa [listReturnCopyOffset, listArrayDataPtr, listReturnDataDst,
          listReturnBaseMem, listReturnCopiedMem,
          listReturnFinalAw_eq_copied_zero_of_wf _hStorageWF] using h405raw⟩
    obtain ⟨k405, C405, h405rd⟩ := h405
    obtain ⟨_, _, h405done⟩ := cureListReturnCopyLoopRunAux
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      _hStorageWF (cureSlotWord ⟨2⟩ σ_evm I).toNat 0 k405 C405
      (by omega) h405rd
    have hdone :
        UInt256.isZero
          (UInt256.lt (listReturnCopyOffset (cureSlotWord ⟨2⟩ σ_evm I).toNat)
            ((cureSlotWord ⟨2⟩ σ_evm I) * (⟨32⟩ : UInt256))) ≠ ⟨0⟩ := by
      have hlt :
          UInt256.lt (listReturnCopyOffset (cureSlotWord ⟨2⟩ σ_evm I).toNat)
            ((cureSlotWord ⟨2⟩ σ_evm I) * (⟨32⟩ : UInt256)) = ⟨0⟩ := by
        apply ult_zero
        rw [listReturnCopyOffset_toNat_of_wf _hStorageWF
            (n := (cureSlotWord ⟨2⟩ σ_evm I).toNat) (by omega),
          listReturnBound_toNat_of_wf _hStorageWF]
      rw [hlt]
      decide
    have hload64 :
        (if (⟨64⟩ : UInt256).toNat ≥
              (listReturnCopiedMem σ_evm I (cureSlotWord ⟨2⟩ σ_evm I).toNat).size
            ∨ (⟨64⟩ : UInt256) ≥
              listReturnCopiedAw σ_evm I (cureSlotWord ⟨2⟩ σ_evm I).toNat * ⟨32⟩
          then ⟨0⟩
          else UInt256.ofNat
            (fromByteArrayBigEndian
              ((listReturnCopiedMem σ_evm I
                (cureSlotWord ⟨2⟩ σ_evm I).toNat).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
          listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I) := by
      exact mloadWordValue_of_readWithPadding
        (by
          rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
            listReturnCopiedMem_size_of_wf _hStorageWF
              (n := (cureSlotWord ⟨2⟩ σ_evm I).toNat) (by omega)]
          omega)
        (wordMul32_not_ge_of_lt
          (by
            rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
              listReturnCopiedAw_toNat_of_wf _hStorageWF
                (n := (cureSlotWord ⟨2⟩ σ_evm I).toNat) (by omega)]
            omega)
          (listReturnCopiedAw_mul32_lt_of_wf _hStorageWF
            (n := (cureSlotWord ⟨2⟩ σ_evm I).toNat) (by omega)))
        (listReturnCopiedMem_read64_of_wf _hStorageWF
          (n := (cureSlotWord ⟨2⟩ σ_evm I).toNat) (by omega))
    have hreturn :
        (listReturnCopiedMem σ_evm I (cureSlotWord ⟨2⟩ σ_evm I).toNat).readWithPadding
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I)).toNat
          (UInt256.sub
            (((cureSlotWord ⟨2⟩ σ_evm I) * (⟨32⟩ : UInt256)) +
              listReturnDataDst (cureSlotWord ⟨2⟩ σ_evm I))
            (listArrayFreePtr (cureSlotWord ⟨2⟩ σ_evm I))).toNat =
          listSrcsReturnBytes σ_evm I :=
      listReturnCopiedMem_read_return_of_wf _hStorageWF hlenpos
    have hret := cureListReturnCopyLoopExit
      (oval := listSrcsReturnBytes σ_evm I)
      h405done hdone hload64 hreturn (by simp)
    have hval :
        some [Value.array (listSrcsValues σ_solm I)] =
          some [Value.array (listSrcsValues σ_evm I)] := by
      rw [hvalues]
    have henc :
        returnEquiv (listSrcsReturnBytes σ_evm I)
          (some [Value.array (listSrcsValues σ_evm I)])
          listTransition.returnType := by
      rw [show listTransition.returnType = [addrArray] by rfl]
      exact returnEquiv_of_encode listSrcsReturnEncoding
    exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

end Benchmarks.Dss.Cure
