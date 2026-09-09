import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `list()` -/

def listSrcsValuesFrom (σ : AccountMap) (I : ExecutionEnv) (idx : Nat) : Nat → List Value
  | 0 => []
  | n + 1 =>
      .address (AccountAddress.ofNat
        (UInt256.land
          (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx)))) solcAddrMask).toNat) ::
        listSrcsValuesFrom σ I (idx + 1) n

def listSrcsValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  listSrcsValuesFrom σ I 0 (cureSlotWord ⟨2⟩ σ I).toNat

def listSrcsWordBytesFrom (σ : AccountMap) (I : ExecutionEnv) (idx : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 =>
      (UInt256.toByteArray
        (UInt256.land (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx))))
          solcAddrMask)).toList ++
      listSrcsWordBytesFrom σ I (idx + 1) n

def listSrcsReturnBytes (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  ⟨(ABI.natBytes 32 ++
    (ABI.natBytes (listSrcsValues σ I).length ++
      listSrcsWordBytesFrom σ I 0 (cureSlotWord ⟨2⟩ σ I).toNat)).toArray⟩

/-- ABI encoding of the empty `address[]` return: offset word `0x20` then length word `0`. -/
def listEmptyArrayAbi : ByteArray :=
  UInt256.toByteArray ⟨32⟩ ++ UInt256.toByteArray ⟨0⟩

def listRoutineNewFp (len : UInt256) : UInt256 :=
  ⟨128⟩ + (⟨32⟩ + UInt256.mul (⟨32⟩ : UInt256) len)

abbrev listArrayBasePtr : UInt256 := ⟨128⟩

abbrev listArrayDataPtr : UInt256 := (⟨32⟩ : UInt256) + listArrayBasePtr

abbrev listArrayAllocSize (len : UInt256) : UInt256 :=
  (⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) len

abbrev listArrayFreePtr (len : UInt256) : UInt256 :=
  listArrayBasePtr + listArrayAllocSize len

def listArrayAllocMem (len : UInt256) : ByteArray :=
  (UInt256.toByteArray (listArrayFreePtr len)).write 0 solcFreePtrMem 64 32

def listRoutineMem (len : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0
    (listArrayAllocMem len)
    (⟨128⟩ : UInt256).toNat 32

theorem listRoutineNewFp_zero :
    listRoutineNewFp (⟨0⟩ : UInt256) = ⟨160⟩ := by
  decide +native

theorem listRoutineNewFp_eq_listArrayFreePtr (len : UInt256) :
    listRoutineNewFp len = listArrayFreePtr len := by
  rfl

theorem listArrayAllocMem_size (len : UInt256) :
    (listArrayAllocMem len).size = 96 := by
  unfold listArrayAllocMem
  exact writeWord_size_of_96 solcFreePtrMem (listArrayFreePtr len) 64
    solcFreePtrMem_size (by omega)

theorem listArrayAllocMem_read64 (len : UInt256) :
    (listArrayAllocMem len).readWithPadding 64 32 =
      UInt256.toByteArray (listArrayFreePtr len) := by
  unfold listArrayAllocMem
  rw [toByteArray_write32_read_back _ _ 64 (by rw [solcFreePtrMem_size]; omega)]

theorem listRoutineMem_size (len : UInt256) :
    (listRoutineMem len).size = 160 := by
  unfold listRoutineMem
  rw [toByteArray_write32_size_of_ge _ len (⟨128⟩ : UInt256).toNat 96 160
    (listArrayAllocMem_size len) (by decide +native) (by decide +native) (by decide +native)]

theorem listRoutineMem_read64 (len : UInt256) :
    (listRoutineMem len).readWithPadding 64 32 =
      UInt256.toByteArray (listArrayFreePtr len) := by
  unfold listRoutineMem
  rw [toByteArray_write_read_below_of_gap len (listArrayAllocMem len)
    (⟨128⟩ : UInt256).toNat 64
    (by rw [listArrayAllocMem_size]) (by decide +native)
    (by rw [listArrayAllocMem_size]; decide +native)]
  exact listArrayAllocMem_read64 len

theorem listRoutineMem_read128 (len : UInt256) :
    (listRoutineMem len).readWithPadding listArrayBasePtr.toNat 32 =
      UInt256.toByteArray len := by
  unfold listRoutineMem
  rw [toByteArray_write_read_back_of_gap len (listArrayAllocMem len)
    (⟨128⟩ : UInt256).toNat
    (by rw [listArrayAllocMem_size]; decide +native)]

theorem listRoutineMem_mload64 (len : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (listRoutineMem len).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((listRoutineMem len).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = listArrayFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, listRoutineMem_size]; omega)
    (by decide +native)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      listRoutineMem_read64 len)

theorem listRoutineMem_mload128 (len : UInt256) :
    (if listArrayBasePtr.toNat ≥ (listRoutineMem len).size
        ∨ listArrayBasePtr ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((listRoutineMem len).readWithPadding listArrayBasePtr.toNat 32)))
      = len := by
  exact mloadWordValue_of_readWithPadding
    (by rw [show listArrayBasePtr.toNat = 128 from by decide, listRoutineMem_size]; omega)
    (by decide +native)
    (by simpa [show listArrayBasePtr.toNat = 128 from by decide] using
      listRoutineMem_read128 len)

abbrev listArrayEndPtr (len : UInt256) : UInt256 :=
  listArrayDataPtr + UInt256.mul (⟨32⟩ : UInt256) len

theorem listArrayDataPtr_toNat :
    listArrayDataPtr.toNat = 160 := by
  decide +native

theorem cureStorageWF_mul32_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    32 * (cureSlotWord ⟨2⟩ σ I).toNat < UInt256.size := by
  have h64u : (2 : Nat) ^ 64 < UInt256.size := by norm_num [UInt256.size]
  have hwf := cureStorageWF_returnBound hwf
  omega

theorem cureStorageWF_alloc_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat < UInt256.size := by
  have h64u : (2 : Nat) ^ 64 < UInt256.size := by norm_num [UInt256.size]
  have hwf := cureStorageWF_returnBound hwf
  omega

theorem cureStorageWF_freePtr_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat < UInt256.size := by
  have h64u : (2 : Nat) ^ 64 < UInt256.size := by norm_num [UInt256.size]
  have hwf := cureStorageWF_returnBound hwf
  omega

theorem cureStorageWF_returnDst_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat < UInt256.size := by
  have h64u : (2 : Nat) ^ 64 < UInt256.size := by norm_num [UInt256.size]
  have hwf := cureStorageWF_returnBound hwf
  omega

theorem cureStorageWF_returnEnd_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat < UInt256.size := by
  have h64 : 224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat < 2 ^ 64 := by
    exact cureStorageWF_returnBound hwf
  have h64u : (2 : Nat) ^ 64 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem cureStorageWF_returnEnd_lt_u64 {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat < 2 ^ 64 := by
  exact cureStorageWF_returnBound hwf

theorem listArrayAllocSize_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listArrayAllocSize (cureSlotWord ⟨2⟩ σ I)).toNat =
      32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [listArrayAllocSize, uadd_toNat, u256_mul_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [Nat.mod_eq_of_lt (cureStorageWF_mul32_lt hwf)]
  exact Nat.mod_eq_of_lt (cureStorageWF_alloc_lt hwf)

theorem listArrayFreePtr_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I)).toNat =
      160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [listArrayFreePtr, uadd_toNat,
    show listArrayBasePtr.toNat = 128 from by decide,
    listArrayAllocSize_toNat_of_wf hwf]
  rw [show 128 + (32 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
    160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
  exact Nat.mod_eq_of_lt (cureStorageWF_freePtr_lt hwf)

theorem listArrayEndPtr_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listArrayEndPtr (cureSlotWord ⟨2⟩ σ I)).toNat =
      160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [listArrayEndPtr, uadd_toNat, u256_mul_toNat,
    listArrayDataPtr_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [Nat.mod_eq_of_lt (cureStorageWF_mul32_lt hwf)]
  exact Nat.mod_eq_of_lt (cureStorageWF_freePtr_lt hwf)

theorem listReturnBound_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)).toNat =
      32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    have h := cureStorageWF_mul32_lt hwf
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem listReturnDst_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨64⟩ : UInt256)).toNat =
      224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [uadd_toNat, listArrayFreePtr_toNat_of_wf hwf,
    show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  rw [show 160 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat + 64 =
    224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
  exact Nat.mod_eq_of_lt (cureStorageWF_returnDst_lt hwf)

theorem listReturnEnd_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) +
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨64⟩ : UInt256))).toNat =
      224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [uadd_toNat, listReturnBound_toNat_of_wf hwf,
    listReturnDst_toNat_of_wf hwf]
  rw [show 32 * (cureSlotWord ⟨2⟩ σ I).toNat +
      (224 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat) =
    224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat by omega]
  exact Nat.mod_eq_of_lt (cureStorageWF_returnEnd_lt hwf)

theorem listReturnSize_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    (UInt256.sub
        (((cureSlotWord ⟨2⟩ σ I) * (⟨32⟩ : UInt256)) +
          (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I) + (⟨64⟩ : UInt256)))
        (listArrayFreePtr (cureSlotWord ⟨2⟩ σ I))).toNat =
      64 + 32 * (cureSlotWord ⟨2⟩ σ I).toNat := by
  rw [usub_toNat]
  · rw [listReturnEnd_toNat_of_wf hwf, listArrayFreePtr_toNat_of_wf hwf]
    omega
  · rw [listReturnEnd_toNat_of_wf hwf, listArrayFreePtr_toNat_of_wf hwf]
    omega

noncomputable def listArrayHashMem (len : UInt256) : ByteArray :=
  wordAt0Mem (⟨2⟩ : UInt256) (listRoutineMem len)

noncomputable def listArrayCopyStepMem
    (σ : AccountMap) (ee : ExecutionEnv) (slot dest : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.land (solcSlotWord σ ee slot) solcAddrMask)).write 0
    mem dest.toNat 32

abbrev listArrayCopyStepAw (aw dest : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat dest.toNat 32)

theorem listArrayHashMem_size (len : UInt256) :
    (listArrayHashMem len).size = 160 := by
  unfold listArrayHashMem wordAt0Mem
  exact toByteArray_write32_size_of_le
    (listRoutineMem len) (⟨2⟩ : UInt256) 0 160 160
    (listRoutineMem_size len) (by omega) (by omega)

theorem listArrayHashMem_read64 (len : UInt256) :
    (listArrayHashMem len).readWithPadding 64 32 =
      UInt256.toByteArray (listArrayFreePtr len) := by
  unfold listArrayHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [listRoutineMem_size]; omega)
    (by omega) (by rw [listRoutineMem_size]; decide +native)]
  exact listRoutineMem_read64 len

theorem listArrayHashMem_read128 (len : UInt256) :
    (listArrayHashMem len).readWithPadding listArrayBasePtr.toNat 32 =
      UInt256.toByteArray len := by
  unfold listArrayHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 listArrayBasePtr.toNat (by rw [toByteArray_size])
    (by rw [listRoutineMem_size]; omega)
    (by decide +native) (by rw [listRoutineMem_size]; decide +native)]
  exact listRoutineMem_read128 len

def listArraySlot : Nat → UInt256
  | 0 => srcsDataSlot
  | n + 1 => (⟨1⟩ : UInt256) + listArraySlot n

def listArrayDest : Nat → UInt256
  | 0 => listArrayDataPtr
  | n + 1 => (⟨32⟩ : UInt256) + listArrayDest n

def listArrayCopiedAw : Nat → UInt256
  | 0 => UInt256.ofNat 5
  | n + 1 => listArrayCopyStepAw (listArrayCopiedAw n) (listArrayDest n)

theorem listArrayDest_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listArrayDest n).toNat = 160 + 32 * n
  | 0, _ => by
      decide +native
  | n + 1, hn => by
      rw [listArrayDest, uadd_toNat, listArrayDest_toNat_of_wf hwf (n := n) (by omega),
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [show 32 + (160 + 32 * n) = 160 + 32 * (n + 1) by omega]
      have hlt : 160 + 32 * (n + 1) < UInt256.size := by
        have hfree := cureStorageWF_freePtr_lt hwf
        have hn' : n + 1 ≤ (cureSlotWord ⟨2⟩ σ I).toNat := hn
        nlinarith
      exact Nat.mod_eq_of_lt hlt

theorem listArrayDest_succ_eq (n : Nat) :
    listArrayDest (n + 1) = (⟨32⟩ : UInt256) + listArrayDest n := by
  rfl

theorem listArraySlot_succ_eq (n : Nat) :
    listArraySlot (n + 1) = (⟨1⟩ : UInt256) + listArraySlot n := by
  rfl

theorem listArraySlot_eq_srcsDataSlot_add_ofNat (n : Nat) :
    listArraySlot n = srcsDataSlot + UInt256.ofNat n := by
  induction n with
  | zero =>
      rw [listArraySlot]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
      have hz : srcsDataSlot + (⟨0⟩ : UInt256) = srcsDataSlot := by
        rw [u256_add_comm, u256_zero_add]
      exact hz.symm
  | succ n ih =>
      rw [listArraySlot, ih, ← u256_one_add_ofNat n]
      rw [u256_add_comm (⟨1⟩ : UInt256) (srcsDataSlot + UInt256.ofNat n)]
      rw [u256_add_assoc, u256_add_comm (UInt256.ofNat n) (⟨1⟩ : UInt256)]

theorem listArraySlot_eq_srcElemSlot_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    listArraySlot n = srcElemSlot (.int (Int.ofNat n)) := by
  have hnlt : n < UInt256.size := by
    have hfree := cureStorageWF_freePtr_lt hwf
    omega
  have hnat : (UInt256.ofNat n).toNat = n := UInt256.toNat_ofNat_of_lt hnlt
  rw [listArraySlot_eq_srcsDataSlot_add_ofNat, srcElemSlot]
  conv_rhs => rw [← hnat]
  rw [keyValueToWord_uint256]

theorem listArrayNextDest_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n + 1 ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    ((⟨32⟩ : UInt256) + listArrayDest n).toNat = 160 + 32 * (n + 1) := by
  rw [← listArrayDest_succ_eq]
  exact listArrayDest_toNat_of_wf hwf hn

theorem listArrayLoopGuard_true_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n + 1 < (cureSlotWord ⟨2⟩ σ I).toNat) :
    UInt256.gt (listArrayEndPtr (cureSlotWord ⟨2⟩ σ I))
        ((⟨32⟩ : UInt256) + listArrayDest n) = ⟨1⟩ := by
  apply ugt_one
  rw [listArrayEndPtr_toNat_of_wf hwf, listArrayNextDest_toNat_of_wf hwf (by omega)]
  omega

theorem listArrayLoopGuard_false_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n + 1 = (cureSlotWord ⟨2⟩ σ I).toNat) :
    UInt256.gt (listArrayEndPtr (cureSlotWord ⟨2⟩ σ I))
        ((⟨32⟩ : UInt256) + listArrayDest n) = ⟨0⟩ := by
  apply ugt_zero
  rw [listArrayEndPtr_toNat_of_wf hwf, listArrayNextDest_toNat_of_wf hwf (by omega)]
  omega

noncomputable def listArrayCopiedMem
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) : Nat → ByteArray
  | 0 => listArrayHashMem len
  | n + 1 =>
      (UInt256.toByteArray
        (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)).write 0
        (listArrayCopiedMem σ ee len n) (160 + 32 * n) 32

theorem listArrayCopiedMem_size
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (listArrayCopiedMem σ ee len n).size = 160 + 32 * n
  | 0 => by
      rw [listArrayCopiedMem, listArrayHashMem_size]
  | n + 1 => by
      rw [listArrayCopiedMem]
      exact toByteArray_write32_size_of_ge
        (listArrayCopiedMem σ ee len n)
        (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)
        (160 + 32 * n) (160 + 32 * n) (160 + 32 * (n + 1))
        (listArrayCopiedMem_size σ ee len n) (by omega)
        (by
          have hU : 0 < USize.size := by decide +native
          omega)
        (by omega)

theorem listArrayCopiedMem_read64
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (listArrayCopiedMem σ ee len n).readWithPadding 64 32 =
      UInt256.toByteArray (listArrayFreePtr len)
  | 0 => by
      rw [listArrayCopiedMem]
      exact listArrayHashMem_read64 len
  | n + 1 => by
      rw [listArrayCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)
        (listArrayCopiedMem σ ee len n) (160 + 32 * n) 64
        (by rw [listArrayCopiedMem_size]; omega)
        (by omega)
        (by
          rw [listArrayCopiedMem_size]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listArrayCopiedMem_read64 σ ee len n

theorem listArrayCopiedMem_read128
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (listArrayCopiedMem σ ee len n).readWithPadding listArrayBasePtr.toNat 32 =
      UInt256.toByteArray len
  | 0 => by
      rw [listArrayCopiedMem]
      exact listArrayHashMem_read128 len
  | n + 1 => by
      rw [listArrayCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)
        (listArrayCopiedMem σ ee len n) (160 + 32 * n) listArrayBasePtr.toNat
        (by
          rw [listArrayCopiedMem_size]
          have hbase : listArrayBasePtr.toNat = 128 := by decide +native
          omega)
        (by
          have hbase : listArrayBasePtr.toNat = 128 := by decide +native
          omega)
        (by
          rw [listArrayCopiedMem_size]
          have hU : 0 < USize.size := by decide +native
          omega)]
      exact listArrayCopiedMem_read128 σ ee len n

theorem listArrayCopiedMem_read_elem
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n i, i < n →
      (listArrayCopiedMem σ ee len n).readWithPadding (160 + 32 * i) 32 =
        UInt256.toByteArray
          (UInt256.land (solcSlotWord σ ee (listArraySlot i)) solcAddrMask)
  | 0, i, hi => by omega
  | n + 1, i, hi => by
      rw [listArrayCopiedMem]
      by_cases hlast : i = n
      · subst i
        rw [toByteArray_write_read_back_of_gap
          (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)
          (listArrayCopiedMem σ ee len n) (160 + 32 * n)
          (by
            rw [listArrayCopiedMem_size]
            have hU : 0 < USize.size := by decide +native
            omega)]
      · have hi' : i < n := by omega
        rw [toByteArray_write_read_below_of_gap
          (UInt256.land (solcSlotWord σ ee (listArraySlot n)) solcAddrMask)
          (listArrayCopiedMem σ ee len n) (160 + 32 * n) (160 + 32 * i)
          (by rw [listArrayCopiedMem_size]; omega)
          (by omega)
          (by
            rw [listArrayCopiedMem_size]
            have hU : 0 < USize.size := by decide +native
            omega)]
        exact listArrayCopiedMem_read_elem σ ee len n i hi'

theorem listArrayHashMem_keccak_slot (len : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((listArrayHashMem len).readWithPadding (⟨0⟩ : UInt256).toNat
            (⟨32⟩ : UInt256).toNat))) =
      srcsDataSlot := by
  simpa [listArrayHashMem, srcsDataSlot, uInt256OfByteArray_eq,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
    wordAt0Mem_keccak_word (⟨2⟩ : UInt256) (listRoutineMem len)

theorem listArrayCopiedMem_mload64
    (σ : AccountMap) (ee : ExecutionEnv) (len aw : UInt256) (n : Nat)
    (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (listArrayCopiedMem σ ee len n).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((listArrayCopiedMem σ ee len n).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = listArrayFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, listArrayCopiedMem_size]
      omega)
    haw
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      listArrayCopiedMem_read64 σ ee len n)

theorem listArrayCopyStepMem_eq_copied_succ_of_wf
    {σ : AccountMap} {I : ExecutionEnv} (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n + 1 ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    listArrayCopyStepMem σ I (listArraySlot n) (listArrayDest n)
        (listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I) n) =
      listArrayCopiedMem σ I (cureSlotWord ⟨2⟩ σ I) (n + 1) := by
  unfold listArrayCopyStepMem
  rw [listArrayCopiedMem, listArrayDest_toNat_of_wf hwf (n := n) (by omega)]

theorem wordMul32_not_ge_of_lt {off aw : UInt256}
    (hlt : off.toNat < aw.toNat * 32)
    (hNoWrap : aw.toNat * 32 < UInt256.size) :
    ¬ off ≥ aw * ⟨32⟩ := by
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hge
  have h : off.toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hge
  rw [hmul] at h
  omega

theorem machineState_M_endWrite (aw : Nat) :
    MachineState.M aw (32 * aw) 32 = aw + 1 := by
  show max aw ((32 * aw + 32 + 31) / 32) = aw + 1
  rw [show 32 * aw + 32 + 31 = 32 * (aw + 1) + 31 from by ring,
    Nat.mul_add_div (by norm_num), show (31 : Nat) / 32 = 0 from by norm_num]
  omega

theorem machineState_M_inBounds {s f l : Nat} (h : f + l ≤ 32 * s) :
    MachineState.M s f l = s := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [MachineState.M, hl]
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    show max s ((f + (l' + 1) + 31) / 32) = s
    have hlt : (f + (l' + 1) + 31) / 32 < s + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      omega
    omega

theorem listArrayCopiedAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    ∀ {n}, n ≤ (cureSlotWord ⟨2⟩ σ I).toNat →
      (listArrayCopiedAw n).toNat = 5 + n
  | 0, _ => by
      rw [listArrayCopiedAw]
      exact ulit_toNat' 5 (by norm_num [UInt256.size])
  | n + 1, hn => by
      rw [listArrayCopiedAw, listArrayCopyStepAw, UInt256.toNat_ofNat_of_lt]
      · rw [listArrayCopiedAw_toNat_of_wf hwf (n := n) (by omega),
          listArrayDest_toNat_of_wf hwf (n := n) (by omega)]
        rw [show 160 + 32 * n = 32 * (5 + n) by omega]
        rw [machineState_M_endWrite]
        omega
      · rw [listArrayCopiedAw_toNat_of_wf hwf (n := n) (by omega),
          listArrayDest_toNat_of_wf hwf (n := n) (by omega)]
        rw [show 160 + 32 * n = 32 * (5 + n) by omega]
        rw [machineState_M_endWrite]
        have hfree := cureStorageWF_freePtr_lt hwf
        omega

theorem listArrayCopiedAw_mul32_lt_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) {n : Nat}
    (hn : n ≤ (cureSlotWord ⟨2⟩ σ I).toNat) :
    (listArrayCopiedAw n).toNat * 32 < UInt256.size := by
  rw [listArrayCopiedAw_toNat_of_wf hwf hn]
  have hfree := cureStorageWF_freePtr_lt hwf
  nlinarith

theorem listRoutineMem_zero :
    listRoutineMem (⟨0⟩ : UInt256) =
      (UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray ⟨160⟩).write 0 solcFreePtrMem (⟨64⟩ : UInt256).toNat 32)
        (⟨128⟩ : UInt256).toNat 32 := by
  unfold listRoutineMem
  unfold listArrayAllocMem
  decide +native

theorem listSrcsValues_nil_of_len_zero {σ : AccountMap} {I : ExecutionEnv}
    (hlen : cureSlotWord ⟨2⟩ σ I = ⟨0⟩) :
    listSrcsValues σ I = [] := by
  simp [listSrcsValues, hlen, listSrcsValuesFrom]

theorem listSrcsValuesFrom_length {σ : AccountMap} {I : ExecutionEnv} :
    ∀ idx n, (listSrcsValuesFrom σ I idx n).length = n
  | _, 0 => rfl
  | idx, n + 1 => by
      simp [listSrcsValuesFrom, listSrcsValuesFrom_length (idx + 1) n]

theorem listSrcsValues_length {σ : AccountMap} {I : ExecutionEnv} :
    (listSrcsValues σ I).length = (cureSlotWord ⟨2⟩ σ I).toNat := by
  unfold listSrcsValues
  rw [listSrcsValuesFrom_length]

theorem listSrcsWordBytesFrom_length {σ : AccountMap} {I : ExecutionEnv} :
    ∀ idx n, (listSrcsWordBytesFrom σ I idx n).length = 32 * n
  | _, 0 => rfl
  | idx, n + 1 => by
      have hwordLen :
          ((UInt256.toByteArray
            (UInt256.land (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx))))
              solcAddrMask)).toList).length = 32 := by
        rw [← word_toBytesBE_toByteArray_eq_toByteArray, byteArray_toList_eq,
          Array.length_toList]
        simpa using
          word_toBytesBE_toByteArray_size
            (UInt256.land (solcSlotWord σ I (srcElemSlot (.int (Int.ofNat idx))))
              solcAddrMask)
      simp only [listSrcsWordBytesFrom, List.length_append,
        listSrcsWordBytesFrom_length (idx + 1) n]
      rw [hwordLen]
      omega

theorem encodeABIValue_address_masked (w : UInt256) :
    encodeABIValue? addr
      (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
        some (UInt256.toByteArray (UInt256.land w solcAddrMask)).toList := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat =
      UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  have hbytes :
      (UInt256.toByteArray (UInt256.land w solcAddrMask)).toList =
        EVM.Word.toBytesBE (UInt256.land w solcAddrMask) := by
    rw [toByteArray_eq_toBytesBE, byteArray_toList_eq]
  rw [hbytes]
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

theorem encodeABIStaticArrayElems_listSrcsValuesFrom
    {σ : AccountMap} {I : ExecutionEnv} :
    ∀ idx n,
      encodeABIStaticArrayElems? addr (listSrcsValuesFrom σ I idx n) =
        some (listSrcsWordBytesFrom σ I idx n)
  | _, 0 => by
      simp [listSrcsValuesFrom, listSrcsWordBytesFrom, encodeABIStaticArrayElems?]
  | idx, n + 1 => by
      simp only [listSrcsValuesFrom, listSrcsWordBytesFrom, encodeABIStaticArrayElems?,
        bind, Option.bind]
      rw [encodeABIValue_address_masked,
        encodeABIStaticArrayElems_listSrcsValuesFrom (idx + 1) n]

theorem listSrcsReturnEncoding {σ : AccountMap} {I : ExecutionEnv} :
    encodeReturnValues? [addrArray] [.array (listSrcsValues σ I)] =
      some (listSrcsReturnBytes σ I) := by
  unfold encodeReturnValues?
  rw [show encodeABIValues? [addrArray] [.array (listSrcsValues σ I)] =
      (encodeABIStaticArrayElems? addr (listSrcsValues σ I)).bind
        (fun e => some (ABI.natBytes 32 ++
          (ABI.natBytes (listSrcsValues σ I).length ++ e))) from by
        simpa [addrArray, addr] using
          (encodeABIValues_single_dynArray_static
            (elemTy := addr) (vs := listSrcsValues σ I) (by rfl))]
  unfold listSrcsValues listSrcsReturnBytes
  rw [encodeABIStaticArrayElems_listSrcsValuesFrom]
  rfl

noncomputable def wordConcat (f : Nat → UInt256) (idx : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => (f idx).toByteArray ++ wordConcat f (idx + 1) n

@[simp] theorem wordConcat_zero (f : Nat → UInt256) (idx : Nat) :
    wordConcat f idx 0 = ByteArray.empty := rfl

theorem wordConcat_succ (f : Nat → UInt256) (idx n : Nat) :
    wordConcat f idx (n + 1) = (f idx).toByteArray ++ wordConcat f (idx + 1) n := rfl

theorem wordConcat_congr (f g : Nat → UInt256) :
    ∀ (n idx : Nat), (∀ k, k < n → f (idx + k) = g (idx + k)) →
      wordConcat f idx n = wordConcat g idx n
  | 0, _, _ => rfl
  | n + 1, idx, h => by
      rw [wordConcat_succ, wordConcat_succ]
      have h0 : f idx = g idx := by simpa using h 0 (Nat.zero_lt_succ n)
      rw [h0, wordConcat_congr f g n (idx + 1) (by
        intro k hk
        have := h (k + 1) (Nat.succ_lt_succ hk)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)]

theorem readWithPadding_wordConcat (mem : ByteArray) (f : Nat → UInt256) (base : Nat) :
    ∀ (n idx : Nat), 32 * n < 2 ^ 64 → base + 32 * idx + 32 * n ≤ mem.size →
      (∀ k, k < n → mem.readWithPadding (base + 32 * (idx + k)) 32 =
        (f (idx + k)).toByteArray) →
      mem.readWithPadding (base + 32 * idx) (32 * n) = wordConcat f idx n
  | 0, idx, _, _, _ => by
      rw [Nat.mul_zero, byteArray_readWithPadding_zero, wordConcat_zero]
  | n + 1, idx, hlt, hin, hread => by
      have hsplit :
          mem.readWithPadding (base + 32 * idx) (32 + 32 * n) =
            mem.readWithPadding (base + 32 * idx) 32 ++
              mem.readWithPadding (base + 32 * idx + 32) (32 * n) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [Nat.mul_zero, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
        · exact byteArray_readWithPadding_split mem (base + 32 * idx) 32 (32 * n)
            (by norm_num) (by omega) (by norm_num) (by omega) (by omega)
            (by rw [Nat.mul_succ] at hin; omega)
      rw [Nat.mul_succ, Nat.add_comm (32 * n) 32, hsplit, wordConcat_succ]
      have hw0 : mem.readWithPadding (base + 32 * idx) 32 = (f idx).toByteArray := by
        have := hread 0 (Nat.zero_lt_succ n)
        simpa using this
      rw [hw0]
      have htail : mem.readWithPadding (base + 32 * idx + 32) (32 * n) =
          wordConcat f (idx + 1) n := by
        have hbase' : base + 32 * idx + 32 = base + 32 * (idx + 1) := by ring
        rw [hbase']
        exact readWithPadding_wordConcat mem f base n (idx + 1)
          (by rw [Nat.mul_succ] at hlt; omega)
          (by
            rw [Nat.mul_succ] at hin
            rw [show base + 32 * (idx + 1) = base + 32 * idx + 32 from by ring]
            omega)
          (by
            intro k hk
            have := hread (k + 1) (Nat.succ_lt_succ hk)
            simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
      rw [htail]

theorem listEmptyArrayReturnEncoding :
    encodeReturnValues? [addrArray] [.array []] = some listEmptyArrayAbi := by
  decide +native


end Benchmarks.Dss.Cure
