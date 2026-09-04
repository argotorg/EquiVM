import Benchmarks.Dss.Clipper.ListStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperStorageWF_returnSize_lt_u64 {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    64 + 32 * (solcSlotWord σ I ⟨11⟩).toNat < 2 ^ 64 := by
  simpa [clipperStorageWF] using hwf.2.1

theorem clipperMk_toArray_eq (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  rw [← List.data_toByteArray]

theorem clipperNatBytes_toByteArray (n : Nat) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) := by
  show (EVM.Word.toBytesBE (UInt256.ofNat n)).toByteArray = _
  exact word_toBytesBE_toByteArray_eq_toByteArray _

theorem clipperUInt256_toByteArray_natBytes (w : UInt256) :
    UInt256.toByteArray w = ⟨(ABI.natBytes w.toNat).toArray⟩ := by
  symm
  rw [clipperMk_toArray_eq, clipperNatBytes_toByteArray, u256_ofNat_toNat]

theorem clipperKeyValueToWord_int_ofNat_of_lt {n : Nat} (hn : n < UInt256.size) :
    keyValueToWord (.int (Int.ofNat n)) = UInt256.ofNat n := by
  have hto : (UInt256.ofNat n).toNat = n := ulit_toNat' n hn
  simpa [hto] using keyValueToWord_uint256 (UInt256.ofNat n)

theorem clipperUInt256_one_add_ofNat_of_lt {n : Nat} (hn : n + 1 < UInt256.size) :
    (⟨1⟩ : UInt256) + UInt256.ofNat n = UInt256.ofNat (n + 1) := by
  apply u256_inj
  rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 from by decide,
    ulit_toNat' n (by omega), ulit_toNat' (n + 1) hn]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem clipperListArraySlot_eq_activeSlot_of_lt :
    ∀ n, n < UInt256.size → clipperListArraySlot n = activeSlot (.int (Int.ofNat n))
  | 0, _ => by
      unfold clipperListArraySlot activeSlot
      rw [clipperKeyValueToWord_int_ofNat_of_lt (n := 0) (by native_decide)]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]
      rw [u256_add_comm activeDataSlot (⟨0⟩ : UInt256), u256_zero_add]
  | n + 1, hn => by
      have hn' : n < UInt256.size := by omega
      rw [clipperListArraySlot, clipperListArraySlot_eq_activeSlot_of_lt n hn']
      unfold activeSlot
      rw [clipperKeyValueToWord_int_ofNat_of_lt hn,
        clipperKeyValueToWord_int_ofNat_of_lt hn']
      rw [← u256_add_assoc, u256_add_comm (⟨1⟩ : UInt256) activeDataSlot,
        u256_add_assoc, clipperUInt256_one_add_ofNat_of_lt hn]

def clipperListArrayWordBytesFrom (σ : AccountMap) (I : ExecutionEnv) : Nat → Nat → List UInt8
  | _, 0 => []
  | k, n + 1 =>
      EVM.Word.toBytesBE (solcSlotWord σ I (clipperListArraySlot k)) ++
        clipperListArrayWordBytesFrom σ I (k + 1) n

theorem clipperActiveArrayWordBytesFrom_eq_listSlots
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    ∀ k n, k + n < UInt256.size →
      clipperActiveArrayWordBytesFrom (initState cA gh bl σ σ₀ g A I) k n =
        clipperListArrayWordBytesFrom σ I k n
  | _, 0, _ => rfl
  | k, n + 1, hbound => by
      have hk : k < UInt256.size := by omega
      have hslot := clipperListArraySlot_eq_activeSlot_of_lt k hk
      have hload :
          Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
              (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
              (activeSlot (.int (Int.ofNat k))) =
            solcSlotWord σ I (clipperListArraySlot k) := by
        rw [← hslot]
        simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord]
      rw [clipperActiveArrayWordBytesFrom, clipperListArrayWordBytesFrom, hload,
        clipperActiveArrayWordBytesFrom_eq_listSlots (k + 1) n (by omega)]

theorem clipperListReturnOffsetMem_size_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat)).size =
      192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  unfold clipperListReturnOffsetMem
  exact toByteArray_write32_size_of_ge
    (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
      (solcSlotWord σ I ⟨11⟩).toNat)
    (⟨32⟩ : UInt256)
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
    (160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat)
    (192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat)
    (clipperListArrayCopiedMem_size σ I (solcSlotWord σ I ⟨11⟩)
      (solcSlotWord σ I ⟨11⟩).toNat)
    (by rw [clipperListArrayFreePtr_toNat_of_wf hwf])
    (by
      rw [clipperListArrayFreePtr_toNat_of_wf hwf]
      have hU : 0 < USize.size := by native_decide
      omega)
    (by
      rw [clipperListArrayFreePtr_toNat_of_wf hwf]
      omega)

theorem clipperListReturnBaseMem_read_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ i, i < (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnBaseMem σ I).readWithPadding (160 + 32 * i) 32 =
        UInt256.toByteArray (solcSlotWord σ I (clipperListArraySlot i))
  | i, hi => by
      unfold clipperListReturnBaseMem clipperListReturnLengthMem
      rw [toByteArray_write_read_below_of_gap
        (solcSlotWord σ I ⟨11⟩)
        (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
          (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
            (solcSlotWord σ I ⟨11⟩).toNat))
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat
        (160 + 32 * i)
        (by
          rw [clipperListReturnOffsetMem_size_of_wf hwf]
          omega)
        (by
          rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
          omega)
        (by
          rw [clipperListReturnOffsetMem_size_of_wf hwf,
            clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
          have hU : 0 < USize.size := by native_decide
          omega)]
      unfold clipperListReturnOffsetMem
      rw [toByteArray_write_read_below_of_gap
        (⟨32⟩ : UInt256)
        (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
          (solcSlotWord σ I ⟨11⟩).toNat)
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
        (160 + 32 * i)
        (by
          rw [clipperListArrayCopiedMem_size]
          omega)
        (by
          rw [clipperListArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by
          rw [clipperListArrayCopiedMem_size, clipperListArrayFreePtr_toNat_of_wf hwf]
          have hU : 0 < USize.size := by native_decide
          omega)]
      exact clipperListArrayCopiedMem_read_elem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat i hi

theorem clipperListReturnCopiedMem_read_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ k i, k ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      i < (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnCopiedMem σ I k).readWithPadding (160 + 32 * i) 32 =
        UInt256.toByteArray (solcSlotWord σ I (clipperListArraySlot i))
  | 0, i, _hk, hi => clipperListReturnBaseMem_read_src_of_wf hwf i hi
  | k + 1, i, hk, hi => by
      have hk' : k ≤ (solcSlotWord σ I ⟨11⟩).toNat := by omega
      rw [clipperListReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (solcSlotWord σ I (clipperListArraySlot k))
        (clipperListReturnCopiedMem σ I k)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * k)
        (160 + 32 * i)
        (by
          rw [clipperListReturnCopiedMem_size hwf k hk']
          omega)
        (by omega)
        (by
          rw [clipperListReturnCopiedMem_size hwf k hk']
          have hU : 0 < USize.size := by native_decide
          omega)]
      exact clipperListReturnCopiedMem_read_src_of_wf hwf k i hk' hi

theorem clipperListReturnCopiedMem_read64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ k, k ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnCopiedMem σ I k).readWithPadding 64 32 =
        UInt256.toByteArray (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
  | 0, _ => clipperListReturnBaseMem_read64_of_wf hwf
  | k + 1, hk => by
      have hk' : k ≤ (solcSlotWord σ I ⟨11⟩).toNat := by omega
      rw [clipperListReturnCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (solcSlotWord σ I (clipperListArraySlot k))
        (clipperListReturnCopiedMem σ I k)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * k)
        64
        (by
          rw [clipperListReturnCopiedMem_size hwf k hk']
          omega)
        (by omega)
        (by
          rw [clipperListReturnCopiedMem_size hwf k hk']
          have hU : 0 < USize.size := by native_decide
          omega)]
      exact clipperListReturnCopiedMem_read64_of_wf hwf k hk'

theorem clipperListReturnCopiedMem_mload64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ k, k ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperListReturnCopiedMem σ I k).size
          ∨ (⟨64⟩ : UInt256) ≥ clipperListReturnCopiedAw σ I k * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((clipperListReturnCopiedMem σ I k).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)
  | k, hk => by
      apply mloadWordValue_of_readWithPadding
      · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          clipperListReturnCopiedMem_size hwf k hk]
        omega
      · apply not_u256_ge_of_toNat_lt
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          u256_mul32_toNat_of_toNat (clipperListReturnCopiedAw_toNat_of_wf hwf k hk) (by
            unfold clipperStorageWF at hwf
            omega)]
        omega
      · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
          clipperListReturnCopiedMem_read64_of_wf hwf k hk

theorem clipperListReturnCopiedMem_mload_src_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ k, k < (solcSlotWord σ I ⟨11⟩).toNat →
      (if (clipperListReturnCopyIndex k + ((⟨32⟩ : UInt256) + clipperListArrayBasePtr)).toNat
            ≥ (clipperListReturnCopiedMem σ I k).size
          ∨ (clipperListReturnCopyIndex k + ((⟨32⟩ : UInt256) + clipperListArrayBasePtr))
            ≥ clipperListReturnCopiedAw σ I k * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((clipperListReturnCopiedMem σ I k).readWithPadding
             (clipperListReturnCopyIndex k + ((⟨32⟩ : UInt256) + clipperListArrayBasePtr)).toNat
             32))) =
        solcSlotWord σ I (clipperListArraySlot k)
  | k, hk => by
      apply mloadWordValue_of_readWithPadding
      · rw [clipperListReturnCopySrc_toNat hwf (by omega),
          clipperListReturnCopiedMem_size hwf k (by omega)]
        omega
      · apply not_u256_ge_of_toNat_lt
        rw [clipperListReturnCopySrc_toNat hwf (by omega),
          u256_mul32_toNat_of_toNat (clipperListReturnCopiedAw_toNat_of_wf hwf k (by omega)) (by
            unfold clipperStorageWF at hwf
            omega)]
        omega
      · rw [clipperListReturnCopySrc_toNat hwf (n := k) (by omega)]
        exact clipperListReturnCopiedMem_read_src_of_wf hwf k k (by omega) hk

theorem clipperListReturnCopyStepMem_eq_copied {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) {k : Nat}
    (hk : k ≤ (solcSlotWord σ I ⟨11⟩).toNat) :
    clipperListReturnCopyStepMem (solcSlotWord σ I (clipperListArraySlot k))
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256))
        (clipperListReturnCopyIndex k)
        (clipperListReturnCopiedMem σ I k) =
      clipperListReturnCopiedMem σ I (k + 1) := by
  unfold clipperListReturnCopyStepMem
  rw [clipperListReturnCopyDst_toNat hwf hk, clipperListReturnCopiedMem]

theorem clipperListArrayWordBytesFrom_succ_right (σ : AccountMap) (I : ExecutionEnv) :
    ∀ k n,
      clipperListArrayWordBytesFrom σ I k (n + 1) =
        clipperListArrayWordBytesFrom σ I k n ++
          EVM.Word.toBytesBE (solcSlotWord σ I (clipperListArraySlot (k + n)))
  | k, 0 => by
      simp [clipperListArrayWordBytesFrom]
  | k, n + 1 => by
      change
        EVM.Word.toBytesBE (solcSlotWord σ I (clipperListArraySlot k)) ++
            clipperListArrayWordBytesFrom σ I (k + 1) (n + 1) =
          (EVM.Word.toBytesBE (solcSlotWord σ I (clipperListArraySlot k)) ++
              clipperListArrayWordBytesFrom σ I (k + 1) n) ++
            EVM.Word.toBytesBE (solcSlotWord σ I (clipperListArraySlot (k + (n + 1))))
      rw [clipperListArrayWordBytesFrom_succ_right σ I (k + 1) n]
      rw [List.append_assoc]
      rw [show k + 1 + n = k + (n + 1) by omega]

theorem clipperActiveArrayReturnBytes_eq_listSlots
    {cA gh bl σ σ₀ A I} {g : Sat256} (hwf : clipperStorageWF σ I) :
    clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A I) =
      ⟨(ABI.natBytes 32 ++ ABI.natBytes (solcSlotWord σ I ⟨11⟩).toNat ++
        clipperListArrayWordBytesFrom σ I 0 (solcSlotWord σ I ⟨11⟩).toNat).toArray⟩ := by
  have hlen :
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨11⟩ =
        solcSlotWord σ I ⟨11⟩ := by
    simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord]
  unfold clipperActiveArrayReturnBytes clipperActiveArrayValues
  rw [hlen]
  rw [clipperActiveArrayValuesFrom_length]
  rw [clipperActiveArrayWordBytesFrom_eq_listSlots 0 (solcSlotWord σ I ⟨11⟩).toNat]
  · rw [List.append_assoc]
  · have h := clipperStorageWF_returnEnd_lt hwf
    omega

theorem clipperListReturnBaseMem_read_fmp_offset_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).readWithPadding
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat 32 =
      UInt256.toByteArray (⟨32⟩ : UInt256) := by
  unfold clipperListReturnBaseMem clipperListReturnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (solcSlotWord σ I ⟨11⟩)
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat))
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
    (by
      rw [clipperListReturnOffsetMem_size_of_wf hwf,
        clipperListArrayFreePtr_toNat_of_wf hwf]
      omega)
    (by
      rw [clipperListArrayFreePtr_toNat_of_wf hwf,
        clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      omega)
    (by
      rw [clipperListReturnOffsetMem_size_of_wf hwf,
        clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold clipperListReturnOffsetMem
  rw [toByteArray_write_read_back_of_gap]
  rw [clipperListArrayCopiedMem_size, clipperListArrayFreePtr_toNat_of_wf hwf]
  have hU : 0 < USize.size := by native_decide
  omega

theorem clipperListReturnBaseMem_read_fmp_length_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).readWithPadding
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray (solcSlotWord σ I ⟨11⟩) := by
  unfold clipperListReturnBaseMem clipperListReturnLengthMem
  rw [toByteArray_write_read_back_of_gap]
  rw [clipperListReturnOffsetMem_size_of_wf hwf, clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
  have hU : 0 < USize.size := by native_decide
  omega

theorem clipperListReturnBaseMem_returnBytes_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).readWithPadding
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat 64 =
      UInt256.toByteArray (⟨32⟩ : UInt256) ++
        UInt256.toByteArray (solcSlotWord σ I ⟨11⟩) := by
  rw [byteArray_readWithPadding_split (clipperListReturnBaseMem σ I)
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [clipperListReturnBaseMem_size hwf, clipperListArrayFreePtr_toNat_of_wf hwf]
      omega)]
  rw [clipperListReturnBaseMem_read_fmp_offset_of_wf hwf]
  rw [show (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat + 32 =
      (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat by
    rw [clipperListArrayFreePtr_toNat_of_wf hwf,
      clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
    omega]
  rw [clipperListReturnBaseMem_read_fmp_length_of_wf hwf]

set_option maxHeartbeats 1000000 in
theorem clipperListReturnCopiedMem_returnBytes_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ n, n ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnCopiedMem σ I n).readWithPadding
          (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat (64 + 32 * n) =
        UInt256.toByteArray (⟨32⟩ : UInt256) ++
          UInt256.toByteArray (solcSlotWord σ I ⟨11⟩) ++
          (clipperListArrayWordBytesFrom σ I 0 n).toByteArray
  | 0, _ => by
      rw [clipperListReturnCopiedMem, show 64 + 32 * 0 = 64 by omega,
        clipperListReturnBaseMem_returnBytes_of_wf hwf]
      simp [clipperListArrayWordBytesFrom, ByteArray.append_empty]
  | n + 1, hn => by
      have hn' : n ≤ (solcSlotWord σ I ⟨11⟩).toNat := by omega
      rw [show 64 + 32 * (n + 1) = (64 + 32 * n) + 32 by omega]
      rw [byteArray_readWithPadding_split
        (clipperListReturnCopiedMem σ I (n + 1))
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
        (64 + 32 * n) 32
        (by omega) (by omega)
        (by
          have h := clipperStorageWF_returnSize_lt_u64 hwf
          omega)
        (by norm_num)
        (by
          have h := clipperStorageWF_returnSize_lt_u64 hwf
          omega)
        (by
          rw [clipperListReturnCopiedMem_size hwf (n + 1) hn,
            clipperListArrayFreePtr_toNat_of_wf hwf]
          omega)]
      rw [clipperListReturnCopiedMem]
      rw [toByteArray_write_read_below_len_of_gap
        (solcSlotWord σ I (clipperListArraySlot n))
        (clipperListReturnCopiedMem σ I n)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n)
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
        (64 + 32 * n)
        (by
          rw [clipperListReturnCopiedMem_size hwf n hn',
            clipperListArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by
          rw [clipperListArrayFreePtr_toNat_of_wf hwf]
          omega)
        (by omega)
        (by
          have h := clipperStorageWF_returnSize_lt_u64 hwf
          omega)
        (by
          rw [clipperListReturnCopiedMem_size hwf n hn']
          have hU : 0 < USize.size := by native_decide
          omega)]
      rw [show (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat +
          (64 + 32 * n) =
          224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n by
        rw [clipperListArrayFreePtr_toNat_of_wf hwf]
        omega]
      rw [toByteArray_write_read_back_of_gap
        (solcSlotWord σ I (clipperListArraySlot n))
        (clipperListReturnCopiedMem σ I n)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n)]
      · rw [clipperListReturnCopiedMem_returnBytes_of_wf hwf n hn']
        rw [clipperListArrayWordBytesFrom_succ_right σ I 0 n, List.toByteArray_append,
          word_toBytesBE_toByteArray_eq_toByteArray]
        simp [ByteArray.append_assoc]
      · rw [clipperListReturnCopiedMem_size hwf n hn']
        have hU : 0 < USize.size := by native_decide
        omega

theorem clipperListReturnCopiedMem_activeReturnBytes_of_wf
    {cA gh bl σ σ₀ A I} {g : Sat256} (hwf : clipperStorageWF σ I) :
    (clipperListReturnCopiedMem σ I (solcSlotWord σ I ⟨11⟩).toNat).readWithPadding
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat
        (UInt256.sub
          (((solcSlotWord σ I ⟨11⟩) * (⟨32⟩ : UInt256)) +
            (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256)))
          (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))).toNat =
      clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A I) := by
  rw [clipperListReturnSize_toNat_of_wf hwf]
  rw [clipperListReturnCopiedMem_returnBytes_of_wf hwf
    (solcSlotWord σ I ⟨11⟩).toNat le_rfl]
  rw [clipperActiveArrayReturnBytes_eq_listSlots hwf]
  rw [clipperUInt256_toByteArray_natBytes (⟨32⟩ : UInt256),
    clipperUInt256_toByteArray_natBytes (solcSlotWord σ I ⟨11⟩)]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  simp [clipperMk_toArray_eq, List.toByteArray_append, ByteArray.append_assoc]

set_option maxHeartbeats 1000000 in
theorem clipperListReturnCopyLoopFrom {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {gh bl σ₀ A}
    {σ : AccountMap}
    (hwfStorage : clipperStorageWF σ ee)
    (hwf : clipperListReturnFromMemWf code)
    (h548 : (D_J code 0).contains (⟨548⟩ : UInt256) = true)
    (h572 : (D_J code 0).contains (⟨572⟩ : UInt256) = true)
    (hov : R.length + 14 ≤ 1024) :
    ∀ m k,
      (solcSlotWord σ ee ⟨11⟩).toNat = k + m →
      (∀ k₀ C₀,
        RD code ee g s0 (⟨548⟩ : UInt256)
          (clipperListReturnCopyIndex k ::
            ((⟨32⟩ : UInt256) + clipperListArrayBasePtr) ::
            (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)) ::
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) ::
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) ::
            ((⟨32⟩ : UInt256) + clipperListArrayBasePtr) ::
            (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)) ::
            clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
            clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
            clipperListArrayBasePtr :: R)
          (clipperListReturnCopiedMem σ ee k)
          (clipperListReturnCopiedAw σ ee k) rdata (cA, σ) k₀ C₀ →
        RDret code g s0 (cA, σ)
          (clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A ee))) := by
  intro m
  induction m with
  | zero =>
      intro k hn k₀ C₀ hrd
      have hk : k ≤ (solcSlotWord σ ee ⟨11⟩).toNat := by omega
      have hidxBound : 32 * k < UInt256.size := by
        have h := clipperStorageWF_mul32_lt hwfStorage
        omega
      have hlt :
          UInt256.lt (clipperListReturnCopyIndex k)
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) = ⟨0⟩ := by
        apply ult_zero
        rw [clipperListReturnCopyIndex_toNat (n := k) hidxBound,
          clipperListReturnBound_toNat_of_wf hwfStorage, hn]
        omega
      have hdone :
          UInt256.isZero (UInt256.lt (clipperListReturnCopyIndex k)
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256))) ≠ ⟨0⟩ := by
        rw [hlt]
        native_decide
      have hreturn :
          (clipperListReturnCopiedMem σ ee k).readWithPadding
              (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩)).toNat
              (UInt256.sub
                (((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) +
                  (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)))
                (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩))).toNat =
            clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A ee) := by
        simpa [hn] using
          (clipperListReturnCopiedMem_activeReturnBytes_of_wf
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := ee) (g := g) hwfStorage)
      exact clipperListReturnCopyLoopExit
        (i := clipperListReturnCopyIndex k)
        (src := ((⟨32⟩ : UInt256) + clipperListArrayBasePtr))
        (dst := (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)))
        (bound := ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)))
        (fmp := clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩))
        (arrPtr := clipperListArrayBasePtr) (R := R) hrd hwf h572 hdone
        (clipperListReturnCopiedMem_mload64_of_wf hwfStorage k hk)
        hreturn (by omega)
  | succ m ih =>
      intro k hn k₀ C₀ hrd
      have hkLe : k ≤ (solcSlotWord σ ee ⟨11⟩).toNat := by omega
      have hkLt : k < (solcSlotWord σ ee ⟨11⟩).toNat := by omega
      have hidxBoundSucc : 32 * (k + 1) < UInt256.size := by
        have h := clipperStorageWF_mul32_lt hwfStorage
        omega
      have hidxSucc := clipperListReturnCopyIndex_succ (n := k) hidxBoundSucc
      have hlt :
          UInt256.lt (clipperListReturnCopyIndex k)
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) = ⟨1⟩ := by
        apply ult_one
        rw [clipperListReturnCopyIndex_toNat (n := k) (by omega),
          clipperListReturnBound_toNat_of_wf hwfStorage]
        omega
      have hcont :
          UInt256.isZero (UInt256.lt (clipperListReturnCopyIndex k)
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256))) = ⟨0⟩ := by
        rw [hlt]
        native_decide
      obtain ⟨kNext, CNext, rdnextRaw⟩ :=
        clipperListReturnCopyLoopStep
          (R :=
            ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) ::
            ((⟨32⟩ : UInt256) + clipperListArrayBasePtr) ::
            (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)) ::
            clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
            clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
            clipperListArrayBasePtr :: R)
          hrd hwf h548 hcont
          (clipperListReturnCopiedMem_mload_src_of_wf hwfStorage k hkLt)
          (by simp only [List.length_cons]; omega)
      have hmem := clipperListReturnCopyStepMem_eq_copied hwfStorage (k := k) hkLe
      have hnNext : (solcSlotWord σ ee ⟨11⟩).toNat = (k + 1) + m := by omega
      have rdnext :
          RD code ee g s0 (⟨548⟩ : UInt256)
            (clipperListReturnCopyIndex (k + 1) ::
              ((⟨32⟩ : UInt256) + clipperListArrayBasePtr) ::
              (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)) ::
              ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) ::
              ((solcSlotWord σ ee ⟨11⟩) * (⟨32⟩ : UInt256)) ::
              ((⟨32⟩ : UInt256) + clipperListArrayBasePtr) ::
              (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256)) ::
              clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
              clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) ::
              clipperListArrayBasePtr :: R)
            (clipperListReturnCopiedMem σ ee (k + 1))
            (clipperListReturnCopiedAw σ ee (k + 1)) rdata (cA, σ) kNext CNext := by
        simpa [hidxSucc, hmem, clipperListReturnCopiedAw] using rdnextRaw
      exact ih (k + 1) hnNext kNext CNext rdnext

theorem clipperListReturnLengthMem_empty_returnBytes :
    (clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
        (clipperListArrayLengthMem ⟨0⟩)).readWithPadding
      (clipperListArrayFreePtr ⟨0⟩).toNat
      (UInt256.sub
        ((⟨0⟩ : UInt256) + (clipperListArrayFreePtr ⟨0⟩ + (⟨64⟩ : UInt256)))
        (clipperListArrayFreePtr ⟨0⟩)).toNat =
      ⟨(ABI.natBytes 32 ++ ABI.natBytes 0).toArray⟩ := by
  unfold clipperListReturnLengthMem clipperListReturnOffsetMem
  unfold clipperListArrayLengthMem clipperListArrayAllocMem
  unfold clipperListArrayFreePtr clipperListArrayAllocSize clipperListArrayBasePtr
  native_decide

theorem clipperListReturnLengthMem_empty_mload128 :
    (if clipperListArrayBasePtr.toNat ≥
          (clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
            (clipperListArrayLengthMem ⟨0⟩)).size
        ∨ clipperListArrayBasePtr ≥
          clipperListReturnLengthAw (UInt256.ofNat 5) (clipperListArrayFreePtr ⟨0⟩)
            clipperListArrayBasePtr * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
          (clipperListArrayLengthMem ⟨0⟩)).readWithPadding clipperListArrayBasePtr.toNat 32)))
      = (⟨0⟩ : UInt256) := by
  unfold clipperListReturnLengthMem clipperListReturnOffsetMem
  unfold clipperListArrayLengthMem clipperListArrayAllocMem
  unfold clipperListReturnLengthAw clipperListReturnArrayMloadAw clipperListReturnOffsetAw
  unfold clipperListReturnMload64Aw clipperListArrayFreePtr clipperListArrayAllocSize
  unfold clipperListArrayBasePtr
  native_decide

theorem clipperListReturnOffsetMem_empty_mload128 :
    (if clipperListArrayBasePtr.toNat ≥
          (clipperListReturnOffsetMem (clipperListArrayFreePtr ⟨0⟩)
            (clipperListArrayLengthMem ⟨0⟩)).size
        ∨ clipperListArrayBasePtr ≥
          clipperListReturnOffsetAw (UInt256.ofNat 5) (clipperListArrayFreePtr ⟨0⟩) *
            ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnOffsetMem (clipperListArrayFreePtr ⟨0⟩)
          (clipperListArrayLengthMem ⟨0⟩)).readWithPadding clipperListArrayBasePtr.toNat 32)))
      = (⟨0⟩ : UInt256) := by
  unfold clipperListReturnOffsetMem clipperListArrayLengthMem clipperListArrayAllocMem
  unfold clipperListReturnOffsetAw clipperListReturnMload64Aw clipperListArrayFreePtr
  unfold clipperListArrayAllocSize clipperListArrayBasePtr
  native_decide

theorem clipperListReturnLengthMem_empty_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥
          (clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
            (clipperListArrayLengthMem ⟨0⟩)).size
        ∨ (⟨64⟩ : UInt256) ≥
          clipperListReturnFinalAw (UInt256.ofNat 5) (clipperListArrayFreePtr ⟨0⟩)
            clipperListArrayBasePtr * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
          (clipperListArrayLengthMem ⟨0⟩)).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = clipperListArrayFreePtr ⟨0⟩ := by
  unfold clipperListReturnLengthMem clipperListReturnOffsetMem
  unfold clipperListArrayLengthMem clipperListArrayAllocMem
  unfold clipperListReturnFinalAw clipperListReturnLengthAw clipperListReturnArrayMloadAw
  unfold clipperListReturnOffsetAw clipperListReturnMload64Aw clipperListArrayFreePtr
  unfold clipperListArrayAllocSize clipperListArrayBasePtr
  native_decide

theorem clipperActiveArrayReturnBytes_empty {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlen : solcSlotWord σ I ⟨11⟩ = ⟨0⟩) :
    clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A I) =
      ⟨(ABI.natBytes 32 ++ ABI.natBytes 0).toArray⟩ := by
  unfold clipperActiveArrayReturnBytes clipperActiveArrayValues
  simp only [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord] at hlen ⊢
  rw [hlen]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide]
  simp only [clipperActiveArrayValuesFrom, clipperActiveArrayWordBytesFrom, List.length_nil]
  native_decide

abbrev clipperListEmptyFmp : UInt256 := clipperListArrayFreePtr ⟨0⟩

abbrev clipperListEmptySrc : UInt256 :=
  (⟨32⟩ : UInt256) + clipperListArrayBasePtr

abbrev clipperListEmptyDst : UInt256 :=
  clipperListEmptyFmp + (⟨64⟩ : UInt256)

abbrev clipperListEmptyBound : UInt256 :=
  (⟨0⟩ : UInt256) * ⟨32⟩

end Benchmarks.Dss.Clipper
