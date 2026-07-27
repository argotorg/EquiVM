import Benchmarks.Dss.Clipper.ListBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperListReturnCopyIndex_zero :
    clipperListReturnCopyIndex 0 = (⟨0⟩ : UInt256) := by
  native_decide

theorem clipperListReturnCopyIndex_toNat {n : Nat}
    (h : 32 * n < UInt256.size) :
    (clipperListReturnCopyIndex n).toNat = 32 * n :=
  ulit_toNat' _ h

theorem clipperListReturnCopyIndex_succ {n : Nat}
    (h : 32 * (n + 1) < UInt256.size) :
    (⟨32⟩ : UInt256) + clipperListReturnCopyIndex n =
      clipperListReturnCopyIndex (n + 1) := by
  apply u256_inj
  rw [uadd_toNat, clipperListReturnCopyIndex_toNat (n := n) (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    clipperListReturnCopyIndex_toNat (n := n + 1) h]
  rw [show 32 + 32 * n = 32 * (n + 1) by omega]
  exact Nat.mod_eq_of_lt h

theorem clipperListReturnCopySrc_toNat {σ : AccountMap} {I : ExecutionEnv} {n : Nat}
    (hwf : clipperStorageWF σ I) (hn : n ≤ (solcSlotWord σ I ⟨11⟩).toNat) :
    (clipperListReturnCopyIndex n + ((⟨32⟩ : UInt256) + clipperListArrayBasePtr)).toNat =
      160 + 32 * n := by
  rw [uadd_toNat, clipperListReturnCopyIndex_toNat (by
      have h := clipperStorageWF_mul32_lt hwf
      omega),
    show (((⟨32⟩ : UInt256) + clipperListArrayBasePtr).toNat) = 160 from by native_decide]
  rw [show 32 * n + 160 = 160 + 32 * n by omega]
  rw [Nat.mod_eq_of_lt (by
    have hfree := clipperStorageWF_freePtr_lt hwf
    omega)]

theorem clipperListReturnCopyDst_toNat {σ : AccountMap} {I : ExecutionEnv} {n : Nat}
    (hwf : clipperStorageWF σ I) (hn : n ≤ (solcSlotWord σ I ⟨11⟩).toNat) :
    (clipperListReturnCopyIndex n +
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256))).toNat =
      224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n := by
  rw [uadd_toNat, clipperListReturnCopyIndex_toNat (by
      have h := clipperStorageWF_mul32_lt hwf
      omega),
    clipperListReturnDst_toNat_of_wf hwf]
  rw [show 32 * n + (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat) =
    224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n by omega]
  rw [Nat.mod_eq_of_lt (by
    have hend := clipperStorageWF_returnEnd_lt hwf
    omega)]

theorem not_u256_ge_of_toNat_lt {a b : UInt256} (h : a.toNat < b.toNat) : ¬ a ≥ b := by
  intro hge
  have hnat : b.toNat ≤ a.toNat := hge
  omega

theorem u256_mul32_toNat_of_toNat {a : UInt256} {n : Nat}
    (ha : a.toNat = n) (h : 32 * n < UInt256.size) :
    (a * (⟨32⟩ : UInt256)).toNat = 32 * n := by
  rw [umul_toNat a (⟨32⟩ : UInt256) (by
    rw [ha, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega), ha, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  omega

theorem clipperM_return_mload64 (n : Nat) :
    MachineState.M (5 + n) 64 32 = 5 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_storeOffset (n : Nat) :
    MachineState.M (5 + n) (160 + 32 * n) 32 = 6 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_mload128_from6 (n : Nat) :
    MachineState.M (6 + n) 128 32 = 6 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_storeLength (n : Nat) :
    MachineState.M (6 + n) (192 + 32 * n) 32 = 7 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_mload128_from7 (n : Nat) :
    MachineState.M (7 + n) 128 32 = 7 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_copy_mload (n k : Nat) :
    MachineState.M (7 + n + k) (160 + 32 * k) 32 = 7 + n + k := by
  unfold MachineState.M
  simp only []
  omega

theorem clipperM_return_copy_mstore (n k : Nat) :
    MachineState.M (7 + n + k) (224 + 32 * n + 32 * k) 32 = 8 + n + k := by
  unfold MachineState.M
  simp only []
  omega

noncomputable abbrev clipperListReturnBaseMem (σ : AccountMap) (ee : ExecutionEnv) :
    ByteArray :=
  clipperListReturnLengthMem (solcSlotWord σ ee ⟨11⟩)
    (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩))
    (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩)
      (solcSlotWord σ ee ⟨11⟩).toNat)

noncomputable def clipperListReturnCopiedMem
    (σ : AccountMap) (ee : ExecutionEnv) : Nat → ByteArray
  | 0 => clipperListReturnBaseMem σ ee
  | n + 1 =>
      (UInt256.toByteArray (solcSlotWord σ ee (clipperListArraySlot n))).write 0
        (clipperListReturnCopiedMem σ ee n)
        (224 + 32 * (solcSlotWord σ ee ⟨11⟩).toNat + 32 * n) 32

theorem clipperListReturnBaseMem_size {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).size =
      224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  have harr :
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat).size =
        160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat :=
    clipperListArrayCopiedMem_size σ I (solcSlotWord σ I ⟨11⟩)
      (solcSlotWord σ I ⟨11⟩).toNat
  have hoff :
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
      harr
      (by rw [clipperListArrayFreePtr_toNat_of_wf hwf])
      (by
        rw [clipperListArrayFreePtr_toNat_of_wf hwf]
        have hU : 0 < USize.size := by native_decide
        omega)
      (by
        rw [clipperListArrayFreePtr_toNat_of_wf hwf]
        omega)
  unfold clipperListReturnBaseMem clipperListReturnLengthMem
  exact toByteArray_write32_size_of_ge
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat))
    (solcSlotWord σ I ⟨11⟩)
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat
    (192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat)
    (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat)
    hoff
    (by rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf])
    (by
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      have hU : 0 < USize.size := by native_decide
      omega)
    (by
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      omega)

theorem clipperListReturnCopiedMem_size {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ n, n ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnCopiedMem σ I n).size =
        224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n
  | 0, _ => by
      rw [clipperListReturnCopiedMem, clipperListReturnBaseMem_size hwf]
      omega
  | n + 1, hn => by
      have hn' : n ≤ (solcSlotWord σ I ⟨11⟩).toNat := by omega
      rw [clipperListReturnCopiedMem]
      exact toByteArray_write32_size_of_ge
        (clipperListReturnCopiedMem σ I n)
        (solcSlotWord σ I (clipperListArraySlot n))
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * n)
        (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 * (n + 1))
        (clipperListReturnCopiedMem_size hwf n hn')
        (by omega)
        (by
          have hU : 0 < USize.size := by native_decide
          omega)
        (by omega)

theorem clipperListReturnOffsetMem_read128_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
        (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
          (solcSlotWord σ I ⟨11⟩).toNat)).readWithPadding 128 32 =
      UInt256.toByteArray (solcSlotWord σ I ⟨11⟩) := by
  unfold clipperListReturnOffsetMem
  rw [toByteArray_write_read_below_of_gap
    (⟨32⟩ : UInt256)
    (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
      (solcSlotWord σ I ⟨11⟩).toNat)
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat 128
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
  exact clipperListArrayCopiedMem_read128 σ I (solcSlotWord σ I ⟨11⟩)
    (solcSlotWord σ I ⟨11⟩).toNat

theorem clipperListReturnBaseMem_read64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)) := by
  unfold clipperListReturnBaseMem clipperListReturnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (solcSlotWord σ I ⟨11⟩)
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat))
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat 64
    (by
      unfold clipperListReturnOffsetMem
      rw [toByteArray_write32_size_of_ge
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
          omega)]
      omega)
    (by
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      omega)
    (by
      unfold clipperListReturnOffsetMem
      rw [toByteArray_write32_size_of_ge
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
          omega)]
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold clipperListReturnOffsetMem
  rw [toByteArray_write_read_below_of_gap
    (⟨32⟩ : UInt256)
    (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
      (solcSlotWord σ I ⟨11⟩).toNat)
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat 64
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
  exact clipperListArrayCopiedMem_read64 σ I (solcSlotWord σ I ⟨11⟩)
    (solcSlotWord σ I ⟨11⟩).toNat

theorem clipperListReturnBaseMem_read128_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseMem σ I).readWithPadding 128 32 =
      UInt256.toByteArray (solcSlotWord σ I ⟨11⟩) := by
  unfold clipperListReturnBaseMem clipperListReturnLengthMem
  rw [toByteArray_write_read_below_of_gap
    (solcSlotWord σ I ⟨11⟩)
    (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
      (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat))
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat 128
    (by
      unfold clipperListReturnOffsetMem
      rw [toByteArray_write32_size_of_ge
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
          omega)]
      omega)
    (by
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      omega)
    (by
      unfold clipperListReturnOffsetMem
      rw [toByteArray_write32_size_of_ge
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
          omega)]
      rw [clipperListArrayFreePtrAdd32_toNat_of_wf hwf]
      have hU : 0 < USize.size := by native_decide
      omega)]
  exact clipperListReturnOffsetMem_read128_of_wf hwf

theorem clipperListArrayCopiedMem_mload64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
            (solcSlotWord σ I ⟨11⟩).toNat).size
        ∨ (⟨64⟩ : UInt256) ≥
          clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
          (solcSlotWord σ I ⟨11⟩).toNat).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) := by
  apply mloadWordValue_of_readWithPadding
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      clipperListArrayCopiedMem_size]
    omega
  · apply not_u256_ge_of_toNat_lt
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      u256_mul32_toNat_of_toNat
        (clipperListArrayCopiedAw_toNat (clipperStorageWF_freePtr_lt hwf))]
    · omega
    · unfold clipperStorageWF at hwf
      omega
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clipperListArrayCopiedMem_read64 σ I (solcSlotWord σ I ⟨11⟩)
        (solcSlotWord σ I ⟨11⟩).toNat

theorem clipperListReturnOffsetMem_mload128_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (if clipperListArrayBasePtr.toNat ≥
          (clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
            (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
              (solcSlotWord σ I ⟨11⟩).toNat)).size
        ∨ clipperListArrayBasePtr ≥
          clipperListReturnOffsetAw
            (clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat)
            (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnOffsetMem (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
          (clipperListArrayCopiedMem σ I (solcSlotWord σ I ⟨11⟩)
            (solcSlotWord σ I ⟨11⟩).toNat)).readWithPadding
          clipperListArrayBasePtr.toNat 32)))
      = solcSlotWord σ I ⟨11⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [show clipperListArrayBasePtr.toNat = 128 from by decide]
    unfold clipperListReturnOffsetMem
    rw [toByteArray_write32_size_of_ge
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
        omega)]
    omega
  · apply not_u256_ge_of_toNat_lt
    rw [show clipperListArrayBasePtr.toNat = 128 from by decide]
    have haw : (clipperListReturnOffsetAw
        (clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat)
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))).toNat =
        6 + (solcSlotWord σ I ⟨11⟩).toNat := by
      unfold clipperListReturnOffsetAw clipperListReturnMload64Aw
      rw [clipperListArrayCopiedAw_toNat (clipperStorageWF_freePtr_lt hwf)]
      have h5 :
          (UInt256.ofNat
              (MachineState.M (5 + (solcSlotWord σ I ⟨11⟩).toNat)
                (⟨64⟩ : UInt256).toNat 32)).toNat =
            5 + (solcSlotWord σ I ⟨11⟩).toNat := by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          clipperM_return_mload64]
        exact ulit_toNat' _ (by
          unfold clipperStorageWF at hwf
          omega)
      rw [h5, clipperListArrayFreePtr_toNat_of_wf hwf, clipperM_return_storeOffset]
      exact ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)
    rw [u256_mul32_toNat_of_toNat haw (by
      unfold clipperStorageWF at hwf
      omega)]
    omega
  · simpa [show clipperListArrayBasePtr.toNat = 128 from by decide] using
      clipperListReturnOffsetMem_read128_of_wf hwf

theorem clipperListReturnBaseMem_mload128_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (if clipperListArrayBasePtr.toNat ≥ (clipperListReturnBaseMem σ I).size
        ∨ clipperListArrayBasePtr ≥
          clipperListReturnLengthAw
            (clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat)
            (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
            clipperListArrayBasePtr * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnBaseMem σ I).readWithPadding clipperListArrayBasePtr.toNat 32)))
      = solcSlotWord σ I ⟨11⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [show clipperListArrayBasePtr.toNat = 128 from by decide,
      clipperListReturnBaseMem_size hwf]
    omega
  · apply not_u256_ge_of_toNat_lt
    rw [show clipperListArrayBasePtr.toNat = 128 from by decide]
    have haw : (clipperListReturnLengthAw
        (clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat)
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
        clipperListArrayBasePtr).toNat =
        7 + (solcSlotWord σ I ⟨11⟩).toNat := by
      unfold clipperListReturnLengthAw clipperListReturnArrayMloadAw
      unfold clipperListReturnOffsetAw clipperListReturnMload64Aw
      rw [clipperListArrayCopiedAw_toNat (clipperStorageWF_freePtr_lt hwf),
        clipperListArrayFreePtr_toNat_of_wf hwf,
        show clipperListArrayBasePtr.toNat = 128 from by decide,
        clipperListArrayFreePtrAdd32_toNat_of_wf hwf,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [clipperM_return_mload64]
      have h5 : (UInt256.ofNat (5 + (solcSlotWord σ I ⟨11⟩).toNat)).toNat =
          5 + (solcSlotWord σ I ⟨11⟩).toNat := ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)
      rw [h5, clipperM_return_storeOffset]
      have h6 : (UInt256.ofNat (6 + (solcSlotWord σ I ⟨11⟩).toNat)).toNat =
          6 + (solcSlotWord σ I ⟨11⟩).toNat := ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)
      rw [h6, clipperM_return_mload128_from6, h6, clipperM_return_storeLength]
      exact ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)
    rw [u256_mul32_toNat_of_toNat haw]
    · omega
    · unfold clipperStorageWF at hwf
      omega
  · simpa [show clipperListArrayBasePtr.toNat = 128 from by decide] using
      clipperListReturnBaseMem_read128_of_wf hwf

abbrev clipperListReturnBaseAw (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  clipperListReturnFinalAw (clipperListArrayCopiedAw (solcSlotWord σ ee ⟨11⟩).toNat)
    (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩)) clipperListArrayBasePtr

def clipperListReturnCopiedAw (σ : AccountMap) (ee : ExecutionEnv) : Nat → UInt256
  | 0 => clipperListReturnBaseAw σ ee
  | n + 1 =>
      clipperListReturnCopyStepAw (clipperListReturnCopiedAw σ ee n)
        ((⟨32⟩ : UInt256) + clipperListArrayBasePtr)
        (clipperListArrayFreePtr (solcSlotWord σ ee ⟨11⟩) + (⟨64⟩ : UInt256))
        (clipperListReturnCopyIndex n)

theorem clipperListReturnBaseAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListReturnBaseAw σ I).toNat =
      7 + (solcSlotWord σ I ⟨11⟩).toNat := by
  unfold clipperListReturnBaseAw clipperListReturnFinalAw clipperListReturnLengthAw
  unfold clipperListReturnArrayMloadAw clipperListReturnOffsetAw clipperListReturnMload64Aw
  rw [clipperListArrayCopiedAw_toNat (clipperStorageWF_freePtr_lt hwf)]
  rw [clipperListArrayFreePtr_toNat_of_wf hwf]
  rw [show clipperListArrayBasePtr.toNat = 128 from by decide]
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  rw [show (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat =
      192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat by
    rw [uadd_toNat, clipperListArrayFreePtr_toNat_of_wf hwf,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show 160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 =
      192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat by omega]
    rw [Nat.mod_eq_of_lt (by
      have h := clipperStorageWF_returnDst_lt hwf
      omega)]]
  rw [clipperM_return_mload64]
  have h5 : (UInt256.ofNat (5 + (solcSlotWord σ I ⟨11⟩).toNat)).toNat =
      5 + (solcSlotWord σ I ⟨11⟩).toNat := ulit_toNat' _ (by
    unfold clipperStorageWF at hwf
    omega)
  rw [h5]
  rw [clipperM_return_storeOffset]
  have h6 : (UInt256.ofNat (6 + (solcSlotWord σ I ⟨11⟩).toNat)).toNat =
      6 + (solcSlotWord σ I ⟨11⟩).toNat := ulit_toNat' _ (by
    unfold clipperStorageWF at hwf
    omega)
  rw [h6]
  rw [clipperM_return_mload128_from6]
  rw [h6]
  rw [clipperM_return_storeLength]
  have h7 : (UInt256.ofNat (7 + (solcSlotWord σ I ⟨11⟩).toNat)).toNat =
      7 + (solcSlotWord σ I ⟨11⟩).toNat := ulit_toNat' _ (by
    unfold clipperStorageWF at hwf
    omega)
  rw [h7]
  rw [clipperM_return_mload128_from7]
  exact h7

theorem clipperListReturnBaseMem_mload64_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperListReturnBaseMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ clipperListReturnBaseAw σ I * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListReturnBaseMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) := by
  apply mloadWordValue_of_readWithPadding
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      clipperListReturnBaseMem_size hwf]
    omega
  · apply not_u256_ge_of_toNat_lt
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      u256_mul32_toNat_of_toNat (clipperListReturnBaseAw_toNat_of_wf hwf) (by
        unfold clipperStorageWF at hwf
        omega)]
    omega
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clipperListReturnBaseMem_read64_of_wf hwf

theorem clipperListReturnCopiedAw_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ∀ n, n ≤ (solcSlotWord σ I ⟨11⟩).toNat →
      (clipperListReturnCopiedAw σ I n).toNat =
        7 + (solcSlotWord σ I ⟨11⟩).toNat + n
  | 0, _ => by
      rw [clipperListReturnCopiedAw, clipperListReturnBaseAw_toNat_of_wf hwf]
      omega
  | n + 1, hn => by
      have hn' : n ≤ (solcSlotWord σ I ⟨11⟩).toNat := by omega
      have hprev := clipperListReturnCopiedAw_toNat_of_wf hwf n hn'
      rw [clipperListReturnCopiedAw, clipperListReturnCopyStepAw]
      unfold clipperListReturnCopyMloadAw
      rw [hprev, clipperListReturnCopySrc_toNat hwf hn']
      rw [clipperM_return_copy_mload]
      have h7n :
          (UInt256.ofNat (7 + (solcSlotWord σ I ⟨11⟩).toNat + n)).toNat =
            7 + (solcSlotWord σ I ⟨11⟩).toNat + n := ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)
      rw [h7n, clipperListReturnCopyDst_toNat hwf hn']
      rw [clipperM_return_copy_mstore]
      rw [ulit_toNat' _ (by
        unfold clipperStorageWF at hwf
        omega)]
      omega

end Benchmarks.Dss.Clipper
