import Benchmarks.CompoundIII.Comet.ScalarWrites
import Benchmarks.CompoundIII.Comet.InitializeWords
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: replacement of any of four uint64 fields in a packed word.
def uint64FieldWrite (old data : UInt256) (field : Fin 4) : UInt256 :=
  let mask := UInt256.shiftLeft ⟨2^64-1⟩ (UInt256.ofNat (64 * field.val))
  UInt256.lor (UInt256.land mask (UInt256.shiftLeft data (UInt256.ofNat (64 * field.val))))
    (UInt256.land (UInt256.lnot mask) old)

theorem uint64FieldWrite_bits (x y : BitVec 256) (field : Fin 3) :
    x % BitVec.ofNat 256 (256^(8 * field.val)) +
      BitVec.ofNat 256 (256^(8 * field.val)) * (y % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^(8 * field.val + 8)) *
        (x / BitVec.ofNat 256 (256^(8 * field.val + 8))) =
    ((BitVec.ofNat 256 (2^64-1) <<< (64 * field.val)) &&& (y <<< (64 * field.val))) |||
      ((~~~(BitVec.ofNat 256 (2^64-1) <<< (64 * field.val))) &&& x) := by
  fin_cases field <;> bv_decide

theorem uint64FieldWrite_packed (old data : UInt256) (field : Fin 4) :
    packedWriteWord old data (8 * field.val) 8 = uint64FieldWrite old data field := by
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨data.val⟩
  by_cases hf : field.val < 3
  · rw [packedWriteWord_bitvec x y (8 * field.val) 8 (by omega) (by decide) (by omega)]
    have hb := uint64FieldWrite_bits x y ⟨field.val, hf⟩
    rw [hb]
    apply congrArg UInt256.mk
    simp only [UInt256.land, UInt256.lnot,
      BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
    have he : field.val = 0 ∨ field.val = 1 ∨ field.val = 2 := by omega
    rcases he with he | he | he <;> rw [he] <;> rfl
  · have he : field.val = 3 := by omega
    have hd : old.toNat / 256^(8 * field.val + 8) = 0 := by
      rw [he]
      exact Nat.div_eq_of_lt old.val.isLt
    unfold packedWriteWord
    rw [hd, Nat.mul_zero, Nat.add_zero, he]
    apply congrArg UInt256.mk
    change (BitVec.ofNat 256 (x.toNat % 256^24 + 256^24 * (y.toNat % 256^8))).toFin = _
    rw [BitVec.ofNat_add, BitVec.ofNat_mul, bitvecOfNatMod x _ (by decide),
      bitvecOfNatMod y _ (by decide)]
    have hb : x % BitVec.ofNat 256 (256^24) +
        BitVec.ofNat 256 (256^24) * (y % BitVec.ofNat 256 (256^8)) =
        ((BitVec.ofNat 256 (2^64-1) <<< 192) &&& (y <<< 192)) |||
          ((~~~(BitVec.ofNat 256 (2^64-1) <<< 192)) &&& x) := by bv_decide
    rw [hb]
    simp only [he, UInt256.land, UInt256.lnot,
      BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
    rfl

theorem uint64FieldWrite_zero (old data : UInt256) :
    uint64FieldWrite old data 0 =
      UInt256.lor (UInt256.land data ⟨2^64-1⟩)
        (UInt256.land (UInt256.lnot ⟨2^64-1⟩) old) := by
  have hz (word : UInt256) : UInt256.shiftLeft word ⟨0⟩ = word := by
    apply u256_inj
    simp [UInt256.shiftLeft, UInt256.toNat, Fin.shiftLeft_val, Nat.shiftLeft_zero,
      Nat.mod_eq_of_lt word.val.isLt]
  change UInt256.lor
    (UInt256.land (UInt256.shiftLeft ⟨2^64-1⟩ ⟨0⟩) (UInt256.shiftLeft data ⟨0⟩))
    (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨2^64-1⟩ ⟨0⟩)) old) = _
  rw [hz, hz, u256_land_comm (⟨2^64-1⟩ : UInt256) data]

def trackingIndexName (borrow : Bool) : Ident :=
  if borrow then "trackingBorrowIndex" else "trackingSupplyIndex"

def trackingIndexOffset (borrow : Bool) : Fin 32 := if borrow then 24 else 16

def trackingIndexWord (w : UInt256) (borrow : Bool) : UInt256 :=
  packedUint w (trackingIndexOffset borrow).val 8

theorem trackingIndexWord_lt (w : UInt256) (borrow : Bool) :
    (trackingIndexWord w borrow).toNat < 2^64 := packedUint_lt w _ (by decide)

theorem trackingIndexWord_eq (w : UInt256) (borrow : Bool) :
    trackingIndexWord w borrow = if borrow then UInt256.shiftRight w ⟨192⟩ else
      UInt256.land (UInt256.shiftRight w ⟨128⟩) ⟨2^64-1⟩ := by
  cases borrow
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256^(16 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift w (16 : Fin 32)]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256^(24 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift w (24 : Fin 32)]
    apply u256LandMaskCleanOfToNat _ _ (bits := 64) rfl
    rw [← divBytePow_eq_shift w (24 : Fin 32), udiv_toNat]
    change w.toNat / 2^192 < 2^64
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr w.val.isLt

def storeTrackingIndex (evm : EVM.State) (borrow : Bool) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      value (trackingIndexOffset borrow).val 8)

theorem evalTrackingIndex (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (hlocal : locals.get? (trackingIndexName borrow) = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨trackingIndexName borrow, []⟩) =
      .ok (.int (trackingIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        borrow).toNat) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := ⟨0⟩, offset := trackingIndexOffset borrow, size := 8,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨64, by decide⟩) })
    (er := ⟨trackingIndexName borrow, []⟩) (t := .int (.uint ⟨64, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact packedUint_load evm ⟨0⟩ (trackingIndexOffset borrow) 8 ⟨64, by decide⟩ rfl

theorem assignTrackingIndex (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (value : UInt256) (hlocal : locals.get? (trackingIndexName borrow) = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨trackingIndexName borrow, []⟩ (.int value.toNat) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeTrackingIndex evm borrow value) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
    (loc := { slot := ⟨0⟩, offset := trackingIndexOffset borrow, size := 8,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨64, by decide⟩) })
    (er := ⟨trackingIndexName borrow, []⟩) (ty := .elem (.int (.uint ⟨64, by decide⟩))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_packed_int evm ⟨0⟩ value (trackingIndexOffset borrow) 8 _

theorem sourceState_storeTotalsIndex {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (borrow : Bool) (value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ ⟨0⟩
      (uint64FieldWrite (solcSlotWordAt ⟨0⟩ σ I) value (if borrow then 1 else 0)))
      (storeTotalsIndex evm borrow value) := by
  have hw := hs.readModifyWrite ⟨0⟩
    (fun old ↦ packedWriteWord old value (totalsIndexOffset borrow).val 8)
  change SourceState _ _ _ (storeTotalsIndex evm borrow value) at hw
  have he : (totalsIndexOffset borrow).val =
      8 * (if borrow then (1 : Fin 4) else 0).val := by cases borrow <;> rfl
  simp only [he, uint64FieldWrite_packed] at hw
  exact hw

theorem sourceState_storeTrackingIndex {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (borrow : Bool) (value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ ⟨0⟩
      (uint64FieldWrite (solcSlotWordAt ⟨0⟩ σ I) value (if borrow then 3 else 2)))
      (storeTrackingIndex evm borrow value) := by
  have hw := hs.readModifyWrite ⟨0⟩
    (fun old ↦ packedWriteWord old value (trackingIndexOffset borrow).val 8)
  change SourceState _ _ _ (storeTrackingIndex evm borrow value) at hw
  have he : (trackingIndexOffset borrow).val =
      8 * (if borrow then (3 : Fin 4) else 2).val := by cases borrow <;> rfl
  simp only [he, uint64FieldWrite_packed] at hw
  exact hw

theorem sourceState_storeLastAccrual {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ ⟨1⟩
      (initializeTimeWord (solcSlotWordAt ⟨1⟩ σ I) value)) (storeLastAccrual evm value) := by
  have hw := hs.readModifyWrite ⟨1⟩ (fun old ↦ packedWriteWord old value 26 5)
  change SourceState _ _ _ (storeLastAccrual evm value) at hw
  simpa only [initializeTimeWord_packed] using hw

end Benchmarks.CompoundIII.Comet
