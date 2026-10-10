import Benchmarks.CompoundIII.Comet.ScalarWrites
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: replacing either uint104 field in a packed storage word.
def totalsPrincipalWriteWord (old data : UInt256) (borrow : Bool) : UInt256 :=
  if borrow then
    let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    UInt256.lor (UInt256.land mask (UInt256.shiftLeft data (UInt256.ofNat 104)))
      (UInt256.land (UInt256.lnot mask) old)
  else
    let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
      (UInt256.ofNat 1)
    UInt256.lor (UInt256.land data mask) (UInt256.land (UInt256.lnot mask) old)

theorem totalsPrincipalWriteWord_packed (old data : UInt256) (borrow : Bool) :
    packedWriteWord old data (totalsPrincipalOffset borrow).val 13 =
      totalsPrincipalWriteWord old data borrow := by
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨data.val⟩
  cases borrow
  · change packedWriteWord old data 0 13 = _
    rw [packedWriteWord_bitvec x y 0 13 (by decide) (by decide) (by decide)]
    have hb : x % BitVec.ofNat 256 (256^0) +
        BitVec.ofNat 256 (256^0) * (y % BitVec.ofNat 256 (256^13)) +
        BitVec.ofNat 256 (256^13) * (x / BitVec.ofNat 256 (256^13)) =
        (y &&& BitVec.ofNat 256 (2^104-1)) |||
          ((~~~BitVec.ofNat 256 (2^104-1)) &&& x) := by bv_decide
    rw [hb]
    simp only [totalsPrincipalWriteWord, Bool.false_eq_true, if_false,
      UInt256.land, UInt256.lor, UInt256.lnot, BitVec.toFin_and, BitVec.toFin_or,
      BitVec.toFin_not]
    rfl
  · change packedWriteWord old data 13 13 = _
    rw [packedWriteWord_bitvec x y 13 13 (by decide) (by decide) (by decide)]
    have hb : x % BitVec.ofNat 256 (256^13) +
        BitVec.ofNat 256 (256^13) * (y % BitVec.ofNat 256 (256^13)) +
        BitVec.ofNat 256 (256^26) * (x / BitVec.ofNat 256 (256^26)) =
        (BitVec.ofNat 256 (2^208-2^104) &&& (y <<< 104)) |||
          ((~~~BitVec.ofNat 256 (2^208-2^104)) &&& x) := by bv_decide
    rw [hb]
    simp only [totalsPrincipalWriteWord, if_true, UInt256.land, UInt256.lor,
      UInt256.lnot, BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
    rfl

def storeTotalsPrincipal (evm : EVM.State) (borrow : Bool) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (packedWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      value (totalsPrincipalOffset borrow).val 13)

theorem assignTotalsPrincipal (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (value : UInt256) (hlocal : locals.get? (totalsPrincipalName borrow) = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨totalsPrincipalName borrow, []⟩ (.int value.toNat) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeTotalsPrincipal evm borrow value) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
    (loc := { slot := ⟨1⟩, offset := totalsPrincipalOffset borrow, size := 13,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨104, by decide⟩) })
    (er := ⟨totalsPrincipalName borrow, []⟩) (ty := .elem (.int (.uint ⟨104, by decide⟩))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_packed_int evm ⟨1⟩ value (totalsPrincipalOffset borrow) 13 _

theorem sourceState_storeTotalsPrincipal {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (borrow : Bool) (value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ ⟨1⟩
      (totalsPrincipalWriteWord (solcSlotWordAt ⟨1⟩ σ I) value borrow))
      (storeTotalsPrincipal evm borrow value) := by
  have hw := hs.readModifyWrite ⟨1⟩
    (fun old ↦ packedWriteWord old value (totalsPrincipalOffset borrow).val 13)
  change SourceState _ _ _ (storeTotalsPrincipal evm borrow value) at hw
  simpa only [totalsPrincipalWriteWord_packed] using hw

end Benchmarks.CompoundIII.Comet
