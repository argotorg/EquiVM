import Benchmarks.CompoundIII.Comet.PackedFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def totalsIndexName (borrow : Bool) : Ident :=
  if borrow then "baseBorrowIndex" else "baseSupplyIndex"

def totalsPrincipalName (borrow : Bool) : Ident :=
  if borrow then "totalBorrowBase" else "totalSupplyBase"

def totalsIndexOffset (borrow : Bool) : Fin 32 := if borrow then 8 else 0
def totalsPrincipalOffset (borrow : Bool) : Fin 32 := if borrow then 13 else 0

def totalsIndexWord (w : UInt256) (borrow : Bool) : UInt256 :=
  packedUint w (totalsIndexOffset borrow).val 8

def totalsPrincipalWord (w : UInt256) (borrow : Bool) : UInt256 :=
  packedUint w (totalsPrincipalOffset borrow).val 13

theorem totalsIndexWord_lt (w : UInt256) (borrow : Bool) :
    (totalsIndexWord w borrow).toNat < 2^64 := packedUint_lt w _ (by decide)

theorem totalsPrincipalWord_lt (w : UInt256) (borrow : Bool) :
    (totalsPrincipalWord w borrow).toNat < 2^104 := packedUint_lt w _ (by decide)

theorem totalsIndexWord_eq (w : UInt256) (borrow : Bool) :
    totalsIndexWord w borrow =
      UInt256.land (if borrow then UInt256.shiftRight w ⟨64⟩ else w)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) := by
  cases borrow
  · change UInt256.land (UInt256.div w ⟨1⟩) _ = _
    rw [word_div_one]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (8 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl

theorem totalsPrincipalWord_eq (w : UInt256) (borrow : Bool) :
    totalsPrincipalWord w borrow =
      UInt256.land (if borrow then UInt256.shiftRight w ⟨104⟩ else w)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
          (UInt256.ofNat 1)) := by
  cases borrow
  · change UInt256.land (UInt256.div w ⟨1⟩) _ = _
    rw [word_div_one]
    rfl
  · change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (13 : Fin 32).val))) _ = _
    rw [divBytePow_eq_shift]
    rfl

theorem evalTotalsIndex (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (hlocal : locals.get? (totalsIndexName borrow) = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨totalsIndexName borrow, []⟩) =
      .ok (.int (totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        borrow).toNat) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := ⟨0⟩, offset := totalsIndexOffset borrow, size := 8,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨64, by decide⟩) })
    (er := ⟨totalsIndexName borrow, []⟩) (t := .int (.uint ⟨64, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact packedUint_load evm ⟨0⟩ (totalsIndexOffset borrow) 8 ⟨64, by decide⟩ rfl

theorem evalTotalsPrincipal (evm : EVM.State) (locals imms : Store) (borrow : Bool)
    (hlocal : locals.get? (totalsPrincipalName borrow) = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨totalsPrincipalName borrow, []⟩) =
      .ok (.int (totalsPrincipalWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
        borrow).toNat) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := ⟨1⟩, offset := totalsPrincipalOffset borrow, size := 13,
              hbound := by cases borrow <;> decide, type := .int (.uint ⟨104, by decide⟩) })
    (er := ⟨totalsPrincipalName borrow, []⟩) (t := .int (.uint ⟨104, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · cases borrow <;> rfl
  · cases borrow <;> rfl
  · exact packedUint_load evm ⟨1⟩ (totalsPrincipalOffset borrow) 13 ⟨104, by decide⟩ rfl

end Benchmarks.CompoundIII.Comet
