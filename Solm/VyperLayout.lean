import Solm.Storage

namespace Solm

open ABI

/-!
# Vyper storage-layout helpers

Vyper exposes concrete storage layouts through compiler output, so this module intentionally does
not try to mirror the compiler's allocation algorithm.  It only packages the representation rules
needed by hand-recorded layouts.
-/

def vyperWordLoc (slot : EVM.Word) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := ty }

def vyperUint256Loc (slot : EVM.Word) : StorageLoc :=
  vyperWordLoc slot (.int (.uint ⟨256, by decide⟩))

/-- Vyper stores `HashMap[K, V]` entries at `keccak256(baseSlot ++ key)`.

This differs from Solidity's `keccak256(key ++ baseSlot)` convention.  Nested maps compose this
function: first derive the outer map slot, then use that as the base slot for the inner map.
-/
def vyperMappingSlot (baseSlot : EVM.Word) (key : KeyValue) : EVM.Word :=
  Ethereum.uInt256OfByteArray (ffi.KEC (baseSlot.toByteArray ++ (keyValueToWord key).toByteArray))

@[simp] theorem vyperUint256Loc_def (slot : EVM.Word) :
    vyperUint256Loc slot = vyperWordLoc slot (.int (.uint ⟨256, by decide⟩)) :=
  rfl

end Solm
