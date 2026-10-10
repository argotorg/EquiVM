import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def pauseFlagsLoc : StorageLoc :=
  { slot := ⟨1⟩, offset := ⟨31, by decide⟩, size := ⟨1, by decide⟩,
    hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }

def pauseFlagsWord (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (UInt256.ofNat (256 ^ 31))) (UInt256.ofNat 255)

theorem evalPauseFlags (evm : EVM.State) (locals imms : Store)
    (hlocal : locals.get? "pauseFlags" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"pauseFlags", []⟩) = .ok (.int (pauseFlagsWord evm).toNat) := by
  apply evalExpr_storage_scalar_value (loc := pauseFlagsLoc) (hbackend := rfl)
    (er := ⟨"pauseFlags", []⟩) (t := .int (.uint ⟨8, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · change storageTypeAt? contract.storage ⟨"pauseFlags", []⟩ = _
    decide +kernel
  · rfl
  · exact storageLocLoad_uint_offset evm ⟨1⟩ ⟨31, by decide⟩ ⟨1, by decide⟩
      ⟨8, by decide⟩ rfl (by decide) (by decide)

theorem pauseFlagsWord_lt (evm : EVM.State) : (pauseFlagsWord evm).toNat < 256 :=
  lowByte_bound _

theorem pauseFlagsWord_eq_shift (evm : EVM.State) :
    pauseFlagsWord evm =
      UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) ⟨248⟩ := by
  unfold pauseFlagsWord
  have hq : (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (UInt256.ofNat (256 ^ 31))).toNat < 256 := by
    change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat / 256 ^ 31 < 256
    exact Nat.div_lt_of_lt_mul (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).val.isLt
  have hclean : UInt256.land
      (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
        (UInt256.ofNat (256 ^ 31))) (UInt256.ofNat 255) = _ := lowByteClean hq
  rw [hclean]
  apply u256_inj
  simp [UInt256.shiftRight, UInt256.div, UInt256.toNat, Fin.shiftRight_val,
    Nat.shiftRight_eq_div_pow, UInt256.ofNat]
  rfl

def isAllowedSlot (owner manager : AccountAddress) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨3⟩ (EVM.word owner.val)) (EVM.word manager.val)

def isAllowedWord (σ : AccountMap) (I : ExecutionEnv) (owner manager : AccountAddress) : UInt256 :=
  UInt256.land (solcSlotWordAt (isAllowedSlot owner manager) σ I) ⟨255⟩

-- LIBRARY CANDIDATE: expose the boolean value of an EVM storage word.
theorem wordToElem_bool_value (w : UInt256) :
    wordToElem .bool w = .bool (decide (w.toNat ≠ 0)) := by
  by_cases hz : w.toNat = 0
  · have hw : w = ⟨0⟩ := u256_inj hz
    rw [hw]
    rfl
  · have hval : w.val ≠ 0 := fun h ↦ hz (congrArg Fin.val h)
    simp only [wordToElem, beq_iff_eq, hval, if_false, ne_eq, hz, not_false_eq_true, decide_true]

theorem evalIsAllowed (evm : EVM.State) (locals imms : Store)
    (owner manager : AccountAddress) (ownerName managerName : Ident)
    (hlocal : locals.get? "isAllowed" = none)
    (ho : locals.get? ownerName = some (.address owner))
    (hm : locals.get? managerName = some (.address manager)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"isAllowed", [.mindex (.var ownerName), .mindex (.var managerName)]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (isAllowedSlot owner manager)) ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := boolOffset0Loc (isAllowedSlot owner manager))
    (er := ⟨"isAllowed", [.mindex (.address owner), .mindex (.address manager)]⟩)
    (t := .bool) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, ho, hm,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · change storageTypeAt? contract.storage
      ⟨"isAllowed", [.mindex (.address owner), .mindex (.address manager)]⟩ = _
    rfl
  · simp only [isAllowedSlot, solcMappingSlot, keyValueToWord_address, boolOffset0Loc]
    rfl
  · exact storageLocLoad_bool_offset0 evm (isAllowedSlot owner manager)

end Benchmarks.CompoundIII.Comet
