import Benchmarks.Dss.Clipper.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-!
Shared source-side facts for Clipper's `auth` and `lockPrefix` guards.

These are local library candidates for the repeated mutating-function pattern; they are
parameterized by `locals` so ABI-specific files do not need near-identical copies.
-/

-- LIBRARY CANDIDATE: generic storage-ref evaluation for `wards[msg.sender]` auth guards.
theorem evalStorageRef_clipperAuth (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (locals : Store) (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef (config v) { contract := contract v, locals := locals } evm
      (wardsRef sender) = .ok (clipperRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    clipperRelyAuthEvaledRef, clipperRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

-- LIBRARY CANDIDATE: generic source evaluation of a true `wards[msg.sender] == 1` auth guard.
theorem evalExpr_clipperAuth_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (locals : Store) (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "wards" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := hbase)
      (her := evalStorageRef_clipperAuth v evm I locals hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using clipperStorageLocLoad_uint256 evm
          (clipperRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

-- LIBRARY CANDIDATE: generic source evaluation of a false `wards[msg.sender] == 1` auth guard.
theorem evalExpr_clipperAuth_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (locals : Store) (hsrc : evm.executionEnv.source = I.source)
    (hbase : locals.get? "wards" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (hbase := hbase)
      (her := evalStorageRef_clipperAuth v evm I locals hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact clipperStorageLocLoad_uint256 evm (clipperRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact clipperUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

-- LIBRARY CANDIDATE: generic storage-ref evaluation for the `locked` guard slot.
theorem evalStorageRef_clipperLocked (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) :
    evalStorageRef (config v) { contract := contract v, locals := locals } evm
      lockedRef = .ok { base := "locked", steps := [] } := by
  simp [lockedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

-- LIBRARY CANDIDATE: generic source evaluation of a true `locked == 0` guard.
theorem evalExpr_clipperLocked_zero_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "locked" = none)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage lockedRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (value := .int 0)
      (hbase := hbase)
      (her := evalStorageRef_clipperLocked v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using clipperStorageLocLoad_uint256 evm ⟨13⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

-- LIBRARY CANDIDATE: generic source evaluation of a false `locked == 0` guard.
theorem evalExpr_clipperLocked_zero_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "locked" = none)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage lockedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := lockedRef)
      (er := { base := "locked", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨13⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperLocked v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact clipperStorageLocLoad_uint256 evm ⟨13⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

-- LIBRARY CANDIDATE: generic source assignment for `locked := value`.
theorem assign_clipperLocked (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "locked" = none) (value : UInt256) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage lockedRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract v, locals := locals },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ value) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc ⟨13⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperLocked v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using storageLocStore_uint256 evm ⟨13⟩ value

end Benchmarks.Dss.Clipper
