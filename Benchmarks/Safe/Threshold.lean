import Benchmarks.Safe.Authorization
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Blocks.Runtime_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def thresholdArgs (value : UInt256) : Store :=
  (∅ : Store).insert "_threshold" (.int (Int.ofNat value.toNat))

def thresholdFrame (value : UInt256) : Frame :=
  { contract := contract, locals := thresholdArgs value }

theorem safeEvalThreshold (evm : EVM.State) (value : UInt256) :
    evalExpr? config (thresholdFrame value) evm (.var "_threshold") =
      .ok (.int (Int.ofNat value.toNat)) := by
  simp [thresholdFrame, thresholdArgs, evalExpr?, EvalResult.ofOption]

theorem safeThresholdBound (evm : EVM.State) (value : UInt256) :
    evalExpr? config (thresholdFrame value) evm (leE (.var "_threshold") (.storage ownerCountRef)) =
      .ok (.bool (decide (value.toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat))) := by
  have hload : evalExpr? config (thresholdFrame value) evm (.storage ownerCountRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)) := by
    apply evalExpr_storage_scalar_value (er := { base := "ownerCount" }) (loc := uint256Loc ⟨3⟩)
    · simp [thresholdFrame, thresholdArgs, ownerCountRef]
    · simp [evalStorageRef, evalStorageRefSteps, ownerCountRef, EvalResult.bind, bind, pure]
    · rfl
    · rfl
    · rfl
    · exact storageLocLoad_uint256 evm ⟨3⟩
  rw [leE, evalExpr_binary_nonshort (by decide) (by decide), safeEvalThreshold, hload]
  simp [evalBinaryOp?, EvalResult.bind, bind]

theorem safeThresholdNonzero (evm : EVM.State) (value : UInt256) :
    evalExpr? config (thresholdFrame value) evm (neE (.var "_threshold") (.intLit 0)) =
      .ok (.bool (decide (value.toNat ≠ 0))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), safeEvalThreshold]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.natCast_eq_zero]

theorem safeAssignThreshold (evm : EVM.State) (value : UInt256) :
    assignStorageRef? config (thresholdFrame value) evm .storage thresholdRef
      (.int (Int.ofNat value.toNat)) = .ok (thresholdFrame value,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "threshold" }) (loc := uint256Loc
    ⟨4⟩)
  · simp [thresholdFrame, thresholdArgs, thresholdRef]
  · simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm ⟨4⟩ value

theorem safeThresholdSource (evm : EVM.State) (value : UInt256)
    (hle : value.toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) :
    ExecFuncBody config (thresholdFrame value) evm changeThresholdBodyFunction.body
      (.returned (thresholdFrame value)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) none) := by
  have hn : value.toNat ≠ 0 := fun h ↦ hnz (uint256_toNat_eq_zero h)
  exact .execBlockOK (.consNormal (.requireTrue (by simpa [hle] using safeThresholdBound evm value))
    (.consNormal (.requireTrue (by simpa [hn] using safeThresholdNonzero evm value))
      (.consNormal (.assign (safeEvalThreshold evm value) (safeAssignThreshold evm value))
        (.consNormal (.emit (evalExprs?_singleton (safeEvalThreshold _ value))) .nil))))

theorem safeThresholdSourceStatic (evm : EVM.State) (value : UInt256)
    (hle : value.toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (thresholdFrame value) evm changeThresholdBodyFunction.body
      .staticViolation := by
  have hn : value.toNat ≠ 0 := fun h ↦ hnz (uint256_toNat_eq_zero h)
  exact .execBlockStatic
    (.consNormal (.requireTrue (by simpa [hle] using safeThresholdBound evm value))
      (.consNormal (.requireTrue (by simpa [hn] using safeThresholdNonzero evm value))
        (.consStatic (.assignStatic (safeEvalThreshold evm value)
          (safeAssignThreshold evm value) hperm))))

theorem safeThresholdSourceTooLarge (evm : EVM.State) (value : UInt256)
    (hle : ¬ value.toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat) :
    ExecFuncBody config (thresholdFrame value) evm changeThresholdBodyFunction.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by simpa [hle] using safeThresholdBound evm value)))

theorem safeThresholdSourceZero (evm : EVM.State) :
    ExecFuncBody config (thresholdFrame ⟨0⟩) evm changeThresholdBodyFunction.body .reverted := by
  exact .execBlockRevert (.consNormal (.requireTrue
    (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 by rfl, Nat.zero_le, decide_true]
      using safeThresholdBound evm ⟨0⟩))
    (.consRevert (.requireFalse (by simpa using safeThresholdNonzero evm ⟨0⟩))))

theorem safeThresholdReach {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3423⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024)
    (hle : value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) (hnz : value ≠ ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨3474⟩ (value :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h3450⟩ := safeRuntime_block_3423_taken hov
    (by
      change UInt256.isZero (UInt256.gt value (solcSlotWordAt ⟨3⟩ σ I)) ≠ ⟨0⟩
      rw [ugt_zero hle]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_3450_taken hov (u256_zero_sub_ne_zero hnz) (by jump_dest) h3450⟩

theorem safeThresholdTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3474⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', RD safeBytecode I g s0 ret R mem' aw' rdata
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ value) k' C' := by
  obtain ⟨_, _, hout⟩ := safeRuntime_block_3474 hov hperm hret h
  exact ⟨_, _, _, _, hout⟩

theorem safeThresholdTraceStatic {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3474⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hstore := evm_run h with [jumpdest, push1 ⟨4⟩, dup2, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeThresholdTraceTooLarge {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3423⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hle : ¬ value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) : RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h3434⟩ := safeRuntime_block_3423_fallthrough (by omega)
    (by
      change UInt256.isZero (UInt256.gt value (solcSlotWordAt ⟨3⟩ σ I)) = ⟨0⟩
      rw [ugt_one (by omega)]; decide) h
  have h6898 := safeRuntime_block_3434 (by simp; omega) (by jump_dest) h3434
  exact safeRuntime_block_6898 (by simp; omega) h6898

theorem safeThresholdTraceZero {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3423⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) : RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h3450⟩ := safeRuntime_block_3423_taken (by omega)
    (by
      change UInt256.isZero (UInt256.gt ⟨0⟩ (solcSlotWordAt ⟨3⟩ σ I)) ≠ ⟨0⟩
      rw [ugt_zero (show (⟨0⟩ : UInt256).toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat
        from Nat.zero_le _)]; decide)
    (by jump_dest) h
  have h3458 := safeRuntime_block_3450_fallthrough (by omega) (by decide) h3450
  have h6898 := safeRuntime_block_3458 (by simp; omega) (by jump_dest) h3458
  exact safeRuntime_block_6898 (by simp; omega) h6898

end Benchmarks.Safe
