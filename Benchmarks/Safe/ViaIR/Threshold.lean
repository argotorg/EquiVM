import Benchmarks.Safe.ViaIR.Authorization
import Benchmarks.Safe.ViaIR.Storage
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027
import Benchmarks.Safe.ViaIR.Blocks.Runtime_028
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat))) := by
  have hload : evalExpr? config (thresholdFrame value) evm (.storage ownerCountRef) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)) := by
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
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) := by
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
    (hle : value.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config (thresholdFrame value) evm changeThresholdBodyFunction.body
      (.returned (thresholdFrame value)
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) none) := by
  have hn : value.toNat ≠ 0 := fun h ↦ hnz (uint256_toNat_eq_zero h)
  exact .execBlockOK (.consNormal (.requireTrue (by simpa [hle] using safeThresholdBound evm value))
    (.consNormal (.requireTrue (by simpa [hn] using safeThresholdNonzero evm value))
      (.consNormal (.assign (hperm := Or.inr hperm) (safeEvalThreshold evm value) (safeAssignThreshold evm value))
        (.consNormal (.emit (hperm := by simpa only [storageStore_executionEnv] using hperm) (evalExprs?_singleton (safeEvalThreshold _ value))) .nil))))

theorem safeThresholdSourceStatic (evm : EVM.State) (value : UInt256)
    (hle : value.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody fork config (thresholdFrame value) evm changeThresholdBodyFunction.body
      .staticViolation := by
  have hn : value.toNat ≠ 0 := fun h ↦ hnz (uint256_toNat_eq_zero h)
  exact .execBlockStatic
    (.consNormal (.requireTrue (by simpa [hle] using safeThresholdBound evm value))
      (.consNormal (.requireTrue (by simpa [hn] using safeThresholdNonzero evm value))
        (.consStatic (.assignStatic (safeEvalThreshold evm value)
          (safeAssignThreshold evm value) hperm))))

theorem safeThresholdSourceTooLarge (evm : EVM.State) (value : UInt256)
    (hle : ¬ value.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat) :
    ExecFuncBody fork config (thresholdFrame value) evm changeThresholdBodyFunction.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (by simpa [hle] using safeThresholdBound evm value)))

theorem safeThresholdSourceZero (evm : EVM.State) :
    ExecFuncBody fork config (thresholdFrame ⟨0⟩) evm changeThresholdBodyFunction.body .reverted := by
  exact .execBlockRevert (.consNormal (.requireTrue
    (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 by rfl, Nat.zero_le, decide_true]
      using safeThresholdBound evm ⟨0⟩))
    (.consRevert (.requireFalse (by simpa using safeThresholdNonzero evm ⟨0⟩))))

theorem safeThresholdReach {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5721⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024)
    (hle : value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) (hnz : value ≠ ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5737⟩ (value :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h5731⟩ := safeRuntime_block_5721_fallthrough hov (ugt_zero hle) h
  exact ⟨_, _, safeRuntime_block_5731_fallthrough hov (isZero_eq_zero_of_ne hnz) h5731⟩

theorem safeThresholdTrace {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5737⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ ⟨4⟩ value) ByteArray.empty := by
  exact safeRuntime_block_5737 hov hperm h

theorem safeThresholdTraceStatic {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5737⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have htopic := evm_run h with [push1 ⟨32⟩, dup2]
  have hswap := htopic.pushConst
    ⟨43901732083494477469716044267715912957164410118621377285867120976187919408275⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have hstore := evm_run hswap with [swap3, push1 ⟨4⟩]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeThresholdTraceTooLarge {I g s0 σ k C aw mem rdata} {value : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5721⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hle : ¬ value.toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h874⟩ := safeRuntime_block_5721_taken (by omega)
    (by
      change UInt256.gt value (solcSlotWordAt ⟨3⟩ σ I) ≠ ⟨0⟩
      rw [ugt_one (by omega)]; decide) (by jump_dest) h
  have h9502 := safeRuntime_block_874 (by simp; omega) (by jump_dest) h874
  exact safeRuntime_block_9502 (by simp; omega) h9502

theorem safeThresholdTraceZero {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5721⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h5731⟩ := safeRuntime_block_5721_fallthrough (by omega)
    (ugt_zero (show (⟨0⟩ : UInt256).toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat
      from Nat.zero_le _)) h
  have h869 := safeRuntime_block_5731_taken (by omega) (by decide) (by jump_dest) h5731
  have h9547 := safeRuntime_block_869 (by simp; omega) (by jump_dest) h869
  exact safeRuntime_block_9547 (by simp; omega) h9547

end Benchmarks.Safe.ViaIR
