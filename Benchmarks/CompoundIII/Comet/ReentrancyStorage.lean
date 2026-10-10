import Benchmarks.CompoundIII.Comet.ReentrancyModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem evalReentrancy (frame : Frame) (evm : EVM.State) (hc : frame.contract = contract)
    (hl : frame.locals.get? "__reentrancyGuard" = none) :
    evalExpr? config frame evm (.storage ⟨"__reentrancyGuard", []⟩) =
      .ok (.int (reentrancyWord evm).toNat) := by
  apply evalExpr_storage_scalar_value (loc := uint256Loc reentrancySlot)
    (er := ⟨"__reentrancyGuard", []⟩) (t := .int (.uint ⟨256, by decide⟩)) hl
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · rfl
  · exact storageLocLoad_uint256 _ _

theorem assignReentrancy (frame : Frame) (evm : EVM.State) (enter : Bool)
    (hc : frame.contract = contract) (hl : frame.locals.get? "__reentrancyGuard" = none) :
    assignStorageRef? config frame evm .storage ⟨"__reentrancyGuard", []⟩
      (.int (reentrancyValue enter).toNat) = .ok (frame, reentrancyState evm enter) := by
  apply assignStorageRef_storage_scalar_value (loc := uint256Loc reentrancySlot)
    (er := ⟨"__reentrancyGuard", []⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) hl
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 _ _ _

theorem sourceState_reentrancy {s0 I σ evm} (hs : SourceState s0 I σ evm) (enter : Bool) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ reentrancySlot (reentrancyValue enter))
      (reentrancyState evm enter) := by
  simpa only [reentrancyState, hs.env] using hs.storageWrite reentrancySlot (reentrancyValue enter)

end Benchmarks.CompoundIII.Comet
