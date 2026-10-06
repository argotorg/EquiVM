import Reasoning.Storage
import Reasoning.Memory
import Benchmarks.WETH9.Routines

/-!
# WETH9 shared storage helpers for mutating functions

Reusable source-level facts for the caller-keyed `balanceOf` mapping and the wrapping (`unchecked`)
uint256 store that WETH9's `deposit`/`withdraw`/`transferFrom` perform.  The two `wordOfInt` lemmas
are general library candidates (`Reasoning.Storage`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9


/-! ## Caller-keyed `balanceOf[msg.sender]` -/

/-- The evaluated storage ref for `balanceOf[msg.sender]`. -/
abbrev callerBalRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

/-- The `balanceOf[msg.sender]` slot. -/
def callerBalSlot (I : ExecutionEnv) : UInt256 := balanceOfSlot (.address I.source)

/-- Reading `balanceOf[msg.sender]` in the source semantics. -/
theorem evalCallerBal (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv = I) (hbase : locals.get? "balanceOf" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (balanceOfRef sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat)) := by
  refine evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals })
    (slot := balanceOfRef sender) (er := callerBalRef I) (t := .int uint256Int)
    (loc := wordLoc (callerBalSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (callerBalSlot I)).toNat))
    (hbase := by simpa [balanceOfRef] using hbase) ?_ ?_ (by rfl) ?_
  · simp only [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · simpa [wordLoc, uint256Loc, uint256Int, callerBalSlot] using
      storageLocLoad_uint256 evm (callerBalSlot I)

end Benchmarks.WETH9
