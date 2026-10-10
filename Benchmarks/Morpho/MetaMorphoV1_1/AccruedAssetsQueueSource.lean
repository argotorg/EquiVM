import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsLoopSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage

/-! Source storage reads and loop control for accrued assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def accruedAssetsQueueSlot (i : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i

def accruedAssetsIdWord (I : ExecutionEnv) (σ : AccountMap) (i : UInt256) : UInt256 :=
  codeOwnerStorageWord I σ (accruedAssetsQueueSlot i)

theorem accruedAssetsQueueRead {frame : Frame} {evm : State} {i : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "withdrawQueue" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    evalExpr? config frame evm (.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩) =
      .ok (wordBytes32Value
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (accruedAssetsQueueSlot i))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hbase hi
  subst c
  exact evalStorage_withdrawQueue_local evm locals imms "i" i hbase hi hbound

theorem accruedAssetsConditionSource {frame : Frame} {evm : State} {i len : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "withdrawQueue" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩ = len) :
    evalExpr? config frame evm accruedAssetsCondition =
      .ok (.bool (decide (i.toNat < len.toNat))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hbase hi
  subst c
  have hl := evalStorage_withdrawQueueLength evm locals imms hbase
  rw [hlen] at hl
  simp only [accruedAssetsCondition, evalExpr?, hl, hi, EvalResult.ofOption,
    bind, EvalResult.bind, uint256Value, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

def accruedAssetsPostFrame (frame : Frame) (i : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "i" (uint256Value (i + ⟨1⟩)) }

theorem accruedAssetsPostSource {frame : Frame} {evm : State} {i : UInt256}
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock config frame evm accruedAssetsPost (.ok (accruedAssetsPostFrame frame i) evm) := by
  apply ExecBlock.consNormal
    (ExecStmt.assign (checkedAddSourceOk (a := i) (b := ⟨1⟩) ?_ ?_ hfit) ?_) ExecBlock.nil
  · simp only [evalExpr?, hi, EvalResult.ofOption]
  · simp only [evalExpr?, pure]; rfl
  · simp only [assignStorageRef?, hi, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
