import Benchmarks.UniswapV4PoolManager.PositionWriteStorage
import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev positionUpdateFunction : FunctionDecl := contract.functions[66]!
theorem positionUpdate_lookup : lookupCallable? contract "Position_update" =
    some positionUpdateFunction.toCallable := rfl

def positionFeeStores (evm : EVM.State) (id key fee0 fee1 : UInt256) : EVM.State :=
  let evm1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (positionFeeSlot id key false) fee0
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (positionFeeSlot id key true) fee1

def positionFeesStoreResult (f : Frame) (evm : EVM.State) (id key fee0 fee1 owed0 owed1 : UInt256) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else
    .returned f (positionFeeStores evm id key fee0 fee1)
      (some [.int (Int.ofNat owed0.toNat), .int (Int.ofNat owed1.toNat)])

theorem positionFeesStoreBody {f : Frame} {evm : EVM.State} {id key fee0 fee1 owed0 owed1 : UInt256}
    (hs : f.locals.get? "self" = some (positionRefValue id key))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)))
    (h1 : f.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)))
    (ho0 : f.locals.get? "feesOwed0" = some (.int (Int.ofNat owed0.toNat)))
    (ho1 : f.locals.get? "feesOwed1" = some (.int (Int.ofNat owed1.toNat))) :
    ExecFuncBody config f evm (positionUpdateFunction.body.drop 8)
      (positionFeesStoreResult f evm id key fee0 fee1 owed0 owed1) := by
  have hw0 := positionFee_write (f := f) (evm := evm) (value := fee0) hs false
  unfold positionFeesStoreResult
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignStatic (evalLocalValue h0) hw0 hp))
  · rw [if_neg hp]
    let evm1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (positionFeeSlot id key false) fee0
    have hw1 := positionFee_write (f := f) (evm := evm1) (value := fee1) hs true
    refine .execBlockRet (ExecBlock.consNormal (ExecStmt.assign (evalLocalValue h0) hw0)
      (ExecBlock.consNormal (ExecStmt.assign (evalLocalValue h1) hw1) (ExecBlock.consReturn (ExecStmt.return ?_))))
    change evalExprs? config f (positionFeeStores evm id key fee0 fee1) [.var "feesOwed0", .var "feesOwed1"] = _
    simp only [evalExprs?, evalLocalValue (cfg := config) (f := f) (evm := positionFeeStores evm id key fee0 fee1) ho0,
      evalLocalValue (cfg := config) (f := f) (evm := positionFeeStores evm id key fee0 fee1) ho1,
      bind, EvalResult.bind, pure]

end Benchmarks.UniswapV4PoolManager
