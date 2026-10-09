import Benchmarks.Morpho.MorphoBlue.FlashLoanDecode
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal
import Benchmarks.Morpho.MorphoBlue.AccrueSourceFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanArgs (token : AccountAddress) (assets : UInt256) (data : ByteArray) : Store :=
  (((∅ : Store).insert "token" (.address token)).insert
    "assets" (.int (Int.ofNat assets.toNat))).insert "data" (.bytes data)

def flashLoanFrame (token : AccountAddress) (assets : UInt256) (data cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := (flashLoanArgs token assets data).insert "__calldata" (.bytes cd) }

structure FlashLoanInputs (frame : Frame) (token : AccountAddress) (assets : UInt256) (data : ByteArray) : Prop where
  token_eq : frame.locals.get? "token" = some (.address token)
  assets_eq : frame.locals.get? "assets" = some (.int (Int.ofNat assets.toNat))
  data_eq : frame.locals.get? "data" = some (.bytes data)

theorem flashLoanFrame_inputs (token : AccountAddress) (assets : UInt256) (data cd : ByteArray) (imms : Store) :
    FlashLoanInputs (flashLoanFrame token assets data cd imms) token assets data := by
  constructor <;> simp [flashLoanFrame, flashLoanArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem FlashLoanInputs.assetsGuard {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm : EVM.State) : evalExpr? config frame evm (.binary .ne (.var "assets") (.intLit 0)) =
      .ok (.bool (decide (assets ≠ ⟨0⟩))) :=
  evalWordNeZero (by simp only [evalExpr?, hi.assets_eq, EvalResult.ofOption])

theorem morphoFlashLoanPrelude (token : AccountAddress) (assets : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := flashLoanArgs token assets data, immutables := imms }
      flashLoanTransition.body (flashLoanFrame token assets data evm.executionEnv.calldata imms)
      (flashLoanTransition.body.drop 3) := calldataPrelude_ok hcv hsize

theorem morphoFlashLoanSourceZero (token : AccountAddress) (assets : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hz : assets = ⟨0⟩) :
    ExecTransitionBody config contract evm (flashLoanArgs token assets data) flashLoanTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (morphoFlashLoanPrelude token assets data evm imms hcv hsize).requireRevert
  simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
    (flashLoanFrame_inputs token assets data evm.executionEnv.calldata imms).assetsGuard evm

theorem morphoFlashLoanSourceGuard (token : AccountAddress) (assets : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hz : assets ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := flashLoanArgs token assets data, immutables := imms }
      flashLoanTransition.body (flashLoanFrame token assets data evm.executionEnv.calldata imms)
      (flashLoanTransition.body.drop 4) := by
  apply (morphoFlashLoanPrelude token assets data evm imms hcv hsize).requireStep
  simpa only [decide_eq_true hz] using
    (flashLoanFrame_inputs token assets data evm.executionEnv.calldata imms).assetsGuard evm

theorem flashLoanEventArgs {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm : EVM.State) : evalExprs? config frame evm [.env .caller, .var "token", .var "assets"] =
      .ok [.address evm.executionEnv.source, .address token, .int (Int.ofNat assets.toNat)] := by
  simp only [evalExprs?, evalExpr?, envValue, hi.token_eq, hi.assets_eq,
    EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem morphoFlashLoanSourceStatic (token : AccountAddress) (assets : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hz : assets ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (flashLoanArgs token assets data) flashLoanTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (morphoFlashLoanSourceGuard token assets data evm imms hcv hsize hz).run
  exact ExecBlock.consStatic (ExecStmt.emitStatic
    (flashLoanEventArgs (flashLoanFrame_inputs token assets data evm.executionEnv.calldata imms) evm) hperm)

theorem morphoFlashLoanSourceEnter (token : AccountAddress) (assets : UInt256) (data : ByteArray)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hz : assets ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := flashLoanArgs token assets data, immutables := imms }
      flashLoanTransition.body (flashLoanFrame token assets data evm.executionEnv.calldata imms)
      (flashLoanTransition.body.drop 5) := by
  exact (morphoFlashLoanSourceGuard token assets data evm imms hcv hsize hz).emitStep
    (flashLoanEventArgs (flashLoanFrame_inputs token assets data evm.executionEnv.calldata imms) evm)

end Benchmarks.Morpho.MorphoBlue
