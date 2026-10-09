import Benchmarks.Safe.Common
import Benchmarks.Safe.AddressBytesCalldata
import Benchmarks.Safe.RawDelegateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def simulateArgs (target : EVM.Address) (payload : ByteArray) : Store :=
  ((∅ : Store).insert "targetContract" (.address target)).insert "calldataPayload" (.bytes payload)

theorem safeSimulateLength (evm : EVM.State) (target : EVM.Address) (payload : ByteArray) :
    evalExpr? config { contract := contract, locals := simulateArgs target payload } evm
      (leE (localLength "calldataPayload") (.intLit (2 ^ 64 - 192))) =
        .ok (.bool (decide (payload.size ≤ 2 ^ 64 - 192))) := by
  simp [leE, localLength, varRef, simulateArgs, evalExpr?, evalStorageRef, evalStorageRefSteps,
    readLocalPath?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?, Int.ofNat_eq_natCast]

theorem safeSimulateSource (evm : EVM.State) (target : EVM.Address) (payload : ByteArray) :
    ExecTransitionBody config contract evm (simulateArgs target payload)
      simulateandrevertTransition.body .reverted := by
  by_cases hv : evm.executionEnv.weiValue = ⟨0⟩
  swap
  · exact bodyReverts_nonPayable hv
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv)) ?_
  by_cases hp : payload.size ≤ 2 ^ 64 - 192
  swap
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hp, decide_false] using safeSimulateLength evm target payload))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [hp, decide_true] using safeSimulateLength evm target payload)) ?_
  obtain ⟨z, evm', out, hcall⟩ := delegateCallExists evm (EVM.address target) payload
    evm.machineState.gasAvailable.toUInt256 evm.substate
  have ht : evalExpr? config { contract := contract, locals := simulateArgs target payload }
      evm (.var "targetContract") = .ok (.address target) := by
    simp [evalExpr?, simulateArgs, EvalResult.ofOption, pure, Std.HashMap.getElem_insert]
  have hd : evalExpr? config { contract := contract, locals := simulateArgs target payload }
      evm (.var "calldataPayload") = .ok (.bytes payload) := by
    simp [evalExpr?, simulateArgs, EvalResult.ofOption, pure, Std.HashMap.getElem_insert]
  cases z
  · exact .consNormal (.delegateCallFailure ht hd hcall)
      (.consRevert (.requireFalse (by simp [evalExpr?, pure])))
  · exact .consNormal (.delegateCallSuccess ht hd hcall)
      (.consRevert (.requireFalse (by simp [evalExpr?, pure])))

end Benchmarks.Safe
