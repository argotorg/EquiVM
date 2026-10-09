import Benchmarks.Safe.TransactionArguments
import Benchmarks.Safe.Operation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeTransactionHashBody {evm : EVM.State} {tx : SafeTransaction}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (ho : tx.operation.toNat < 2) :
    ExecTransitionBody config contract evm (transactionArgs tx) gettransactionhashTransition.body
      (.returned (transactionFrame tx) evm
        (some [wordBytes32Value (transactionWord evm.executionEnv tx)])) := by
  apply ExecFuncBody.execBlockRet
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv)) ?_
  refine .consNormal (.requireTrue (by
    simpa only [ho, decide_true] using
      (evalValidOperation (cfg := config) (evm := evm) (transactionArgsLocals tx).operation))) ?_
  apply ExecBlock.consReturn
  apply ExecStmt.return
  apply evalExprs?_singleton
  apply evalTransactionHash (transactionArgsLocals tx)
  simp [evalExpr?, transactionFrame, transactionArgs, EvalResult.ofOption,
    Std.HashMap.getElem_insert, pure]

theorem safeTransactionHashInvalid {evm : EVM.State} {tx : SafeTransaction}
    (ho : ¬tx.operation.toNat < 2) :
    ExecTransitionBody config contract evm (transactionArgs tx) gettransactionhashTransition.body
      .reverted := by
  by_cases hv : evm.executionEnv.weiValue = ⟨0⟩
  swap
  · exact bodyReverts_nonPayable hv
  apply ExecFuncBody.execBlockRevert
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv)) ?_
  exact .consRevert (.requireFalse (by
    simpa only [ho, decide_false] using
      (evalValidOperation (cfg := config) (evm := evm) (transactionArgsLocals tx).operation)))

end Benchmarks.Safe
