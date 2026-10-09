import Benchmarks.Safe.ExecTransactionSourcePrefix
import Benchmarks.Safe.SignatureCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execSignatureInput (p : ExecTransactionInput) (evm : EVM.State) : SignatureCheckInput :=
  ⟨evm.executionEnv.source, execTransactionHash p evm, p.signatures⟩

def execSignedFrame (p : ExecTransactionInput) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (execHashFrame p evm) "_sigOk" none

theorem execSignedFrame_locals (p : ExecTransactionInput) (evm : EVM.State) :
    ExecTransactionLocals p (execSignedFrame p evm).locals :=
  (execHashFrame_locals p evm).set _ _ (by decide)

set_option maxRecDepth 100000

theorem safeExecSignatureCall (p : ExecTransactionInput) (evm : EVM.State) {result : ExecResult}
    (hb : ExecFuncBody config (execSignatureInput p evm).frame (execNonceState evm)
      checkSignaturesImplFunction.body result) :
    ExecStmt config (execHashFrame p evm) (execNonceState evm)
      (.internalCall "checkSignaturesImpl" [sender, .var "txHash", .var "signatures"] "_sigOk")
      (internalCallResult (execHashFrame p evm) "_sigOk" result) := by
  apply safeInternalCheckSignatures (p := execSignatureInput p evm) rfl rfl
  · simp only [sender, evalExpr?, envValue, execNonceState, storageStore_executionEnv, pure]
    rfl
  · exact evalLocalValue (by simp [execHashFrame, execSignatureInput, Std.HashMap.getElem_insert])
  · exact evalLocalValue (execHashFrame_locals p evm).signatures
  · exact hb

theorem safeExecSignatureRevert (p : ExecTransactionInput) (evm : EVM.State)
    (hn : p.signatures.size ≤ 2 ^ 64 - 192) (ho : p.tx.operation.toNat < 2)
    (hno : (execNonce evm).toNat + 1 < UInt256.size)
    (hb : ExecFuncBody config (execSignatureInput p evm).frame (execNonceState evm)
      checkSignaturesImplFunction.body .reverted) :
    ExecBlock config p.frame evm exectransactionTransition.body .reverted :=
  safeExecTransactionNoncePrefix p evm hn ho hno
    (.consNormal (safeExecTransactionHashLet p evm) (.consRevert (safeExecSignatureCall p evm hb)))

theorem safeExecSignaturePrefix (p : ExecTransactionInput) (evm : EVM.State)
    {f' : Frame} {evm' : EVM.State} {result : ExecResult}
    (hn : p.signatures.size ≤ 2 ^ 64 - 192) (ho : p.tx.operation.toNat < 2)
    (hno : (execNonce evm).toNat + 1 < UInt256.size)
    (hb : ExecFuncBody config (execSignatureInput p evm).frame (execNonceState evm)
      checkSignaturesImplFunction.body (.returned f' evm' none))
    (ht : ExecBlock config (execSignedFrame p evm) evm'
      (exectransactionTransition.body.drop 6) result) :
    ExecBlock config p.frame evm exectransactionTransition.body result :=
  safeExecTransactionNoncePrefix p evm hn ho hno
    (.consNormal (safeExecTransactionHashLet p evm)
      (.consNormal (safeExecSignatureCall p evm hb) ht))

end Benchmarks.Safe
