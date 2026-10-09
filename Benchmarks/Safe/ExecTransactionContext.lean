import Benchmarks.Safe.ExecTransactionInput
import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure ExecTransactionLocals (p : ExecTransactionInput) (locals : Store) : Prop where
  tx : TransactionLocals { contract := contract, locals := locals } p.tx
  signatures : locals["signatures"]? = some (.bytes p.signatures)

theorem ExecTransactionLocals.initial (p : ExecTransactionInput) :
    ExecTransactionLocals p p.args := by
  constructor
  · constructor <;> simp [ExecTransactionInput.args, Std.HashMap.getElem_insert]
  · simp [ExecTransactionInput.args, Std.HashMap.getElem_insert]

theorem ExecTransactionLocals.set {p locals} (h : ExecTransactionLocals p locals)
    (name : Ident) (value : Value) (hn : name ∉ execTransactionNames) :
    ExecTransactionLocals p (locals.insert name value) := by
  simp only [execTransactionNames, List.mem_cons, List.mem_singleton, not_or] at hn
  constructor
  · constructor <;> simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
      hn, h.tx.target, h.tx.value,
      h.tx.data, h.tx.operation, h.tx.safeTxGas, h.tx.baseGas, h.tx.gasPrice,
      h.tx.gasToken, h.tx.refundReceiver]
  · simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hn, h.signatures]

theorem ExecTransactionLocals.withNonce {p locals} (h : ExecTransactionLocals p locals)
    (nonce : UInt256) :
    TransactionLocals { contract := contract, locals := locals } { p.tx with nonce := nonce } :=
  ⟨h.tx.target, h.tx.value, h.tx.data, h.tx.operation, h.tx.safeTxGas, h.tx.baseGas,
    h.tx.gasPrice, h.tx.gasToken, h.tx.refundReceiver⟩

def execNonce (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩

def execNonceFrame (p : ExecTransactionInput) (evm : EVM.State) : Frame :=
  { contract := contract, locals := p.args.insert "nonceBefore" (uint256Value (execNonce evm)) }

def execNonceState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ (execNonce evm + ⟨1⟩)

def execTransactionHash (p : ExecTransactionInput) (evm : EVM.State) : UInt256 :=
  transactionWord evm.executionEnv { p.tx with nonce := execNonce evm }

def execHashFrame (p : ExecTransactionInput) (evm : EVM.State) : Frame :=
  { contract := contract,
    locals := (execNonceFrame p evm).locals.insert "txHash"
      (wordBytes32Value (execTransactionHash p evm)) }

theorem execNonceFrame_locals (p : ExecTransactionInput) (evm : EVM.State) :
    ExecTransactionLocals p (execNonceFrame p evm).locals :=
  (ExecTransactionLocals.initial p).set _ _ (by decide)

theorem execHashFrame_locals (p : ExecTransactionInput) (evm : EVM.State) :
    ExecTransactionLocals p (execHashFrame p evm).locals :=
  (execNonceFrame_locals p evm).set _ _ (by decide)

end Benchmarks.Safe
