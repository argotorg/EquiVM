import Benchmarks.Safe.TransactionHashSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def transactionArgs (tx : SafeTransaction) : Store :=
  ((((((((((∅ : Store).insert "to" (.address tx.target)).insert
    "value" (.int (Int.ofNat tx.value.toNat))).insert "data" (.bytes tx.payload)).insert
    "operation" (.int (Int.ofNat tx.operation.toNat))).insert
    "safeTxGas" (.int (Int.ofNat tx.safeTxGas.toNat))).insert
    "baseGas" (.int (Int.ofNat tx.baseGas.toNat))).insert
    "gasPrice" (.int (Int.ofNat tx.gasPrice.toNat))).insert
    "gasToken" (.address tx.gasToken)).insert
    "refundReceiver" (.address tx.refundReceiver)).insert "_nonce" (.int (Int.ofNat tx.nonce.toNat))

def transactionFrame (tx : SafeTransaction) : Frame :=
  { contract := contract, locals := transactionArgs tx }

theorem transactionArgsLocals (tx : SafeTransaction) :
    TransactionLocals (transactionFrame tx) tx := by
  constructor <;> simp [transactionFrame, transactionArgs, Std.HashMap.getElem_insert]

end Benchmarks.Safe
