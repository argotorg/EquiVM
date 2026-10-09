import Benchmarks.Safe.TransactionCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure ExecTransactionInput where
  tx : SafeTransaction
  signatures : ByteArray

def ExecTransactionInput.args (p : ExecTransactionInput) : Store :=
  ((((((((((∅ : Store).insert "to" (.address p.tx.target)).insert
    "value" (.int (Int.ofNat p.tx.value.toNat))).insert "data" (.bytes p.tx.payload)).insert
    "operation" (.int (Int.ofNat p.tx.operation.toNat))).insert
    "safeTxGas" (.int (Int.ofNat p.tx.safeTxGas.toNat))).insert
    "baseGas" (.int (Int.ofNat p.tx.baseGas.toNat))).insert
    "gasPrice" (.int (Int.ofNat p.tx.gasPrice.toNat))).insert
    "gasToken" (.address p.tx.gasToken)).insert
    "refundReceiver" (.address p.tx.refundReceiver)).insert "signatures" (.bytes p.signatures)

def ExecTransactionInput.frame (p : ExecTransactionInput) : Frame :=
  { contract := contract, locals := p.args }

def execTransactionInput (cd data signatures : ByteArray) : ExecTransactionInput :=
  ⟨{ transactionFromCalldata cd data with nonce := ⟨0⟩ }, signatures⟩

def execTransactionNames : List Ident :=
  ["to", "value", "data", "operation", "safeTxGas", "baseGas", "gasPrice", "gasToken",
    "refundReceiver", "signatures"]

def execTransactionTypes : List ABIType :=
  [abiAddress, abiUInt256, .bytes, abiUInt8, abiUInt256, abiUInt256, abiUInt256,
    abiAddress, abiAddress, .bytes]

end Benchmarks.Safe
