import Benchmarks.Safe.Hashes
import Benchmarks.Safe.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SafeTransaction where
  target : EVM.Address
  value : UInt256
  payload : ByteArray
  operation : UInt256
  safeTxGas : UInt256
  baseGas : UInt256
  gasPrice : UInt256
  gasToken : EVM.Address
  refundReceiver : EVM.Address
  nonce : UInt256

def transactionTypehashWord : UInt256 :=
  ⟨84814075808141314178395468817534025465894426928601295766380145544921651250904⟩

def transactionWords (tx : SafeTransaction) : List UInt256 :=
  [transactionTypehashWord, UInt256.ofNat tx.target.val, tx.value,
    uInt256OfByteArray (KEC tx.payload), tx.operation, tx.safeTxGas, tx.baseGas, tx.gasPrice,
    UInt256.ofNat tx.gasToken.val, UInt256.ofNat tx.refundReceiver.val, tx.nonce]

def transactionStructWord (tx : SafeTransaction) : UInt256 :=
  uInt256OfByteArray (KEC (wordBytes (transactionWords tx)))

def transactionPreimage (I : ExecutionEnv) (tx : SafeTransaction) : ByteArray :=
  ⟨#[0x19, 0x01]⟩ ++ (domainWord I).toByteArray ++ (transactionStructWord tx).toByteArray

def transactionWord (I : ExecutionEnv) (tx : SafeTransaction) : UInt256 :=
  uInt256OfByteArray (KEC (transactionPreimage I tx))

structure TransactionLocals (frame : Frame) (tx : SafeTransaction) : Prop where
  target : frame.locals["to"]? = some (.address tx.target)
  value : frame.locals["value"]? = some (.int (Int.ofNat tx.value.toNat))
  data : frame.locals["data"]? = some (.bytes tx.payload)
  operation : frame.locals["operation"]? = some (.int (Int.ofNat tx.operation.toNat))
  safeTxGas : frame.locals["safeTxGas"]? = some (.int (Int.ofNat tx.safeTxGas.toNat))
  baseGas : frame.locals["baseGas"]? = some (.int (Int.ofNat tx.baseGas.toNat))
  gasPrice : frame.locals["gasPrice"]? = some (.int (Int.ofNat tx.gasPrice.toNat))
  gasToken : frame.locals["gasToken"]? = some (.address tx.gasToken)
  refundReceiver : frame.locals["refundReceiver"]? = some (.address tx.refundReceiver)

-- LIBRARY CANDIDATE: cast an evaluated address to its unsigned 256-bit integer value.
theorem evalAddressAsUint256 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {addr : EVM.Address}
    (he : evalExpr? cfg frame evm e = .ok (.address addr)) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.ofNat addr.val).toNat)) := by
  have hb : addr.val < UInt256.size := lt_trans addr.isLt (by decide)
  simp only [evalExpr?, he, bind, EvalResult.bind, pure, ulit_toNat' _ hb]
  simp [castValue?, EvalResult.ofOption, show addr.val < EVM.twoPow 256 from hb]

theorem evalTransactionStructHash {cfg : Config} {frame : Frame} {evm : EVM.State}
    {tx : SafeTransaction} {nonceExpr : Expr} (hl : TransactionLocals frame tx)
    (hn : evalExpr? cfg frame evm nonceExpr = .ok (.int (Int.ofNat tx.nonce.toNat))) :
    evalExpr? cfg frame evm (transactionStructHashExpr nonceExpr) =
      .ok (wordBytes32Value (transactionStructWord tx)) := by
  unfold transactionStructHashExpr transactionStructWord
  apply evalKeccakWord
  have ht : evalExpr? cfg frame evm safeTxTypehash =
      .ok (wordBytes32Value transactionTypehashWord) := by
    have hc : safeTxTypehash = .fixedBytesLit bytes32Width
        (EVM.Word.toBytesBE transactionTypehashWord) := by native_decide
    rw [hc]
    simp [evalExpr?, wordBytes32Value, bytes32Width, abiBytes32Width, pure]
  have hlocal {name : Ident} {value : Value} (he : frame.locals[name]? = some value) :
      evalExpr? cfg frame evm (.var name) = .ok value := by
    simp [evalExpr?, he, EvalResult.ofOption, pure]
  have hdata : evalExpr? cfg frame evm txDataHashExpr =
      .ok (wordBytes32Value (uInt256OfByteArray (KEC tx.payload))) :=
    evalKeccakWord (hlocal hl.data)
  have hp : evalPackedArgs? cfg frame evm
      [(bytes32, safeTxTypehash), (uint256, addressAsUint256 (.var "to")),
        (uint256, .var "value"), (bytes32, txDataHashExpr), (uint256, .var "operation"),
        (uint256, .var "safeTxGas"), (uint256, .var "baseGas"), (uint256, .var "gasPrice"),
        (uint256, addressAsUint256 (.var "gasToken")),
        (uint256, addressAsUint256 (.var "refundReceiver")), (uint256, nonceExpr)] =
      .ok ((transactionWords tx).flatMap EVM.Word.toBytesBE) := by
    unfold transactionWords
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply evalPackedArgs_cons ht (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (evalAddressAsUint256 (hlocal hl.target)) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (hlocal hl.value) (encodePacked_uint256 _)
    apply evalPackedArgs_cons hdata (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hlocal hl.operation) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (hlocal hl.safeTxGas) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (hlocal hl.baseGas) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (hlocal hl.gasPrice) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (evalAddressAsUint256 (hlocal hl.gasToken)) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (evalAddressAsUint256 (hlocal hl.refundReceiver))
      (encodePacked_uint256 _)
    exact evalPackedArgs_single hn (encodePacked_uint256 _)
  rw [evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, wordBytes_eq_list, byteArray_mk_toArray_eq_toByteArray]

theorem evalTransactionHash {cfg : Config} {frame : Frame} {evm : EVM.State}
    {tx : SafeTransaction} {nonceExpr : Expr} (hl : TransactionLocals frame tx)
    (hn : evalExpr? cfg frame evm nonceExpr = .ok (.int (Int.ofNat tx.nonce.toNat))) :
    evalExpr? cfg frame evm (transactionHashExpr nonceExpr) =
      .ok (wordBytes32Value (transactionWord evm.executionEnv tx)) := by
  unfold transactionHashExpr transactionWord
  apply evalKeccakWord
  have hprefix : evalExpr? cfg frame evm eip712Prefix =
      .ok (.fixedBytes bytes2Width [0x19, 0x01]) := by simp [evalExpr?, eip712Prefix, pure]
  have henc : encodePackedValue? bytes2 (.fixedBytes bytes2Width [0x19, 0x01]) =
      some [0x19, 0x01] := by decide +kernel
  have hp := evalPackedArgs_cons hprefix henc
    (evalPackedArgs_cons (evalDomainSeparator frame evm) (encodePacked_bytes32 _)
      (evalPackedArgs_single (evalTransactionStructHash hl hn) (encodePacked_bytes32 _)))
  change evalPackedArgs? cfg frame evm
    [(bytes2, eip712Prefix), (bytes32, domainSeparatorExpr),
      (bytes32, transactionStructHashExpr nonceExpr)] = _ at hp
  rw [evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, transactionPreimage, byteArray_mk_toArray_eq_toByteArray,
    list_toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

end Benchmarks.Safe
