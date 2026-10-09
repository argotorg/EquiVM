import Benchmarks.Safe.TransactionDomainTrace
import Benchmarks.Safe.ByteCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def transactionPrefixMemory (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) : ByteArray :=
  writeWords mem ptr ((transactionWords tx).take 9)

theorem transactionPrefixMemory_finish (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) :
    writeWord (writeWord (transactionPrefixMemory mem ptr tx) (ptr + 288)
      (UInt256.ofNat tx.refundReceiver.val)) (ptr + 320) tx.nonce =
      transactionStructMemory mem ptr tx := by
  simp only [transactionPrefixMemory, transactionStructMemory, transactionWords,
    List.take_succ_cons, List.take_zero, writeWords, Nat.add_assoc]

theorem transactionCopyHash {I : ExecutionEnv} {mem : ByteArray} {off : UInt256} {ptr : Nat}
    {payload : ByteArray} (hb : ptr < UInt256.size) (hn : payload.size < UInt256.size)
    (hp : ptr ≤ mem.size) (hi : off.toNat + payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + payload.size) = payload) :
    keccakWord (UInt256.ofNat ptr) (UInt256.ofNat payload.size)
      (I.calldata.write off.toNat mem ptr payload.size) = uInt256OfByteArray (KEC payload) := by
  simp only [keccakWord, ulit_toNat' ptr hb, ulit_toNat' payload.size hn,
    copySlice_read _ _ _ _ _ hi hp, hd, uInt256OfByteArray_eq]

set_option maxRecDepth 100000 in
theorem safeTransactionPrefixMemory {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    {off : UInt256} {tx : SafeTransaction}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 352 < UInt256.size)
    (hn : tx.payload.size < UInt256.size) (hp : ptr ≤ mem.size)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + tx.payload.size) = tx.payload) :
    safeRuntime_block_5377_memory (ee := I) (mem := mem)
      (x5 := UInt256.ofNat tx.gasToken.val) (x6 := tx.gasPrice) (x7 := tx.baseGas)
      (x8 := tx.safeTxGas) (x9 := tx.operation) (x10 := UInt256.ofNat tx.payload.size)
      (x11 := off) (x12 := tx.value) (x13 := UInt256.ofNat tx.target.val) =
      transactionPrefixMemory (I.calldata.write off.toNat mem ptr tx.payload.size) ptr tx := by
  have hadd (j : Nat) (hj : j ≤ 352) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_5377_memory, hf, ulit_toNat' ptr (by omega),
    ulit_toNat' tx.payload.size hn, hadd 32 (by decide), hadd 64 (by decide),
    hadd 96 (by decide), hadd 128 (by decide), hadd 160 (by decide), hadd 192 (by decide),
    hadd 224 (by decide), hadd 256 (by decide),
    transactionCopyHash (by omega) hn hp hi hd]
  simp only [transactionPrefixMemory, transactionWords, List.take_succ_cons, List.take_zero,
    writeWords, Reasoning.Theory.writeWord, transactionTypehashWord, Nat.add_assoc]
  rfl

set_option maxRecDepth 100000 in
theorem safeTransactionFinalMemory (I : ExecutionEnv) (mem : ByteArray) (ptr : Nat)
    (tx : SafeTransaction) (hb : ptr + 352 < UInt256.size) :
    safeRuntime_block_5483_memory (mem := transactionPrefixMemory mem ptr tx)
      (x0 := UInt256.ofNat tx.refundReceiver.val) (x1 := tx.nonce) (x2 := domainWord I)
      (x3 := UInt256.ofNat ptr) (x5 := UInt256.ofNat ptr + UInt256.ofNat 64)
      (x6 := UInt256.ofNat ptr + UInt256.ofNat 32) = transactionFinalMemory mem ptr I tx := by
  have hadd (j : Nat) (hj : j ≤ 352) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have hs : keccakWord (UInt256.ofNat ptr) (UInt256.ofNat 352)
      (transactionStructMemory mem ptr tx) = transactionStructWord tx := by
    simp only [keccakWord, ulit_toNat' ptr (by omega),
      show (UInt256.ofNat 352).toNat = 352 by rfl, transactionStructMemory_read,
      transactionStructWord, uInt256OfByteArray_eq]
  simp only [safeRuntime_block_5483_memory, ulit_toNat' ptr (by omega),
    hadd 288 (by decide), hadd 320 (by decide), hadd 32 (by decide), hadd 64 (by decide)]
  change writeWord (writeWord (writeWord
    (writeWord (writeWord (transactionPrefixMemory mem ptr tx) (ptr + 288)
      (UInt256.ofNat tx.refundReceiver.val)) (ptr + 320) tx.nonce) (ptr + 64)
    (keccakWord (UInt256.ofNat ptr) (UInt256.ofNat 352)
      (writeWord (writeWord (transactionPrefixMemory mem ptr tx) (ptr + 288)
        (UInt256.ofNat tx.refundReceiver.val)) (ptr + 320) tx.nonce))) ptr ⟨6401⟩)
    (ptr + 32) (domainWord I) = _
  rw [transactionPrefixMemory_finish, hs]
  rfl

theorem safeTransactionFinalStack (I : ExecutionEnv) (mem : ByteArray) (ptr : Nat)
    (tx : SafeTransaction) (R : List UInt256) (hb : ptr + 352 < UInt256.size) :
    safeRuntime_block_5483_stack (mem := transactionPrefixMemory mem ptr tx)
      (x0 := UInt256.ofNat tx.refundReceiver.val) (x1 := tx.nonce) (x2 := domainWord I)
      (x3 := UInt256.ofNat ptr) (x5 := UInt256.ofNat ptr + UInt256.ofNat 64)
      (x6 := UInt256.ofNat ptr + UInt256.ofNat 32) (R := R) = transactionWord I tx :: R := by
  change keccakWord (UInt256.ofNat ptr + UInt256.ofNat 30) (UInt256.ofNat 66)
    (safeRuntime_block_5483_memory (mem := transactionPrefixMemory mem ptr tx)
      (x0 := UInt256.ofNat tx.refundReceiver.val) (x1 := tx.nonce) (x2 := domainWord I)
      (x3 := UInt256.ofNat ptr) (x5 := UInt256.ofNat ptr + UInt256.ofNat 64)
      (x6 := UInt256.ofNat ptr + UInt256.ofNat 32)) :: R = _
  rw [safeTransactionFinalMemory _ _ _ _ hb]
  have hadd : (UInt256.ofNat ptr + UInt256.ofNat 30).toNat = ptr + 30 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [keccakWord, hadd, show (UInt256.ofNat 66).toNat = 66 by rfl,
    transactionFinalMemory_read, transactionWord, uInt256OfByteArray_eq]

end Benchmarks.Safe
