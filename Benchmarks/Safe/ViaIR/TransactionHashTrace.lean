import Benchmarks.Safe.ViaIR.TransactionStructTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

private theorem transactionMemLoadReadWord (mem : ByteArray) (off : UInt256) :
    memLoad off mem = uInt256OfByteArray (mem.readWithPadding off.toNat 32) :=
  memLoad_of_wordRead _ _ _
    (toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize mem _ 32)).symm

def transactionHashMemory (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv)
    (off : UInt256) (tx : SafeTransaction) : ByteArray :=
  transactionFinalMemory
    (I.calldata.write off.toNat (domainMemoryAt mem ptr I) ptr tx.payload.size) ptr I tx

theorem transactionHashMemory_free {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    {off : UInt256} {tx : SafeTransaction}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size) :
    memLoad ⟨64⟩ (transactionHashMemory mem ptr I off tx) = UInt256.ofNat ptr := by
  have hs := byteArray_write_size_ge_base I.calldata (domainMemoryAt mem ptr I)
    off.toNat ptr tx.payload.size
  rw [transactionMemLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl,
    transactionHashMemory, transactionFinalMemory_preserved _ _ _ _ _ _
      (by rw [domainMemoryAt_size] at hs; omega) hp,
    copyWindowReadBelow _ _ _ _ _ _ _ hi (by rw [domainMemoryAt_size]; omega) hp]
  rw [domainMemoryAt, writeWords_readBelow _ _ _ _ _ hm hp]
  exact (transactionMemLoadReadWord mem ⟨64⟩).symm.trans hf

set_option maxRecDepth 2000 in
theorem safeTransactionHashTrace (tx : SafeTransaction)
    {I g s0 σ k C aw mem rdata ptr} {off ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9040⟩
      (UInt256.ofNat tx.target.val :: tx.value :: off :: UInt256.ofNat tx.payload.size ::
        tx.operation :: tx.safeTxGas :: tx.baseGas :: tx.gasPrice ::
        UInt256.ofNat tx.gasToken.val :: UInt256.ofNat tx.refundReceiver.val ::
        tx.nonce :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 352 < UInt256.size) (hn : tx.payload.size < UInt256.size)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract off.toNat (off.toNat + tx.payload.size) = tx.payload)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret (transactionWord I tx :: R)
      (transactionHashMemory mem ptr I off tx) aw' rdata σ k' C' := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeTransactionDomainTrace h hf (by omega) (by simp; omega)
  have hfree : memLoad ⟨64⟩ (domainMemoryAt mem ptr I) = UInt256.ofNat ptr := by
    rw [transactionMemLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl, domainMemoryAt,
      writeWords_readBelow _ _ _ _ _ hm hp]
    exact (transactionMemLoadReadWord mem ⟨64⟩).symm.trans hf
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_9114_packed (by simp; omega) h₁
  rw [safeTransactionPrefixMemory hfree hb hn (by rw [domainMemoryAt_size]; omega) hi hd] at h₂
  change memLoad (UInt256.ofNat 64) (domainMemoryAt mem ptr I) = UInt256.ofNat ptr at hfree
  simp only [safeRuntime_block_9114_stack, hfree] at h₂
  change RD fork safeBytecode I g s0 ⟨9228⟩
    (UInt256.ofNat ptr :: ⟨6401⟩ :: (UInt256.ofNat ptr + UInt256.ofNat 32) :: domainWord I ::
      UInt256.ofNat ptr :: ⟨30⟩ :: ⟨66⟩ :: ret :: R)
    (transactionStructHashMemory
      (I.calldata.write off.toNat (domainMemoryAt mem ptr I) ptr tx.payload.size) ptr tx)
    aw₂ rdata σ k₂ C₂ at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_9228_packed (by simp; omega) hret h₂
  rw [safeTransactionFinalMemory _ _ _ _ hb, safeTransactionFinalStack _ _ _ _ _ hb] at h₃
  exact ⟨aw₃, k₃, C₃, h₃⟩

end Benchmarks.Safe.ViaIR
