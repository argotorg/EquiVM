import Benchmarks.Safe.Runs1e6.ExecTransactionNonceTrace
import Benchmarks.Safe.Runs1e6.TransactionHashPreserved
import Benchmarks.Safe.Runs1e6.Authorization
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

def execSignatureSaved (cd : ByteArray) (len : Nat) (ptr hash : UInt256)
    (R : List UInt256) : List UInt256 :=
  hash :: ⟨0⟩ :: execTransactionDecodedStack cd len ptr R

theorem safeExecHashTrace (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr dataLen sigLen} {sigPtr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6275⟩
      (execHashStack I.calldata dataLen sigPtr (execNonce evm) R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hptr : ptr + 352 < UInt256.size) (hov : R.length + 36 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4208⟩
      (execTransactionHash (execTransactionCalldataInput I.calldata dataLen sigLen) evm ::
        execHashSaved I.calldata dataLen sigPtr R)
      (transactionHashMemory mem ptr I (UInt256.ofNat (execTransactionDataStart I.calldata))
        { (execTransactionCalldataInput I.calldata dataLen sigLen).tx with nonce := execNonce evm })
      aw' rdata σ k' C' := by
  let p := execTransactionCalldataInput I.calldata dataLen sigLen
  let tx := { p.tx with nonce := execNonce evm }
  have hn : tx.payload.size = dataLen := by
    change (I.calldata.extract (execTransactionDataStart I.calldata)
      (execTransactionDataStart I.calldata + dataLen)).size = dataLen
    rw [ByteArray.size_extract]; have := hb.dataEnd; omega
  have ht : UInt256.ofNat tx.target.val = calldataWord I.calldata 4 :=
    ((canonicalAddress_eq_address_iff _ _ hb.target).mp rfl).symm
  have hk : UInt256.ofNat tx.gasToken.val = calldataWord I.calldata 228 :=
    ((canonicalAddress_eq_address_iff _ _ hb.gasToken).mp rfl).symm
  have hr : UInt256.ofNat tx.refundReceiver.val = calldataWord I.calldata 260 :=
    ((canonicalAddress_eq_address_iff _ _ hb.refundReceiver).mp rfl).symm
  have hsrc : execTransactionDataStart I.calldata < UInt256.size := by
    have := hb.dataEnd
    have := lt_size_of_lt_sign hb.small
    omega
  have hcall : RD fork safeBytecode I g s0 ⟨6275⟩
      (tx.nonce :: UInt256.ofNat tx.refundReceiver.val :: UInt256.ofNat tx.gasToken.val ::
        tx.gasPrice :: tx.baseGas :: tx.safeTxGas :: tx.operation ::
        UInt256.ofNat tx.payload.size ::
        UInt256.ofNat (execTransactionDataStart I.calldata) :: tx.value ::
        UInt256.ofNat tx.target.val :: ⟨4208⟩ :: execHashSaved I.calldata dataLen sigPtr R)
      mem aw rdata σ k C := by
    rw [ht, hk, hr, hn]
    exact h
  obtain ⟨aw', k', C', h₁⟩ := safeTransactionHashTrace tx hcall hf hm hp hptr
    (by rw [hn]; have := hb.dataLength; change dataLen < 2 ^ 256; omega)
    (by rw [ulit_toNat' _ hsrc, hn]; exact hb.dataEnd)
    (by rw [ulit_toNat' _ hsrc, hn]; rfl)
    (by simp [execHashSaved, execTransactionDecodedStack]; omega) (by jump_dest)
  have he : transactionWord I tx = execTransactionHash p evm := by
    dsimp only [execTransactionHash, tx]
    rw [hee]
  rw [he] at h₁
  exact ⟨aw', k', C', h₁⟩

theorem safeExecSignatureStart {I g s0 σ k C aw mem rdata len} {ptr hash : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4208⟩ (hash :: execHashSaved I.calldata len ptr R)
      mem aw rdata σ k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7903⟩
      (ptr :: hash :: UInt256.ofNat I.source.val :: ⟨4221⟩ ::
        execSignatureSaved I.calldata len ptr hash R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4208 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

end Benchmarks.Safe.Runs1e6
