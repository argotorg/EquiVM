import Benchmarks.Safe.ExecGuardEncode
import Benchmarks.Safe.ExecGuardCallMemory
import Benchmarks.Safe.Blocks.Runtime_020

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def execGuardSaved (p : ExecTransactionInput) (src : Nat) (sigPtr guard hash : UInt256)
    (R : List UInt256) : List UInt256 :=
  [guard, hash, ⟨0⟩, sigPtr, UInt256.ofNat p.tx.refundReceiver.val,
    UInt256.ofNat p.tx.gasToken.val, p.tx.gasPrice, p.tx.baseGas, p.tx.safeTxGas,
    p.tx.operation, UInt256.ofNat p.tx.payload.size, UInt256.ofNat src,
    p.tx.value, UInt256.ofNat p.tx.target.val] ++ R

set_option maxRecDepth 100000 in
theorem safeExecGuardCallPrepare (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata ptr src sigPtr} {guard hash : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3647⟩
      (execGuardSaved p src (UInt256.ofNat sigPtr) guard hash R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hsig : BytesMemory mem sigPtr p.signatures)
    (ha : sigPtr + 32 + p.signatures.size ≤ ptr)
    (hin : src + p.tx.payload.size ≤ I.calldata.size) (hs : src < UInt256.size)
    (hb : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 48 ≤ 1024) :
    ∃ words aw' k' C', words.length = (p.signatures.size + 31) / 32 ∧
      (wordBytes words).extract 0 p.signatures.size = p.signatures ∧
      RD safeBytecode I g s0 ⟨3712⟩
        ([UInt256.ofNat (ptr + 420 + ABI.paddedSize p.tx.payload.size +
            ABI.paddedSize p.signatures.size), ⟨1978710866⟩,
          UInt256.land solcAddrMask guard] ++
          execGuardSaved p src (UInt256.ofNat sigPtr) guard hash R)
        (execGuardCallMemory I.calldata mem ptr src p (UInt256.ofNat I.source.val) words)
        aw' rdata σ k' C' := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have ht : (UInt256.ofNat ptr).toNat = ptr := ulit_toNat' _ (by omega)
  have h4 : UInt256.ofNat 4 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 4) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    simpa only [Nat.add_comm] using
      (uadd_ofNat_toNat (a := 4) (b := ptr) (by decide) (by omega) (by omega))
  let m := writeWord mem ptr execGuardSelectorWord
  have hm : mem.size ≤ m.size := by dsimp [m]; rw [writeWord_sparse_size]; omega
  have hsigs : BytesMemory m sigPtr p.signatures := by
    apply hsig.preserved (by omega) hm
    intro off count hlo hhi
    exact writeWordReadBelow _ _ _ _ _ (by have := hsig.available; omega) (by omega)
  obtain ⟨_, _, _, h₁⟩ := safeRuntime_block_3647_packed (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_3647_stack, safeRuntime_block_3647_memory,
    safeAddressMask, hf, ht, h4] at h₁
  obtain ⟨words, aw', k', C', hn, hp, h₂⟩ := safeExecGuardEncode p.tx p.signatures h₁ hsigs
    (by omega) hin hs (by omega) ho (by simp [execGuardSaved]; omega) (by jump_dest)
  have he : ptr + 4 + 416 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size =
      ptr + 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size := by omega
  rw [he] at h₂
  exact ⟨words, aw', k', C', hn, hp, h₂⟩

end Benchmarks.Safe
