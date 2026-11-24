import Benchmarks.Safe.ViaIR.ExecGuardEncode
import Benchmarks.Safe.ViaIR.ExecGuardCallMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execGuardSaved (p : ExecTransactionInput) (src : Nat) (sigPtr guard hash : UInt256)
    (R : List UInt256) : List UInt256 :=
  [sigPtr, UInt256.ofNat p.tx.target.val, UInt256.ofNat src,
    UInt256.ofNat p.tx.refundReceiver.val, UInt256.land guard solcAddrMask,
    UInt256.ofNat p.tx.gasToken.val, hash, UInt256.ofNat p.tx.payload.size] ++ R

set_option maxRecDepth 2000 in
theorem safeExecGuardCallPrepare (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata ptr src sigPtr} {guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5462⟩
      (execGuardSaved p src (UInt256.ofNat sigPtr) guard hash R) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hsig : BytesMemory mem sigPtr p.signatures)
    (ha : sigPtr + 32 + p.signatures.size ≤ ptr)
    (hin : src + p.tx.payload.size ≤ I.calldata.size) (hs : src < UInt256.size)
    (hb : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 32 ≤ 1024) :
    ∃ words gasArg aw' k' C', words.length = (p.signatures.size + 31) / 32 ∧
      (wordBytes words).extract 0 p.signatures.size = p.signatures ∧
      RD fork safeBytecode I g s0 ⟨5650⟩
        ([gasArg, UInt256.land guard solcAddrMask, ⟨0⟩, UInt256.ofNat ptr,
          UInt256.ofNat (420 + ABI.paddedSize p.tx.payload.size +
            ABI.paddedSize p.signatures.size), UInt256.ofNat ptr, ⟨0⟩] ++
          execGuardSaved p src (UInt256.ofNat ptr) guard hash R)
        (execGuardCallMemory I.calldata mem ptr src p (UInt256.ofNat I.source.val) words)
        aw' rdata σ k' C' := by
  obtain ⟨words, aw₁, k₁, C₁, hn, hp, h₁⟩ :=
    safeExecGuardEncode p h hc hf hsig ha hin hs hb ho hov
  have hsub : UInt256.sub
      (UInt256.ofNat (ptr + 420 + ABI.paddedSize p.tx.payload.size +
        ABI.paddedSize p.signatures.size)) (UInt256.ofNat ptr) =
      UInt256.ofNat (420 + ABI.paddedSize p.tx.payload.size +
        ABI.paddedSize p.signatures.size) := by
    rw [show ptr + 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size =
      ptr + (420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size)
      by omega, ← wordOfNatAdd _ _ (by omega), word_add_sub_left]
  have hsender : UInt256.land solcAddrMask (UInt256.ofNat I.source.val) =
      UInt256.ofNat I.source.val := by
    rw [u256_land_comm]
    apply solcAddrMask_clean
    rw [ulit_toNat' _ (lt_trans I.source.isLt (by decide))]
    exact I.source.isLt
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_5637_packed (by simp; omega) h₁
  simp only [safeRuntime_block_5637_stack, safeRuntime_block_5637_memory, hsub,
    wordOfNatAdd ptr 324 (by omega), ulit_toNat' (ptr + 324) (by omega)] at h₂
  exact ⟨words, _, aw₂, k₂, C₂, hn, hp, by
    simpa only [execGuardSaved, execGuardCallMemory, execGuardArgsMemory, hsender,
      Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd] using h₂⟩

end Benchmarks.Safe.ViaIR
