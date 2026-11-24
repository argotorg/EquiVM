import Benchmarks.Safe.ViaIR.TokenTransferMemory
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_025
import Benchmarks.Safe.ViaIR.IRMemoryAllocation

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

theorem tokenTransferPointerAdd {ptr : Nat} (hb : ptr + 100 < UInt256.size)
    (n : Nat) (hn : n ≤ 100) :
    UInt256.ofNat ptr + UInt256.ofNat n = UInt256.ofNat (ptr + n) := by
  apply u256_inj
  rw [ulit_toNat' _ (by omega)]
  exact uadd_ofNat_toNat (by omega) (by omega) (by omega)

theorem safeTokenTransferArgsMemory {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 100 < UInt256.size)
    (hc : receiver.toNat < EVM.addressModulus) :
    amount.toByteArray.write 0
      ((UInt256.land receiver (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem
        (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 36).toNat 32)
      (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 68).toNat 32 =
      tokenTransferArgsMemory mem ptr receiver amount := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [hf, safeAddressMask, solcAddrMask_clean hc,
    tokenTransferPointerAdd hb 36 (by decide), tokenTransferPointerAdd hb 68 (by decide),
    ulit_toNat' (ptr + 36) (by omega), ulit_toNat' (ptr + 68) (by omega),
    tokenTransferArgsMemory, Reasoning.Theory.writeWord]

set_option maxRecDepth 5000 in
theorem safeTokenTransferMemory {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 100 < UInt256.size) (hc : receiver.toNat < EVM.addressModulus) :
    safeRuntime_block_5152_memory (mem := mem) (x0 := amount) (x3 := ⟨32⟩)
      (x4 := receiver) = tokenTransferHeaderMemory mem ptr receiver amount := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := rfl
  change safeRuntime_block_5152_memory (mem := mem) (x0 := amount) (x3 := UInt256.ofNat 32)
    (x4 := receiver) = _
  simp only [safeRuntime_block_5152_memory, hf, hmask, solcAddrMask_clean_left hc,
    tokenTransferPointerAdd hb 32 (by decide), tokenTransferPointerAdd hb 36 (by decide),
    tokenTransferPointerAdd hb 68 (by decide), ulit_toNat' ptr (by omega),
    ulit_toNat' (ptr + 32) (by omega), ulit_toNat' (ptr + 36) (by omega),
    ulit_toNat' (ptr + 68) (by omega), tokenTransferHeaderMemory, tokenTransferArgsMemory,
    Reasoning.Theory.writeWord]
  rfl

set_option maxRecDepth 5000 in
theorem safeTokenTransferPrepare {I g s0 σ k C aw mem rdata ptr}
    {amount receiver token : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5152⟩ (amount :: token :: ⟨0⟩ :: ⟨32⟩ :: receiver :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr)
    (hb : ptr + 128 < UInt256.size) (hc : receiver.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ gasArg aw' k' C', ptr + 128 < 2 ^ 64 ∧ RD fork safeBytecode I g s0 ⟨5214⟩
      (gasArg :: token :: ⟨0⟩ :: UInt256.ofNat (ptr + 32) :: ⟨68⟩ :: ⟨0⟩ :: ⟨32⟩ ::
        amount :: R) (tokenTransferMemory mem ptr receiver amount) aw' rdata σ k' C' := by
  have hmemory := safeTokenTransferMemory (amount := amount) hf (by omega) hc
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_5152_packed (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have h32 : UInt256.ofNat ptr + (⟨32⟩ : UInt256) = UInt256.ofNat (ptr + 32) :=
    tokenTransferPointerAdd (by omega) 32 (by decide)
  simp only [safeRuntime_block_5152_stack, hf, h32] at h₁
  rw [hmemory] at h₁
  obtain hrev | ⟨aw₂, k₂, C₂, hcap, h₂⟩ := safeIRAllocateTrace h₁ (by decide)
    (by simpa only [show ABI.paddedSize 100 = 128 from rfl] using hb)
    (by simp; omega) (by jump_dest)
  · exact .inl hrev
  change RD fork safeBytecode I g s0 (UInt256.ofNat 5205)
    (UInt256.ofNat ptr :: ⟨0⟩ :: UInt256.ofNat (ptr + 32) :: token :: ⟨0⟩ :: ⟨32⟩ ::
      amount :: R) (tokenTransferMemory mem ptr receiver amount) aw₂ rdata σ k₂ C₂ at h₂
  have hlen : memLoad (UInt256.ofNat ptr) (tokenTransferMemory mem ptr receiver amount) =
      ⟨68⟩ := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' ptr (by omega)]
    exact tokenTransferMemory_length _ _ _ _ hp
  have h₃ := safeRuntime_block_5205 (by simp; omega) h₂
  simp only [safeRuntime_block_5205_stack, hlen] at h₃
  exact .inr ⟨_, _, _, _, hcap, h₃⟩

end Benchmarks.Safe.ViaIR
