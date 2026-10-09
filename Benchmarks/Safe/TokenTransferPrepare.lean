import Benchmarks.Safe.TokenTransferMemory
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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

set_option maxRecDepth 100000 in
theorem safeTokenTransferMemory {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 100 < UInt256.size) (hc : receiver.toNat < EVM.addressModulus) :
    safeRuntime_block_8915_memory (mem := mem) (x0 := amount) (x1 := receiver) =
      tokenTransferMemory mem ptr receiver amount := by
  have hargs := safeTokenTransferArgsMemory (amount := amount) hf hb hc
  have hfree := tokenTransferArgsMemory_free (receiver := receiver) (amount := amount) hf hm hp
  change memLoad (UInt256.ofNat 64) _ = UInt256.ofNat ptr at hfree
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hsel : UInt256.land (UInt256.ofNat (2 ^ 256 - 2 ^ 224)) transferSelectorWord =
      transferSelectorWord := by decide +kernel
  unfold safeRuntime_block_8915_memory
  rw [hargs, hfree, hf]
  simp only [u256_sub_self,
    u256_add_zero, tokenTransferPointerAdd hb 32 (by decide),
    tokenTransferPointerAdd hb 100 (by decide), hmask,
    ulit_toNat' ptr (by omega), ulit_toNat' (ptr + 32) (by omega)]
  change writeWord (tokenTransferHeaderMemory mem ptr receiver amount) (ptr + 32)
    (UInt256.lor transferSelectorWord (UInt256.land (UInt256.ofNat (2 ^ 224 - 1))
      (memLoad (UInt256.ofNat (ptr + 32))
        (tokenTransferHeaderMemory mem ptr receiver amount)))) = _
  rw [u256_lor_comm, u256_land_comm (UInt256.ofNat (2 ^ 224 - 1)), ← hsel]
  change Reasoning.Theory.writeWord _ _ (replaceSelectorWord _ transferSelectorWord) = _
  apply replaceSelectorStore
  · rw [tokenTransferHeaderMemory_size]; omega
  · rw [memLoadReadWord, ulit_toNat' (ptr + 32) (by omega)]
    exact toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize _ _ _)

set_option maxRecDepth 100000 in
theorem safeTokenTransferPrepare {I g s0 σ k C aw mem rdata ptr}
    {amount receiver token ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8915⟩ (amount :: receiver :: token :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 100 < UInt256.size) (hc : receiver.toNat < EVM.addressModulus)
    (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨9004⟩
      (gasArg :: token :: ⟨0⟩ :: UInt256.ofNat (ptr + 32) :: ⟨68⟩ :: ⟨0⟩ :: ⟨32⟩ ::
        UInt256.ofNat ptr :: ⟨0⟩ :: amount :: receiver :: token :: ret :: R)
      (tokenTransferMemory mem ptr receiver amount) aw' rdata σ k' C' := by
  have hmemory := safeTokenTransferMemory (amount := amount) hf hm hp hb hc
  have hargs := safeTokenTransferArgsMemory (amount := amount) hf hb hc
  have hfree := tokenTransferArgsMemory_free (receiver := receiver) (amount := amount) hf hm hp
  change memLoad (UInt256.ofNat 64) _ = UInt256.ofNat ptr at hfree
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_8915_packed (by simp; omega) h
  simp only [safeRuntime_block_8915_stack] at h₁
  rw [← safeRuntime_block_8915_memory, hmemory, hargs, hfree] at h₁
  have hlen : memLoad (UInt256.ofNat ptr) (tokenTransferMemory mem ptr receiver amount) =
      ⟨68⟩ := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' ptr (by omega)]
    exact tokenTransferMemory_length _ _ _ _ hp
  simp only [hlen, tokenTransferPointerAdd hb 32 (by decide)] at h₁
  have h₂ := safeRuntime_block_8995 (by simp; omega) h₁
  simp only [safeRuntime_block_8995_stack] at h₂
  exact ⟨_, aw₁, _, _, h₂⟩

end Benchmarks.Safe
