import Benchmarks.Safe.ContractSignatureMemory
import Benchmarks.Safe.Blocks.Runtime_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem contractSignatureArgs_free {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (wordBytesArgsMemory mem (ptr + 36) len hash words) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    wordBytesArgsMemory_preserved _ _ _ _ _ _ _ hm (by omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

set_option maxRecDepth 100000 in
theorem safeContractSignatureArgs (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash owner ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8677⟩
      (UInt256.ofNat src :: hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 36)
    (hb : ptr + 164 + 32 * words.length < UInt256.size) (hov : R.length + 26 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨8706⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: signatureMagicWord :: ⟨0⟩ ::
        ⟨0⟩ :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (wordBytesArgsMemory mem (ptr + 36) len hash words) aw' rdata σ k' C' := by
  have hadd : UInt256.ofNat 36 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 36) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact (uadd_ofNat_toNat (a := 36) (b := ptr) (by decide) (by omega) (by omega)).trans
      (by omega)
  have h₁ := safeRuntime_block_8677 (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8677_stack, hf, hadd] at h₁
  obtain ⟨aw', k', C', h₂⟩ := safeWordBytesEncode words h₁ hl hw hn hin (by omega)
    (by omega) (by simp; omega) (by jump_dest)
  have he : ptr + 36 + 96 + 32 * words.length = contractSignatureCallEnd ptr len := by
    simp only [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  rw [he] at h₂
  exact ⟨aw', k', C', h₂⟩

set_option maxRecDepth 100000 in
theorem safeContractSignatureEncodedMemory {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hn : words.length = (len + 31) / 32)
    (hb : contractSignatureCallEnd ptr len + 32 < UInt256.size) :
    safeRuntime_block_8706_memory
      (mem := wordBytesArgsMemory mem (ptr + 36) len hash words)
      (x0 := UInt256.ofNat (contractSignatureCallEnd ptr len)) (x1 := signatureMagicWord) =
      contractSignatureEncodedMemory mem ptr len hash words := by
  have hptr : ptr < UInt256.size := by
    simp only [contractSignatureCallEnd] at hb
    omega
  have h32 : UInt256.ofNat ptr + UInt256.ofNat 32 = UInt256.ofNat (ptr + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat ptr
  have hend : UInt256.ofNat (contractSignatureCallEnd ptr len) =
      UInt256.ofNat ptr + (UInt256.ofNat 32 + UInt256.ofNat (contractSignatureCallLength len)) := by
    rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from rfl, u256_32_add_ofNat]
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    symm
    simpa only [contractSignatureCallEnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (uadd_ofNat_toNat (a := ptr) (b := contractSignatureCallLength len + 32)
        hptr (by simp only [contractSignatureCallEnd] at hb; omega)
        (by simp only [contractSignatureCallEnd] at hb; omega))
  have hlen : UInt256.sub (UInt256.sub (UInt256.ofNat (contractSignatureCallEnd ptr len))
      (UInt256.ofNat ptr)) (UInt256.ofNat 32) =
        UInt256.ofNat (contractSignatureCallLength len) := by
    rw [hend, word_add_sub_left, word_add_sub_left]
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hnot : UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1)) =
      UInt256.ofNat (2 ^ 256 - 2 ^ 224) := by decide +kernel
  have hfree := contractSignatureArgs_free (len := len) (hash := hash) (words := words) hf hm hp
  change memLoad (UInt256.ofNat 64) _ = UInt256.ofNat ptr at hfree
  simp only [safeRuntime_block_8706_memory, hfree, hlen, h32, hmask, hnot,
    ulit_toNat' ptr hptr, ulit_toNat' (ptr + 32) (by
      simp only [contractSignatureCallEnd] at hb; omega)]
  change writeWord (contractSignatureHeaderMemory mem ptr len hash words) (ptr + 32)
    (replaceSelectorWord
      (memLoad (UInt256.ofNat (ptr + 32)) (contractSignatureHeaderMemory mem ptr len hash words))
      signatureMagicWord) = _
  apply replaceSelectorStore
  · rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]
    omega
  · rw [memLoadReadWord, ulit_toNat' (ptr + 32) (by
      simp only [contractSignatureCallEnd] at hb; omega)]
    exact toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize _ _ _)

set_option maxRecDepth 100000 in
theorem safeContractSignatureEncode {I g s0 σ k C aw mem rdata ptr src len}
    {hash owner ret : UInt256} {words : List UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8706⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: signatureMagicWord :: ⟨0⟩ ::
        ⟨0⟩ :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (wordBytesArgsMemory mem (ptr + 36) len hash words) aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hn : words.length = (len + 31) / 32)
    (hb : contractSignatureCallEnd ptr len + 32 < UInt256.size) (hov : R.length + 14 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨11834⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: UInt256.ofNat ptr :: ⟨8785⟩ ::
        UInt256.land solcAddrMask owner :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureEncodedMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hmemory := safeContractSignatureEncodedMemory (hash := hash) hf hm hp hn hb
  have hstack : safeRuntime_block_8706_stack
      (mem := wordBytesArgsMemory mem (ptr + 36) len hash words)
      (x0 := UInt256.ofNat (contractSignatureCallEnd ptr len)) (x1 := signatureMagicWord)
      (x3 := ⟨0⟩) (x4 := UInt256.ofNat src) (x5 := hash) (x6 := owner) (R := ret :: R) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) :: UInt256.ofNat ptr :: ⟨8785⟩ ::
        UInt256.land solcAddrMask owner :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat src :: hash :: owner :: ret :: R := by
    change memLoad ⟨64⟩ (safeRuntime_block_8706_memory
      (mem := wordBytesArgsMemory mem (ptr + 36) len hash words)
      (x0 := UInt256.ofNat (contractSignatureCallEnd ptr len)) (x1 := signatureMagicWord)) ::
      memLoad ⟨64⟩ (wordBytesArgsMemory mem (ptr + 36) len hash words) :: ⟨8785⟩ ::
      UInt256.land _ owner :: ⟨0⟩ :: ⟨0⟩ ::
      memLoad ⟨64⟩ (wordBytesArgsMemory mem (ptr + 36) len hash words) :: _ = _
    rw [hmemory, contractSignatureEncodedMemory_free _ _ _ _ _ hn hp,
      contractSignatureArgs_free hf hm hp, safeAddressMask]
  obtain ⟨aw', k', C', h₁⟩ := safeRuntime_block_8706_packed (by simp; omega) (by jump_dest) h
  rw [hmemory, hstack] at h₁
  exact ⟨aw', k', C', h₁⟩

end Benchmarks.Safe
