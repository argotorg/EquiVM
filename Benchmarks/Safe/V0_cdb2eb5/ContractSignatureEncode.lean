import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_042
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_050
import Benchmarks.Safe.V0_cdb2eb5.ContractSignatureMemory
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem contractSignatureHeaderMemory_size (mem : ByteArray) (ptr : Nat) (hash : UInt256) :
    (contractSignatureHeaderMemory mem ptr hash).size = max mem.size (ptr + 68) := by
  rw [contractSignatureHeaderMemory, writeWords_size_nonempty _ _ _ (by simp),
    writeWord_sparse_size]
  simp only [List.length_cons, List.length_nil]
  omega

theorem contractSignatureHeaderMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (hash : UInt256) (hin : off + count ≤ mem.size) (ha : off + count ≤ ptr) :
    (contractSignatureHeaderMemory mem ptr hash).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureHeaderMemory, writeWords_readBelow _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin ha]

theorem contractSignatureArgs_free {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hn : words.length = (len + 31) / 32) :
    memLoad ⟨64⟩ (contractSignatureCallMemory mem ptr len hash words) = UInt256.ofNat ptr := by
  rw [contractSignatureCallMemory_free _ _ _ _ _ hn hm hp, hf]

theorem safeContractSignatureArgs (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11576⟩
      (UInt256.ofNat (ptr + 4) :: UInt256.ofNat src :: hash :: ret :: R)
      (writeWord mem ptr signatureMagicWord) aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (src + 32) words)
    (hn : words.length = (len + 31) / 32)
    (hin : src + 32 ≤ mem.size) (ha : src + 32 ≤ ptr)
    (hsrc : src + 32 + 32 * words.length ≤ ptr + 68)
    (hb : ptr + 132 + 32 * words.length < UInt256.size)
    (hov : R.length + 19 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hadd (n : Nat) (hh : ptr + 4 + n < UInt256.size) :
      UInt256.ofNat (ptr + 4) + UInt256.ofNat n =
      UInt256.ofNat (ptr + 4 + n) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  have hm : safeRuntime_block_11576_memory
      (mem := writeWord mem ptr signatureMagicWord) (x0 := UInt256.ofNat (ptr + 4))
      (x2 := hash) = contractSignatureHeaderMemory mem ptr hash := by
    simp only [safeRuntime_block_11576_memory, hadd 32 (by omega),
      ulit_toNat' (ptr + 4) (by omega), ulit_toNat' (ptr + 4 + 32) (by omega),
      contractSignatureHeaderMemory, writeWords, Reasoning.Theory.writeWord]
    rfl
  have hload : memLoad (UInt256.ofNat src) (contractSignatureHeaderMemory mem ptr hash) =
      UInt256.ofNat len := by
    rw [memLoadReadWord, ulit_toNat' src (by omega),
      contractSignatureHeaderMemory_preserved _ _ _ _ _ hin ha,
      ← ulit_toNat' src (by omega), ← memLoadReadWord, hl]
  have h₁ := safeRuntime_block_11576 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11576_stack, hm, hadd 64 (by omega),
    show ptr + 4 + 64 = ptr + 68 by omega] at h₁
  obtain ⟨_, _, _, h₂⟩ := safeMemoryBytesEncodeInto words h₁ hload hw hn hsrc
    (by rw [contractSignatureHeaderMemory_size]; omega) (by omega)
    (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_9705 (by omega) hret h₂
  have he : ptr + 68 + 32 + 32 * words.length = contractSignatureCallEnd ptr len := by
    simp only [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  exact ⟨_, _, _, by simpa only [safeRuntime_block_9705_stack, he] using h₃⟩

theorem safeContractSignatureEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src subptr len} {hash offset owner ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7183⟩
      (UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hsub : UInt256.ofNat 32 + (offset + UInt256.ofNat src) = UInt256.ofNat subptr)
    (hl : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (subptr + 32) words)
    (hn : words.length = (len + 31) / 32)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 68)
    (hb : ptr + 132 + 32 * words.length < UInt256.size) (hov : R.length + 33 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7237⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: ⟨371636862⟩ ::
        UInt256.land owner solcAddrMask :: signatureMagicWord :: UInt256.ofNat subptr ::
        UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hmagic : UInt256.shiftLeft (UInt256.ofNat 185818431) (UInt256.ofNat 225) =
      signatureMagicWord := by native_decide
  have hadd : UInt256.ofNat 4 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 4) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact (uadd_ofNat_toNat (a := 4) (b := ptr) (by decide) (by omega) (by omega)).trans
      (by omega)
  have hm : safeRuntime_block_7183_memory (mem := mem) =
      writeWord mem ptr signatureMagicWord := by
    change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
    simp only [safeRuntime_block_7183_memory, hf, hmagic, ulit_toNat' ptr (by omega),
      Reasoning.Theory.writeWord]
  have h₁ := safeRuntime_block_7183 (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7183_stack, hf, hsub, hmagic, hadd, hm, safeAddressMask] at h₁
  exact safeContractSignatureArgs words h₁ hl hw hn hin ha hsrc hb (by simp; omega)
    (by jump_dest)

end Benchmarks.Safe.V0_cdb2eb5
