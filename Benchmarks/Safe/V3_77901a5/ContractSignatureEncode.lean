import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_037
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_043
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_051
import Benchmarks.Safe.V3_77901a5.ContractSignatureMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

theorem contractSignatureHeaderMemory_size (mem : ByteArray) (ptr : Nat) (hash : UInt256) :
    (contractSignatureHeaderMemory mem ptr hash).size = max mem.size (ptr + 100) := by
  rw [contractSignatureHeaderMemory, writeWords_size_nonempty _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil]

theorem contractSignatureHeaderMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (hash : UInt256) (hin : off + count ≤ mem.size) (ha : off + count ≤ ptr) :
    (contractSignatureHeaderMemory mem ptr hash).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureHeaderMemory, writeWords_readBelow _ _ _ _ _ hin (by omega)]

theorem contractSignatureArgs_free {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hn : words.length = (len + 31) / 32) :
    memLoad ⟨64⟩ (contractSignatureArgsMemory mem ptr len hash words) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    contractSignatureArgsMemory, wordBytesArgsMemory_preserved _ _ _ _ _ _ _ hm (by omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

theorem safeContractSignatureArgs (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11810⟩
      (UInt256.ofNat (ptr + 36) :: UInt256.ofNat src :: hash :: ret :: R)
      mem aw rdata σ k C)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (src + 32) words)
    (hn : words.length = (len + 31) / 32)
    (hin : src + 32 ≤ mem.size) (ha : src + 32 ≤ ptr)
    (hsrc : src + 32 + 32 * words.length ≤ ptr + 100)
    (hb : ptr + 164 + 32 * words.length < UInt256.size)
    (hov : R.length + 19 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: R)
      (contractSignatureArgsMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hadd (n : Nat) (hh : ptr + 36 + n < UInt256.size) :
      UInt256.ofNat (ptr + 36) + UInt256.ofNat n =
      UInt256.ofNat (ptr + 36 + n) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  have hm : safeRuntime_block_11810_memory
      (mem := mem) (x0 := UInt256.ofNat (ptr + 36))
      (x2 := hash) = contractSignatureHeaderMemory mem ptr hash := by
    simp only [safeRuntime_block_11810_memory, hadd 32 (by omega),
      ulit_toNat' (ptr + 36) (by omega), ulit_toNat' (ptr + 36 + 32) (by omega),
      contractSignatureHeaderMemory, writeWords, Reasoning.Theory.writeWord]
    rfl
  have hload : memLoad (UInt256.ofNat src) (contractSignatureHeaderMemory mem ptr hash) =
      UInt256.ofNat len := by
    rw [memLoadReadWord, ulit_toNat' src (by omega),
      contractSignatureHeaderMemory_preserved _ _ _ _ _ hin ha,
      ← ulit_toNat' src (by omega), ← memLoadReadWord, hl]
  have h₁ := safeRuntime_block_11810 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11810_stack, hm, hadd 64 (by omega),
    show ptr + 36 + 64 = ptr + 100 by omega] at h₁
  obtain ⟨_, _, _, h₂⟩ := safeMemoryBytesEncodeInto words h₁ hload hw hn hsrc
    (by rw [contractSignatureHeaderMemory_size]; omega) (by omega)
    (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_9836 (by omega) hret h₂
  have he : ptr + 100 + 32 + 32 * words.length = contractSignatureCallEnd ptr len := by
    simp only [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  exact ⟨_, _, _, by simpa only [safeRuntime_block_9836_stack, he] using h₃⟩

theorem safeContractSignatureEncode (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src subptr len} {hash offset owner ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7036⟩
      (UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hsub : UInt256.ofNat 32 + (offset + UInt256.ofNat src) = UInt256.ofNat subptr)
    (hl : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (subptr + 32) words)
    (hn : words.length = (len + 31) / 32)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 100)
    (hb : ptr + 164 + 32 * words.length < UInt256.size) (hov : R.length + 33 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨8706⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: signatureMagicWord :: ⟨0⟩ :: ⟨0⟩ ::
        UInt256.ofNat subptr :: hash :: owner :: ⟨7053⟩ :: UInt256.ofNat subptr ::
        UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureArgsMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hadd : UInt256.ofNat 36 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 36) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact (uadd_ofNat_toNat (a := 36) (b := ptr) (by decide) (by omega) (by omega)).trans
      (by omega)
  have h₁ := safeRuntime_block_7036 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_7036_stack, hsub] at h₁
  have h₂ := safeRuntime_block_8677 (by simp; omega) (by jump_dest) h₁
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8677_stack, hf, hadd] at h₂
  exact safeContractSignatureArgs words h₂ hl hw hn hin ha hsrc hb (by simp; omega)
    (by jump_dest)

end Benchmarks.Safe.V3_77901a5
