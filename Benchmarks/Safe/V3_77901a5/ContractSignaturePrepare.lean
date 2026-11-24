import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_037
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_038
import Benchmarks.Safe.V3_77901a5.ContractSignatureEncode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeContractSignatureBufferMemory {mem : ByteArray} {ptr len : Nat}
    {hash : UInt256} {words : List UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hn : words.length = (len + 31) / 32) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 164 + 32 * words.length < UInt256.size) :
    safeRuntime_block_8706_memory
      (mem := contractSignatureArgsMemory mem ptr len hash words)
      (x0 := UInt256.ofNat (contractSignatureCallEnd ptr len)) (x1 := signatureMagicWord) =
        contractSignatureBufferMemory mem ptr len hash words := by
  have hfree := contractSignatureArgs_free (len := len) (hash := hash) (words := words)
    hf hm hp hn
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  have hlen : contractSignatureCallLength len = 100 + 32 * words.length := by
    simp only [contractSignatureCallLength, ABI.paddedSize, hn]
  have hend : contractSignatureCallEnd ptr len = ptr + 132 + 32 * words.length := by
    rw [contractSignatureCallEnd, hlen]
    omega
  have hdiff : UInt256.sub
      (UInt256.sub (UInt256.ofNat (contractSignatureCallEnd ptr len)) (UInt256.ofNat ptr))
      (UInt256.ofNat 32) = UInt256.ofNat (contractSignatureCallLength len) := by
    have hd₁ : UInt256.sub (UInt256.ofNat (contractSignatureCallEnd ptr len))
        (UInt256.ofNat ptr) = UInt256.ofNat (32 + contractSignatureCallLength len) := by
      apply u256_inj
      rw [usub_ofNat_lit_toNat (n := contractSignatureCallEnd ptr len) (c := ptr)
          (by rw [hend]; omega) (by rw [hend]; omega),
        ulit_toNat' (32 + contractSignatureCallLength len) (by rw [hlen]; omega)]
      rw [hend, hlen]
      omega
    rw [hd₁]
    apply u256_inj
    rw [usub_ofNat_lit_toNat (n := 32 + contractSignatureCallLength len) (c := 32)
        (by omega) (by rw [hlen]; omega),
      ulit_toNat' (contractSignatureCallLength len) (by rw [hlen]; omega)]
    omega
  have h32 : UInt256.ofNat ptr + UInt256.ofNat 32 = UInt256.ofNat (ptr + 32) := by
    rw [u256_add_comm]; exact u256_32_add_ofNat ptr
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hnot : UInt256.lnot (UInt256.ofNat (2 ^ 224 - 1)) =
      UInt256.ofNat (2 ^ 256 - 2 ^ 224) := by decide +kernel
  simp only [safeRuntime_block_8706_memory, hfree, hdiff, h32, hmask, hnot,
    ulit_toNat' ptr (by omega), ulit_toNat' (ptr + 32) (by omega)]
  change writeWord (contractSignatureStoredMemory mem ptr len hash words) (ptr + 32)
    (replaceSelectorWord (memLoad (UInt256.ofNat (ptr + 32))
      (contractSignatureStoredMemory mem ptr len hash words)) signatureMagicWord) = _
  apply replaceSelectorStore
  · rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega
  · rw [memLoadReadWord, ulit_toNat' _ (by omega),
      toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize _ _ _)]

theorem safeContractSignaturePrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src subptr len} {hash offset owner ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7036⟩
      (UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hsub : UInt256.ofNat 32 + (offset + UInt256.ofNat src) = UInt256.ofNat subptr)
    (hl : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (subptr + 32) words)
    (hn : words.length = (len + 31) / 32) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 100)
    (hb : ptr + 512 + 64 * words.length < UInt256.size) (hov : R.length + 33 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨8796⟩
      (gasArg :: UInt256.land owner solcAddrMask :: UInt256.ofNat (contractSignatureCallEnd ptr len) ::
        UInt256.ofNat (contractSignatureCallLength len) :: UInt256.ofNat (contractSignatureCallEnd ptr len) :: ⟨0⟩ ::
        UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) ::
        UInt256.land owner solcAddrMask :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat subptr :: hash :: owner :: ⟨7053⟩ :: UInt256.ofNat subptr ::
        UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeContractSignatureEncode words h hf hsub hl hw hn hin ha hsrc
    (by omega) hov
  have hpatch := safeContractSignatureBufferMemory (len := len) (hash := hash) (words := words)
    hf hn hm hp (by omega)
  have hfree := contractSignatureArgs_free (len := len) (hash := hash) (words := words)
    hf hm hp hn
  have hbufree := contractSignatureBufferMemory_free mem ptr len hash words hn hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree hbufree
  have h₂ := safeRuntime_block_8706 (by simp; omega) (by jump_dest) h₁
  dsimp only [safeRuntime_block_8706_memory] at hpatch
  simp only [safeRuntime_block_8706_stack, safeRuntime_block_8706_memory] at h₂
  rw [hpatch] at h₂
  simp only [hfree, hbufree, safeAddressMask, u256_land_comm solcAddrMask] at h₂
  have hlen : contractSignatureCallLength len = 32 * (3 + (len + 31) / 32) + 4 :=
    contractSignatureCallLength_words len
  have hload := contractSignatureBufferMemory_length mem ptr len hash words hn hp (by omega)
  rw [hlen] at hload
  obtain ⟨_, _, _, h₃⟩ := safeRawBytesEncode h₂ hload
    (contractSignatureBufferMemory_end _ _ _ _ _ hn)
    (by dsimp [contractSignatureCallEnd]; rw [hlen]; omega)
    (by dsimp [contractSignatureCallEnd]; rw [hlen, hn] at *; omega)
    (by simp; omega) (by jump_dest)
  have he : contractSignatureCallEnd ptr len + 32 * (3 + (len + 31) / 32) + 4 =
      contractSignatureCallEnd ptr len + contractSignatureCallLength len := by rw [hlen]; omega
  rw [he] at h₃
  change RD fork safeBytecode I g s0 ⟨8785⟩ _
    (contractSignatureCallMemory mem ptr len hash words) _ rdata σ _ _ at h₃
  have hfree' := contractSignatureCallMemory_free mem ptr len hash words hn hm hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree'
  have hsum : UInt256.ofNat (contractSignatureCallEnd ptr len) +
      UInt256.ofNat (contractSignatureCallLength len) =
      UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) := by
    have hb' : contractSignatureCallEnd ptr len + contractSignatureCallLength len < UInt256.size := by
      dsimp [contractSignatureCallEnd]; rw [hlen, hn] at *; omega
    apply u256_inj
    rw [ulit_toNat' _ hb']
    exact uadd_ofNat_toNat (by omega) (by omega) hb'
  have hdiff : UInt256.sub
      (UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len))
      (UInt256.ofNat (contractSignatureCallEnd ptr len)) =
      UInt256.ofNat (contractSignatureCallLength len) := by
    rw [← hsum, word_add_sub_left]
  have h₄ := safeRuntime_block_8785 (by simp; omega) h₃
  simp only [safeRuntime_block_8785_stack, hfree', hdiff] at h₄
  exact ⟨_, _, _, _, h₄⟩

end Benchmarks.Safe.V3_77901a5
