import Benchmarks.Safe.ContractSignatureEncode
import Benchmarks.Safe.Blocks.Runtime_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeContractSignatureCopy {I g s0 σ k C aw mem rdata ptr src len}
    {hash owner ret : UInt256} {words : List UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11834⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len) :: UInt256.ofNat ptr :: ⟨8785⟩ ::
        UInt256.land solcAddrMask owner :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureEncodedMemory mem ptr len hash words) aw rdata σ k C)
    (hp : 96 ≤ ptr) (hn : words.length = (len + 31) / 32)
    (hb : contractSignatureCallEnd ptr len + contractSignatureCallLength len + 64 < UInt256.size)
    (hov : R.length + 26 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨8785⟩
      (UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) ::
        UInt256.land solcAddrMask owner :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  have hptr : ptr < UInt256.size := by
    simp only [contractSignatureCallEnd] at hb
    omega
  have hlen : memLoad (UInt256.ofNat ptr)
      (contractSignatureEncodedMemory mem ptr len hash words) =
        UInt256.ofNat (contractSignatureCallLength len) := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' ptr hptr]
    exact contractSignatureEncodedMemory_length _ _ _ _ _ hn hp
  have h32 : UInt256.ofNat ptr + UInt256.ofNat 32 = UInt256.ofNat (ptr + 32) := by
    rw [u256_add_comm]
    exact u256_32_add_ofNat ptr
  have h₁ := safeRuntime_block_11834 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_11834_stack, hlen, h32] at h₁
  obtain ⟨_, _, _, h₂⟩ := safeForwardBytesCopy h₁
    (by dsimp [contractSignatureCallLength]; omega)
    (by rw [contractSignatureEncodedMemory_size _ _ _ _ _ hn]
        dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
        omega) (le_refl _) hb (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_11851 (by simp; omega) (by jump_dest) h₂
  have hadd : UInt256.ofNat (contractSignatureCallLength len) +
      UInt256.ofNat (contractSignatureCallEnd ptr len) =
      UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    simpa only [Nat.add_comm] using
      (uadd_ofNat_toNat (a := contractSignatureCallLength len)
        (b := contractSignatureCallEnd ptr len) (by omega) (by omega) (by omega))
  simp only [safeRuntime_block_11851_stack, hadd] at h₃
  exact ⟨_, _, _, h₃⟩

set_option maxRecDepth 100000 in
theorem safeContractSignaturePrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash owner ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8677⟩
      (UInt256.ofNat src :: hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 36)
    (hb : contractSignatureCallEnd ptr len + contractSignatureCallLength len + 64 < UInt256.size)
    (hov : R.length + 26 ≤ 1024) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨8796⟩
      (gasArg :: UInt256.land solcAddrMask owner ::
        UInt256.ofNat (contractSignatureCallEnd ptr len) ::
        UInt256.ofNat (contractSignatureCallLength len) ::
        UInt256.ofNat (contractSignatureCallEnd ptr len) :: ⟨0⟩ ::
        UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) ::
        UInt256.land solcAddrMask owner :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ptr :: ⟨0⟩ ::
        UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeContractSignatureArgs words h hf hl hw hn hin ha (by
    simp only [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize, ← hn] at hb
    omega) hov
  obtain ⟨_, _, _, h₂⟩ := safeContractSignatureEncode h₁ hf hm hp hn (by omega) (by omega)
  obtain ⟨_, _, _, h₃⟩ := safeContractSignatureCopy h₂ hp hn hb hov
  have hfree := contractSignatureCallMemory_free mem ptr len hash words hn hp
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_8785_packed (by simp; omega) h₃
  have hsub : UInt256.sub
      (UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len))
      (UInt256.ofNat (contractSignatureCallEnd ptr len)) =
        UInt256.ofNat (contractSignatureCallLength len) := by
    have hadd : UInt256.ofNat (contractSignatureCallEnd ptr len) +
        UInt256.ofNat (contractSignatureCallLength len) =
        UInt256.ofNat (contractSignatureCallEnd ptr len + contractSignatureCallLength len) := by
      apply u256_inj
      rw [ulit_toNat' _ (by omega)]
      exact uadd_ofNat_toNat (by omega) (by omega) (by omega)
    rw [← hadd, word_add_sub_left]
  simp only [safeRuntime_block_8785_stack, hfree, hsub] at h₄
  exact ⟨_, aw', k', C', h₄⟩

end Benchmarks.Safe
