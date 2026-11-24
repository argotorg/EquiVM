import Benchmarks.Safe.ViaIR.MemoryBytesDecoded
import Benchmarks.Safe.ViaIR.CalldataDecodeArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
set_option maxHeartbeats 200000 in
theorem safeDecodeMemoryBytesValid {I g s0 σ k C aw rdata off len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R)
      solcFreePtrMem aw rdata σ k C)
    (hword : calldataWord I.calldata off = UInt256.ofNat len)
    (hin : off + 32 + len ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hn : len ≤ 2 ^ 64 - 192) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret (⟨128⟩ :: R)
      (memoryBytesDecoded (I.calldata.extract (off + 32) (off + 32 + len)))
      aw' rdata σ k' C' := by
  have hsize : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hb : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hb
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have hlen : (UInt256.ofNat len).toNat = len := ulit_toNat' _ (by omega)
  have hstop : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by omega)
  have h₁ := safeRuntime_block_7262_fallthrough (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]
    rfl) h
  have h₂ := safeRuntime_block_7275 (by simp; omega) (by jump_dest) h₁
  change RD fork safeBytecode I g s0 ⟨7208⟩
    ((UInt256.ofNat off + UInt256.ofNat 32) ::
      calldataWord I.calldata (UInt256.ofNat off).toNat :: UInt256.ofNat I.calldata.size ::
      ⟨7289⟩ :: ret :: R) solcFreePtrMem aw rdata σ _ _ at h₂
  rw [ho, hword] at h₂
  have h₃ := safeRuntime_block_7208 (by simp; omega) (by jump_dest) h₂
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  have h₄ := safeRuntime_block_7181_fallthrough (by simp; omega) (by
    rw [hmax, ugt_zero (by rw [hlen, hmaxNat]; omega)]
    rfl) h₃
  have h₅ := safeRuntime_block_7196 (by simp; omega) (by jump_dest) h₄
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_7220_packed (by simp; omega)
    (by jump_dest) h₅
  simp only [safeRuntime_block_7220_stack] at h₆
  have he := (memoryBytesEnd_ir solcFreePtrMem (UInt256.ofNat len)).trans
    (memoryBytesEnd_initial (by omega))
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  have heNat : (UInt256.ofNat (memoryBytesInitialEnd len)).toNat =
      memoryBytesInitialEnd len := ulit_toNat' _ (by
    have := memoryBytesInitialEnd_bound hn; omega)
  have hlarge : 128 ≤ memoryBytesInitialEnd len := by unfold memoryBytesInitialEnd; omega
  have h₇ := safeRuntime_block_7128_fallthrough (by simp; omega) (by
    rw [he, hf, hmax, ugt_zero (by
      rw [heNat, hmaxNat]; have := memoryBytesInitialEnd_bound hn; omega),
      ult_zero (by simpa only [heNat] using hlarge)]
    rfl) h₆
  simp only [safeRuntime_block_7128_fallthrough_stack] at h₇
  rw [he, hf] at h₇
  obtain ⟨aw₈, k₈, C₈, h₈⟩ := safeRuntime_block_7157_packed (by simp; omega)
    (by jump_dest) h₇
  have hcopyEnd : (UInt256.ofNat off + UInt256.ofNat 32) + UInt256.ofNat len =
      UInt256.ofNat (off + 32 + len) := by
    rw [hadd off 32 (by omega), hadd (off + 32) len (by omega)]
  obtain ⟨aw₉, k₉, C₉, h₉⟩ := safeRuntime_block_7234_fallthrough_packed (by simp; omega)
    (by
      rw [hcopyEnd, ugt_zero (by rw [hstop, ulit_toNat' _ (by omega)]; exact hin)]
      rfl) h₈
  simp only [safeRuntime_block_7234_fallthrough_stack,
    safeRuntime_block_7234_fallthrough_memory, safeRuntime_block_7157_memory] at h₉
  change RD fork safeBytecode I g s0 ⟨7248⟩
    (UInt256.ofNat len :: (UInt256.ofNat off + UInt256.ofNat 32) :: ⟨128⟩ ::
      ⟨7289⟩ :: ⟨128⟩ :: ret :: R) (memoryBytesInitialHeader len) aw₉ rdata σ k₉ C₉ at h₉
  obtain ⟨aw₁₀, k₁₀, C₁₀, h₁₀⟩ := safeRuntime_block_7248_packed (by simp; omega)
    (by jump_dest) h₉
  have h₁₁ := safeRuntime_block_7289 (by simp; omega) hret h₁₀
  have hz : ((⟨128⟩ : UInt256) + UInt256.ofNat len + UInt256.ofNat 32).toNat =
      160 + len := by
    change ((UInt256.ofNat 128 + UInt256.ofNat len) + UInt256.ofNat 32).toNat = _
    rw [hadd 128 len (by omega), hadd (128 + len) 32 (by omega), ulit_toNat' _ (by omega)]
    omega
  simp only [safeRuntime_block_7289_stack, safeRuntime_block_7248_memory,
    hadd off 32 (by omega), ulit_toNat' (off + 32) (by omega), hlen, hz] at h₁₁
  change RD fork safeBytecode I g s0 ret (⟨128⟩ :: R)
    (writeWord (I.calldata.write (off + 32) (memoryBytesInitialHeader len) 160 len)
      (160 + len) ⟨0⟩) _ _ _ _ _ at h₁₁
  rw [memoryBytesDecoded_copy hin] at h₁₁
  exact ⟨_, _, _, h₁₁⟩

end Benchmarks.Safe.ViaIR
