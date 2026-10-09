import Benchmarks.Safe.MemoryBytesDecoded
import Benchmarks.Safe.CalldataDecodeArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeDecodeMemoryBytesValid {I g s0 σ k C aw rdata off len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9242⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R)
      solcFreePtrMem aw rdata σ k C)
    (hword : calldataWord I.calldata off = UInt256.ofNat len)
    (hin : off + 32 + len ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hn : len ≤ 2 ^ 64 - 192) (hov : R.length + 10 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret (⟨128⟩ :: R)
      (memoryBytesDecoded (I.calldata.extract (off + 32) (off + 32 + len)))
      aw' rdata σ k' C' := by
  have hsize : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hb : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hb
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have hlen : (UInt256.ofNat len).toNat = len := ulit_toNat' _ (by omega)
  have hstop : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    ulit_toNat' _ (by omega)
  have h₁ := safeRuntime_block_9242_taken (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]
    decide) (by jump_dest) h
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  have h₁' : RD safeBytecode I g s0 ⟨9257⟩
      (⟨0⟩ :: UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R)
      solcFreePtrMem _ rdata σ _ _ := h₁
  have h₂ := safeRuntime_block_9257_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat)
      _) ≠ UInt256.ofNat 0
    rw [ho, hword, hmax, ugt_zero (by rw [hlen, hmaxNat]; omega)]
    decide) (by jump_dest) h₁'
  simp only [safeRuntime_block_9257_taken_stack, ho] at h₂
  change RD safeBytecode I g s0 _ (calldataWord I.calldata off :: _) _ _ _ _ _ _ at h₂
  rw [hword] at h₂
  have he := memoryBytesEnd_initial (by omega : len < 2 ^ 64)
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  have heNat : (UInt256.ofNat (memoryBytesInitialEnd len)).toNat =
      memoryBytesInitialEnd len := ulit_toNat' _ (by
    have := memoryBytesInitialEnd_bound hn; omega)
  have hlarge : 128 ≤ memoryBytesInitialEnd len := by unfold memoryBytesInitialEnd; omega
  have h₃ := safeRuntime_block_9282_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.lor (UInt256.lt (memoryBytesEnd solcFreePtrMem
      (UInt256.ofNat len)) (memLoad (UInt256.ofNat 64) solcFreePtrMem))
      (UInt256.gt (memoryBytesEnd solcFreePtrMem (UInt256.ofNat len)) _)) ≠ UInt256.ofNat 0
    rw [he, hf, hmax, ult_zero (by simpa only [heNat] using hlarge),
      ugt_zero (by rw [heNat, hmaxNat]; have := memoryBytesInitialEnd_bound hn; omega)]
    decide) (by jump_dest) h₂
  change RD safeBytecode I g s0 _
    (memoryBytesEnd solcFreePtrMem (UInt256.ofNat len) ::
      memLoad (UInt256.ofNat 64) solcFreePtrMem :: UInt256.ofNat len :: _) _ _ _ _ _ _ at h₃
  rw [he, hf] at h₃
  have hcopyEnd : UInt256.ofNat 32 + (UInt256.ofNat len + UInt256.ofNat off) =
      UInt256.ofNat (off + 32 + len) := by
    rw [hadd len off (by omega), hadd 32 (len + off) (by omega)]
    congr 1; omega
  have h₄ := safeRuntime_block_9328_taken (by simp; omega) (by
    rw [hcopyEnd, ult_zero (by rw [hstop, ulit_toNat' _ (by omega)]; exact hin)]
    decide) (by jump_dest) h₃
  change RD safeBytecode I g s0 _
    (UInt256.ofNat 128 :: UInt256.ofNat len :: ⟨0⟩ :: UInt256.ofNat off ::
      UInt256.ofNat I.calldata.size :: ret :: R) (memoryBytesInitialHeader len) _ _ _ _ _ at h₄
  have h₅ := safeRuntime_block_9351 (by simp; omega) hret h₄
  have hz : (UInt256.ofNat 32 + (UInt256.ofNat 128 + UInt256.ofNat len)).toNat = 160 + len := by
    rw [hadd 128 len (by omega), hadd 32 (128 + len) (by omega), ulit_toNat' _ (by omega)]
    omega
  simp only [safeRuntime_block_9351_stack, safeRuntime_block_9351_memory,
    hadd off 32 (by omega), ulit_toNat' (off + 32) (by omega), hlen, hz] at h₅
  change RD safeBytecode I g s0 ret (⟨128⟩ :: R)
    (writeWord (I.calldata.write (off + 32) (memoryBytesInitialHeader len) 160 len)
      (160 + len) ⟨0⟩) _ _ _ _ _ at h₅
  rw [memoryBytesDecoded_copy hin] at h₅
  exact ⟨_, _, _, h₅⟩

end Benchmarks.Safe
