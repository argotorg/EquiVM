import Benchmarks.Safe.MemoryBytesDecodeValid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeDecodeMemoryBytesEvidence {I g s0 σ k C aw rdata off} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9242⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R)
      solcFreePtrMem aw rdata σ k C)
    (hoff : off ≤ 2 ^ 64 + 4) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 10 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ len aw' k' C',
      calldataWord I.calldata off = UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 192 ∧
      I.calldata.size < 2 ^ 255 ∧ off + 32 + len ≤ I.calldata.size ∧
      RD safeBytecode I g s0 ret (⟨128⟩ :: R)
        (memoryBytesDecoded (I.calldata.extract (off + 32) (off + 32 + len)))
        aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hb : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hb
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have ht : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := ulit_toNat' _ hsize
  have hfail (hc : UInt256.slt (UInt256.ofNat off + UInt256.ofNat 31)
      (UInt256.ofNat I.calldata.size) = UInt256.ofNat 0) : RDrev safeBytecode g s0 := by
    have h₁ := safeRuntime_block_9242_fallthrough (by simp; omega) hc h
    exact safeRuntime_block_9254 (by
      simp only [safeRuntime_block_9242_fallthrough_stack, List.length_cons]; omega) h₁
  by_cases hs : I.calldata.size < 2 ^ 255
  swap
  · exact Or.inl (hfail (by
      rw [hadd off 31 (by omega)]
      exact slt_zero_low_high (by rw [ulit_toNat' _ (by omega)]; omega) (by rw [ht]; omega)))
  by_cases hhead : off + 32 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (by
      rw [hadd off 31 (by omega)]
      exact slt_ofNat_lit_zero hs (by omega) (by omega)))
  have h₁ := safeRuntime_block_9242_taken (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]; decide) (by jump_dest) h
  let len := (calldataWord I.calldata off).toNat
  have hword : calldataWord I.calldata off = UInt256.ofNat len :=
    (u256_ofNat_toNat _).symm
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  by_cases hn : len < 2 ^ 64
  swap
  · have h₂ := safeRuntime_block_9257_fallthrough (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat)
        _) = UInt256.ofNat 0
      rw [ho, hmax, ugt_one (by rw [hmaxNat]; change 2 ^ 64 - 1 < len; omega)]
      decide) h₁
    have h₃ := safeRuntime_block_9275 (by
      simp only [safeRuntime_block_9257_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₂
    exact Or.inl (safeRuntime_block_9222 (by
      simp only [safeRuntime_block_9275_stack, safeRuntime_block_9257_fallthrough_stack,
        List.length_cons]; omega) h₃)
  have hlen : (UInt256.ofNat len).toNat = len := ulit_toNat' _ (by omega)
  have h₂ := safeRuntime_block_9257_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat)
      _) ≠ UInt256.ofNat 0
    rw [ho, hmax, ugt_zero (by rw [hmaxNat]; change len ≤ 2 ^ 64 - 1; omega)]
    decide) (by jump_dest) h₁
  simp only [safeRuntime_block_9257_taken_stack, ho] at h₂
  change RD safeBytecode I g s0 _ (calldataWord I.calldata off :: _) _ _ _ _ _ _ at h₂
  rw [hword] at h₂
  have he := memoryBytesEnd_initial hn
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  have heSize : memoryBytesInitialEnd len < UInt256.size := by
    unfold memoryBytesInitialEnd ABI.paddedSize; omega
  have heNat := ulit_toNat' (memoryBytesInitialEnd len) heSize
  have hlarge : 128 ≤ memoryBytesInitialEnd len := by unfold memoryBytesInitialEnd; omega
  have he' := he
  unfold memoryBytesEnd at he'
  by_cases hlenBound : len ≤ 2 ^ 64 - 192
  swap
  · have h₃ := safeRuntime_block_9282_fallthrough (by simp; omega) (by
      rw [he', hf, hmax, ult_zero (by simpa only [heNat] using hlarge),
        ugt_one (by
          rw [heNat, hmaxNat]
          have := memoryBytesInitialEnd_large (len := len) (by omega)
          omega)]
      decide) h₂
    have h₄ := safeRuntime_block_9321 (by
      simp only [safeRuntime_block_9282_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact Or.inl (safeRuntime_block_9222 (by
      simp only [safeRuntime_block_9321_stack, safeRuntime_block_9282_fallthrough_stack,
        List.length_cons]; omega) h₄)
  by_cases hin : off + 32 + len ≤ I.calldata.size
  · obtain ⟨aw', k', C', hr⟩ := safeDecodeMemoryBytesValid h hword hin hs hlenBound hov hret
    exact Or.inr ⟨len, aw', k', C', hword, hlenBound, hs, hin, hr⟩
  · have h₃ := safeRuntime_block_9282_taken (by simp; omega) (by
      rw [he', hf, hmax, ult_zero (by simpa only [heNat] using hlarge),
        ugt_zero (by rw [heNat, hmaxNat]; have := memoryBytesInitialEnd_bound hlenBound; omega)]
      decide) (by jump_dest) h₂
    have hcopyEnd : (UInt256.ofNat 32 + (UInt256.ofNat len + UInt256.ofNat off)).toNat =
        off + 32 + len := by
      rw [hadd len off (by omega), hadd 32 (len + off) (by omega), ulit_toNat' _ (by omega)]
      omega
    have h₄ := safeRuntime_block_9328_fallthrough (by simp; omega) (by
      rw [ult_one (by rw [ht, hcopyEnd]; omega)]; decide) h₃
    exact Or.inl (safeRuntime_block_9348 (by
      simp only [safeRuntime_block_9328_fallthrough_stack,
        safeRuntime_block_9282_taken_stack, List.length_cons]; omega) h₄)

end Benchmarks.Safe
