import Benchmarks.Safe.ViaIR.MemoryBytesDecodeValid

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
set_option maxHeartbeats 200000 in
theorem safeDecodeMemoryBytesEvidence {I g s0 σ k C aw rdata off} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R)
      solcFreePtrMem aw rdata σ k C)
    (hoff : off ≤ 2 ^ 64 + 4) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
    ∃ len aw' k' C',
      calldataWord I.calldata off = UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 192 ∧
      I.calldata.size < 2 ^ 255 ∧ off + 32 + len ≤ I.calldata.size ∧
      RD fork safeBytecode I g s0 ret (⟨128⟩ :: R)
        (memoryBytesDecoded (I.calldata.extract (off + 32) (off + 32 + len)))
        aw' rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hb : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hb
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have ht : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := ulit_toNat' _ hsize
  have hfail (hc : UInt256.slt (UInt256.ofNat off + UInt256.ofNat 31)
      (UInt256.ofNat I.calldata.size) = UInt256.ofNat 0) : RDrev fork safeBytecode g s0 := by
    have h₁ := safeRuntime_block_7262_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact safeRuntime_block_111 (by
      simp only [safeRuntime_block_7262_taken_stack, List.length_cons]; omega) h₁
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
  have h₁ := safeRuntime_block_7262_fallthrough (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]; rfl) h
  let len := (calldataWord I.calldata off).toNat
  have hword : calldataWord I.calldata off = UInt256.ofNat len :=
    (u256_ofNat_toNat _).symm
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  have h₂ := safeRuntime_block_7275 (by simp; omega) (by jump_dest) h₁
  change RD fork safeBytecode I g s0 ⟨7208⟩
    ((UInt256.ofNat off + UInt256.ofNat 32) ::
      calldataWord I.calldata (UInt256.ofNat off).toNat :: UInt256.ofNat I.calldata.size ::
      ⟨7289⟩ :: ret :: R) solcFreePtrMem aw rdata σ _ _ at h₂
  rw [ho, hword] at h₂
  have h₃ := safeRuntime_block_7208 (by simp; omega) (by jump_dest) h₂
  have hlen : (UInt256.ofNat len).toNat = len := by
    rw [← hword]
  by_cases hn : len < 2 ^ 64
  swap
  · have h₄ := safeRuntime_block_7181_taken (by simp; omega) (by
      rw [hmax, ugt_one (by rw [hlen, hmaxNat]; omega)]
      decide) (by jump_dest) h₃
    exact Or.inl (safeRuntime_block_7161 (by simp; omega) h₄)
  have h₄ := safeRuntime_block_7181_fallthrough (by simp; omega) (by
    rw [hmax, ugt_zero (by rw [hlen, hmaxNat]; omega)]
    rfl) h₃
  have h₅ := safeRuntime_block_7196 (by simp; omega) (by jump_dest) h₄
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_7220_packed (by simp; omega)
    (by jump_dest) h₅
  simp only [safeRuntime_block_7220_stack] at h₆
  have he := (memoryBytesEnd_ir solcFreePtrMem (UInt256.ofNat len)).trans
    (memoryBytesEnd_initial hn)
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  have heSize : memoryBytesInitialEnd len < UInt256.size := by
    unfold memoryBytesInitialEnd ABI.paddedSize; omega
  have heNat := ulit_toNat' (memoryBytesInitialEnd len) heSize
  have hlarge : 128 ≤ memoryBytesInitialEnd len := by unfold memoryBytesInitialEnd; omega
  by_cases hlenBound : len ≤ 2 ^ 64 - 192
  swap
  · have h₇ := safeRuntime_block_7128_taken (by simp; omega) (by
      rw [he, hf, hmax, ugt_one (by
        rw [heNat, hmaxNat]
        have := memoryBytesInitialEnd_large (len := len) (by omega)
        omega), ult_zero (by simpa only [heNat] using hlarge)]
      decide) (by jump_dest) h₆
    exact Or.inl (safeRuntime_block_7161 (by
      simp only [safeRuntime_block_7128_taken_stack, List.length_cons]; omega) h₇)
  by_cases hin : off + 32 + len ≤ I.calldata.size
  · obtain ⟨aw', k', C', hr⟩ := safeDecodeMemoryBytesValid h hword hin hs hlenBound hov hret
    exact Or.inr ⟨len, aw', k', C', hword, hlenBound, hs, hin, hr⟩
  · have h₇ := safeRuntime_block_7128_fallthrough (by simp; omega) (by
      rw [he, hf, hmax, ugt_zero (by
        rw [heNat, hmaxNat]; have := memoryBytesInitialEnd_bound hlenBound; omega),
        ult_zero (by simpa only [heNat] using hlarge)]
      rfl) h₆
    obtain ⟨aw₈, k₈, C₈, h₈⟩ := safeRuntime_block_7157_packed (by simp; omega)
      (by jump_dest) h₇
    have hcopyEnd : ((UInt256.ofNat off + UInt256.ofNat 32) + UInt256.ofNat len).toNat =
        off + 32 + len := by
      rw [hadd off 32 (by omega), hadd (off + 32) len (by omega), ulit_toNat' _ (by omega)]
    obtain ⟨aw₉, k₉, C₉, h₉⟩ := safeRuntime_block_7234_taken_packed (by simp; omega) (by
      rw [ugt_one (by rw [ht, hcopyEnd]; omega)]
      decide) (by jump_dest) h₈
    exact Or.inl (safeRuntime_block_111 (by
      simp only [safeRuntime_block_7234_taken_stack, List.length_cons]; omega) h₉)

end Benchmarks.Safe.ViaIR
