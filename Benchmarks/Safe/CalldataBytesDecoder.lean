import Benchmarks.Safe.MemoryBytesDecodeValid
import Benchmarks.Safe.Blocks.Runtime_039
import Benchmarks.Safe.Blocks.Runtime_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeDecodeCalldataBytesValid {I g s0 σ k C aw mem rdata off len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9154⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hw : calldataWord I.calldata off = UInt256.ofNat len)
    (hi : off + 32 + len ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hn : len ≤ 2 ^ 64 - 1) (hov : R.length + 9 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (UInt256.ofNat len :: UInt256.ofNat (off + 32) :: R) mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hab : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hab
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have hl : (UInt256.ofNat len).toNat = len := ulit_toNat' _ (by omega)
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9154_taken (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_9170_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat) _) ≠ _
    rw [ho, hw, hmax, ugt_zero (by
      rw [hl, show (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 by decide +kernel]
      exact hn)]
    decide) (by jump_dest) h₁
  simp only [safeRuntime_block_9170_taken_stack, safeRuntime_block_9154_taken_stack, ho] at h₂
  change RD safeBytecode I g s0 ⟨9192⟩
    (calldataWord I.calldata off :: ⟨0⟩ :: UInt256.ofNat off ::
      UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ _ _ at h₂
  rw [hw] at h₂
  have h₃ := safeRuntime_block_9192_taken (by simp; omega) (by
    rw [hadd off len (by omega), hadd (off + len) 32 (by omega), ugt_zero (by
      rw [ulit_toNat' (off + len + 32) (by omega),
        ulit_toNat' I.calldata.size (by omega)]; omega)]
    decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_9215 (by simp; omega) hret h₃
  simp only [safeRuntime_block_9215_stack, safeRuntime_block_9192_taken_stack,
    hadd off 32 (by omega)] at h₄
  exact ⟨_, _, h₄⟩

set_option maxRecDepth 100000 in
theorem safeDecodeCalldataBytesEvidence {I g s0 σ k C aw mem rdata off} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9154⟩
      (UInt256.ofNat off :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hoff : off ≤ 2 ^ 64 + 4) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 9 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ len k' C', calldataWord I.calldata off = UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 1 ∧
      I.calldata.size < 2 ^ 255 ∧ off + 32 + len ≤ I.calldata.size ∧
      RD safeBytecode I g s0 ret (UInt256.ofNat len :: UInt256.ofNat (off + 32) :: R)
        mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hadd (a b : Nat) (hb : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd a b hb
  have ho : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by omega)
  have ht : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := ulit_toNat' _ hsize
  have hfail (hc : UInt256.slt (UInt256.ofNat off + UInt256.ofNat 31)
      (UInt256.ofNat I.calldata.size) = UInt256.ofNat 0) : RDrev safeBytecode g s0 := by
    have h₁ := safeRuntime_block_9154_fallthrough (by simp; omega) hc h
    exact safeRuntime_block_9167 (by
      simp only [safeRuntime_block_9154_fallthrough_stack, List.length_cons]; omega) h₁
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
  have h₁ := safeRuntime_block_9154_taken (by simp; omega) (by
    rw [hadd off 31 (by omega), slt_ofNat_lit_one_low hs (by omega)]; decide) (by jump_dest) h
  let len := (calldataWord I.calldata off).toNat
  have hw : calldataWord I.calldata off = UInt256.ofNat len := (u256_ofNat_toNat _).symm
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  by_cases hn : len ≤ 2 ^ 64 - 1
  swap
  · have h₂ := safeRuntime_block_9170_fallthrough (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat)
        _) = UInt256.ofNat 0
      rw [ho, hmax, ugt_one (by rw [hmaxNat]; change 2 ^ 64 - 1 < len; omega)]
      decide) h₁
    exact Or.inl (safeRuntime_block_9189 (by
      simp only [safeRuntime_block_9170_fallthrough_stack,
        safeRuntime_block_9154_taken_stack, List.length_cons]; omega) h₂)
  by_cases hin : off + 32 + len ≤ I.calldata.size
  · obtain ⟨k', C', hr⟩ := safeDecodeCalldataBytesValid h hw hin hs hn hov hret
    exact Or.inr ⟨len, k', C', hw, hn, hs, hin, hr⟩
  · have h₂ := safeRuntime_block_9170_taken (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata (UInt256.ofNat off).toNat)
        _) ≠ UInt256.ofNat 0
      rw [ho, hmax, ugt_zero (by rw [hmaxNat]; exact hn)]
      decide) (by jump_dest) h₁
    simp only [safeRuntime_block_9170_taken_stack, safeRuntime_block_9154_taken_stack, ho]
      at h₂
    change RD safeBytecode I g s0 ⟨9192⟩
      (calldataWord I.calldata off :: ⟨0⟩ :: UInt256.ofNat off ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ _ _ at h₂
    rw [hw] at h₂
    have h₃ := safeRuntime_block_9192_fallthrough (by simp; omega) (by
      rw [hadd off len (by omega), hadd (off + len) 32 (by omega), ugt_one (by
        rw [ulit_toNat' (off + len + 32) (by omega), ht]; omega)]
      decide) h₂
    exact Or.inl (safeRuntime_block_9212 (by
      simp only [safeRuntime_block_9192_fallthrough_stack, List.length_cons]; omega) h₃)

end Benchmarks.Safe
