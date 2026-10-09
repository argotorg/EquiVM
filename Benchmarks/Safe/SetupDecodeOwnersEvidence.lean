import Benchmarks.Safe.SetupDecodeOwners

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeSetupDecodeOwnersEvidence {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10399⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    RDrev safeBytecode g s0 ∨
    ∃ n k' C', 260 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = UInt256.ofNat n ∧
      n ≤ 2 ^ 64 - 1 ∧ setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size ∧
      RD safeBytecode I g s0 ⟨10503⟩ (setupDecodeOwnersStack I.calldata n ret R)
        mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hfail (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 256) = ⟨1⟩) : RDrev safeBytecode g s0 := by
    have h₁ := safeRuntime_block_10399_fallthrough (by simp; omega)
      (by rw [hc]; decide) h
    exact safeRuntime_block_10422 (by
      simp only [safeRuntime_block_10399_fallthrough_stack, List.length_cons]; omega) h₁
  by_cases hh : 260 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong (by exact Nat.lt_of_not_ge hh)
      hsize (by decide)))
  by_cases hs0 : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge
      (by change 2 ^ 255 + 4 ≤ I.calldata.size; omega) hsize (by decide)))
  have h₁ := safeRuntime_block_10399_taken (by simp; omega) (by
    rw [solcDecodeLenCheckOk (by exact hh) hs0 hsize (by decide)]
    decide) (by jump_dest) h
  simp only [safeRuntime_block_10399_taken_stack] at h₁
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  by_cases ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1
  swap
  · have h₂ := safeRuntime_block_10425_fallthrough (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata 4) _) = _
      rw [hmax, ugt_one (by exact Nat.lt_of_not_ge ho)]; decide) h₁
    exact Or.inl (safeRuntime_block_10443 (by
      simp only [safeRuntime_block_10425_fallthrough_stack, List.length_cons]; omega) h₂)
  have h₂ := safeRuntime_block_10425_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 4) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 4 =
      UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 4).toNat (by omega)
  have hheadFail (hc : UInt256.slt
      (UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat + 31))
      (UInt256.ofNat I.calldata.size) = ⟨0⟩) : RDrev safeBytecode g s0 := by
    have h₃ := safeRuntime_block_10446_fallthrough (by simp; omega) (by
      change UInt256.sgt (UInt256.ofNat I.calldata.size)
        ((⟨4⟩ + calldataWord I.calldata 4) + UInt256.ofNat 31) = _
      rw [hoff, wordOfNatAdd _ 31 (by omega), wordSgtReverse, hc]
      rfl) h₂
    exact safeRuntime_block_10459 (by
      simp only [safeRuntime_block_10446_fallthrough_stack,
        safeRuntime_block_10425_taken_stack, List.length_cons]; omega) h₃
  by_cases hs : I.calldata.size < 2 ^ 255
  swap
  · exact Or.inl (hheadFail (slt_zero_low_high (by
      rw [ulit_toNat' _ (by omega)]; omega) (by rw [ulit_toNat' _ hsize]; omega)))
  by_cases hhead : setupOwnersStart I.calldata ≤ I.calldata.size
  swap
  · exact Or.inl (hheadFail (slt_ofNat_lit_zero hs
      (by dsimp only [setupOwnersStart] at hhead; omega) (by omega)))
  have h₃ := safeRuntime_block_10446_taken (by simp; omega) (by
    change UInt256.sgt (UInt256.ofNat I.calldata.size)
      ((⟨4⟩ + calldataWord I.calldata 4) + UInt256.ofNat 31) ≠ _
    rw [hoff, wordOfNatAdd _ 31 (by omega), wordSgtReverse,
      slt_ofNat_lit_one_low hs (by dsimp only [setupOwnersStart] at hhead; omega)]
    decide) (by jump_dest) h₂
  change RD safeBytecode I g s0 ⟨10462⟩
    ((⟨4⟩ + calldataWord I.calldata 4) :: setupDecodeZeros I.calldata ret R)
    mem aw rdata σ _ _ at h₃
  rw [hoff] at h₃
  let n := (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
  have hw : calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) =
      UInt256.ofNat n := (u256_ofNat_toNat _).symm
  have hoNat : (UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat)).toNat =
      4 + (calldataWord I.calldata 4).toNat := ulit_toNat' _ (by omega)
  by_cases hn : n ≤ 2 ^ 64 - 1
  swap
  · have h₄ := safeRuntime_block_10462_fallthrough (by simp [setupDecodeZeros]; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata _) _) = _
      rw [hoNat, hmax, ugt_one (by exact Nat.lt_of_not_ge hn)]
      decide) h₃
    exact Or.inl (safeRuntime_block_10480 (by
      simp only [safeRuntime_block_10462_fallthrough_stack, setupDecodeZeros,
        List.length_cons, List.length_append, List.length_nil]; omega) h₄)
  by_cases hin : setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size
  · obtain ⟨k', C', hr⟩ := safeSetupDecodeOwnersValid h hh hs ho hw hn hin hov
    exact Or.inr ⟨n, k', C', hh, hs, ho, hw, hn, hin, hr⟩
  have h₄ := safeRuntime_block_10462_taken (by simp [setupDecodeZeros]; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata _) _) ≠ _
    rw [hoNat, hmax, ugt_zero hn]; decide) (by jump_dest) h₃
  change RD safeBytecode I g s0 ⟨10483⟩
    (calldataWord I.calldata (UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat)).toNat ::
      UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) ::
      setupDecodeZeros I.calldata ret R) mem aw rdata σ _ _ at h₄
  rw [hoNat, hw] at h₄
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
  have h₅ := safeRuntime_block_10483_fallthrough (by simp; omega) (by
    rw [hshift, wordOfNatAdd _ _ (by omega), wordOfNatAdd _ 32 (by omega), ugt_one (by
      rw [ulit_toNat' _ hsize, ulit_toNat' _ (by omega)]
      dsimp only [setupOwnersStart] at hin
      omega)]
    decide) h₄
  exact Or.inl (safeRuntime_block_10500 (by simp [setupDecodeZeros]; omega) h₅)

end Benchmarks.Safe
