import Benchmarks.Safe.ViaIR.SetupDecodeOwners
import Benchmarks.Safe.ViaIR.Blocks.Runtime_014
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
theorem safeSetupDecodeOwnersEvidence {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2980⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 22 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ n k' C', 260 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = UInt256.ofNat n ∧
      n ≤ 2 ^ 64 - 1 ∧ setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size ∧
      RD fork safeBytecode I g s0 ⟨3060⟩ (setupDecodeOwnersStack I.calldata n (⟨0⟩ :: R))
        mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hfail (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
      (UInt256.ofNat 256) = ⟨1⟩) : RDrev fork safeBytecode g s0 := by
    have h₁ := safeRuntime_block_2980_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize, hc]; decide) (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) h₁
  by_cases hh : 260 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong
      (by change I.calldata.size < 260; omega) hsize (by decide)))
  by_cases hs0 : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge
      (by change 2 ^ 255 + 4 ≤ I.calldata.size; omega) hsize (by decide)))
  have h₁ := safeRuntime_block_2980_fallthrough (by simp; omega) (by
    rw [safeIRArgumentSizeSub hlong hsize, solcDecodeLenCheckOk hh hs0 hsize (by decide)]
    rfl) h
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hmaxNat : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  by_cases ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1
  swap
  · have h₂ := safeRuntime_block_2993_taken (by simp; omega) (by
      rw [hmax]
      change UInt256.gt (calldataWord I.calldata 4) _ ≠ _
      rw [ugt_one (by rw [hmaxNat]; omega)]; decide) (by jump_dest) h₁
    exact Or.inl (safeRuntime_block_3913 (by simp; omega) h₂)
  have h₂ := safeRuntime_block_2993_fallthrough (by simp; omega) (by
    rw [hmax]
    change UInt256.gt (calldataWord I.calldata 4) _ = _
    exact ugt_zero (by rwa [hmaxNat])) h₁
  change RD fork safeBytecode I g s0 ⟨3010⟩ (calldataWord I.calldata 4 :: ⟨0⟩ :: R)
    mem aw rdata σ _ _ at h₂
  have hoff (a : Nat) (hb : (calldataWord I.calldata 4).toNat + a < UInt256.size) :
      calldataWord I.calldata 4 + UInt256.ofNat a =
        UInt256.ofNat ((calldataWord I.calldata 4).toNat + a) := by
    conv_lhs => lhs; rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    exact wordOfNatAdd _ _ hb
  have hheadFail (hc : UInt256.slt
      (UInt256.ofNat ((calldataWord I.calldata 4).toNat + 35))
      (UInt256.ofNat I.calldata.size) = ⟨0⟩) : RDrev fork safeBytecode g s0 := by
    have h₃ := safeRuntime_block_3010_taken (by simp; omega) (by
      rw [hoff 35 (by omega), hc]; decide) (by jump_dest) h₂
    exact safeRuntime_block_3913 (by omega) h₃
  by_cases hs : I.calldata.size < 2 ^ 255
  swap
  · exact Or.inl (hheadFail (slt_zero_low_high (by
      rw [ulit_toNat' _ (by omega)]; omega) (by rw [ulit_toNat' _ hsize]; omega)))
  by_cases hhead : setupOwnersStart I.calldata ≤ I.calldata.size
  swap
  · exact Or.inl (hheadFail (slt_ofNat_lit_zero hs
      (by dsimp only [setupOwnersStart] at hhead; omega) (by omega)))
  have h₃ := safeRuntime_block_3010_fallthrough (by simp; omega) (by
    rw [hoff 35 (by omega), slt_ofNat_lit_one_low hs (by
      dsimp only [setupOwnersStart] at hhead; omega)]; rfl) h₂
  have ho4 : ((UInt256.ofNat 4) + calldataWord I.calldata 4).toNat =
      4 + (calldataWord I.calldata 4).toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change 4 + _ < 2 ^ 256; omega)
  let n := (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
  have hw : calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) =
      UInt256.ofNat n := (u256_ofNat_toNat _).symm
  by_cases hn : n ≤ 2 ^ 64 - 1
  swap
  · have h₄ := safeRuntime_block_3021_taken (by simp; omega) (by
      rw [hmax]
      change UInt256.gt (calldataWord I.calldata _) _ ≠ _
      rw [ho4, ugt_one (by rw [hmaxNat]; change 2 ^ 64 - 1 < n; omega)]
      decide) (by jump_dest) h₃
    exact Or.inl (safeRuntime_block_973 (by simp; omega) h₄)
  by_cases hin : setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size
  · obtain ⟨k', C', hr⟩ := safeSetupDecodeOwnersValid h hh hs ho hw hn hin (by simp; omega)
    exact Or.inr ⟨n, k', C', hh, hs, ho, hw, hn, hin, hr⟩
  have h₄ := safeRuntime_block_3021_fallthrough (by simp; omega) (by
    rw [hmax]
    change UInt256.gt (calldataWord I.calldata _) _ = _
    rw [ho4]
    exact ugt_zero (by rw [hmaxNat]; exact hn)) h₃
  change RD fork safeBytecode I g s0 ⟨3041⟩
    (calldataWord I.calldata 4 :: calldataWord I.calldata _ :: ⟨0⟩ :: R)
    mem aw rdata σ _ _ at h₄
  rw [ho4, hw] at h₄
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
  have hend : (UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) +
      calldataWord I.calldata 4) + UInt256.ofNat 36 =
      UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) := by
    rw [hshift, u256_add_comm (UInt256.ofNat (32 * n)), hoff (32 * n) (by omega),
      wordOfNatAdd _ 36 (by omega)]
    apply congrArg UInt256.ofNat
    dsimp only [setupOwnersStart]
    omega
  have h₅ := safeRuntime_block_3041_taken (by simp; omega) (by
    rw [hend, ugt_one (by
      rw [ulit_toNat' _ hsize, ulit_toNat' _ (by
        dsimp only [setupOwnersStart]; omega)]
      omega)]; decide) (by jump_dest) h₄
  exact Or.inl (safeRuntime_block_3909 (by omega) h₅)

end Benchmarks.Safe.ViaIR
