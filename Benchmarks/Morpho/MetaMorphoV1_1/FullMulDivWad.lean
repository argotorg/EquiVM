import Benchmarks.Morpho.MetaMorphoV1_1.FullMulDivRoutines

/-! The compiler's specialized full-precision division by 10^18. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem fullDivTwos_wad : fullDivTwos ⟨1000000000000000000⟩ = UInt256.ofNat (2 ^ 18) := by
  decide +kernel

theorem fullDivTwosComplement_wad :
    fullDivTwosComplement ⟨1000000000000000000⟩ = UInt256.ofNat (2 ^ 238) := by decide +kernel

theorem fullDivInverse_wad :
    fullDivInverse (UInt256.div ⟨1000000000000000000⟩
      (fullDivTwos ⟨1000000000000000000⟩)) 6 =
      UInt256.ofNat
        78156646155174841979727994598816262306175212592076161876661508869554232690281 := by
  decide +kernel

theorem wordShiftLeft_power (w : UInt256) (k : Nat) (hk : k < 256) :
    UInt256.shiftLeft w (UInt256.ofNat k) = UInt256.mul w (UInt256.ofNat (2 ^ k)) := by
  have hfit : k < UInt256.size := lt_trans hk (by decide)
  have hp : 2 ^ k < UInt256.size := Nat.pow_lt_pow_right (by decide) hk
  apply u256_inj
  rw [u256_mul_toNat, UInt256.toNat_ofNat_of_lt hp]
  unfold UInt256.shiftLeft
  have hguard : ¬ (UInt256.ofNat k).val ≥ 256 := by
    change ¬ (UInt256.ofNat k).toNat ≥ 256
    rw [UInt256.toNat_ofNat_of_lt hfit]
    omega
  rw [if_neg hguard]
  change (w.toNat <<< (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [UInt256.toNat_ofNat_of_lt hfit, Nat.shiftLeft_eq]

theorem fullMulDivWadCalculated (a b : UInt256) :
    UInt256.mul
      (UInt256.lor (UInt256.shiftRight (fullProductLowAdjusted a b ⟨1000000000000000000⟩) ⟨18⟩)
        (UInt256.shiftLeft (fullProductHighAdjusted a b ⟨1000000000000000000⟩) ⟨238⟩))
      (UInt256.ofNat
        78156646155174841979727994598816262306175212592076161876661508869554232690281) =
        fullMulDivWord a b ⟨1000000000000000000⟩ := by
  have hright (w : UInt256) : UInt256.shiftRight w ⟨18⟩ =
      UInt256.div w (UInt256.ofNat (2 ^ 18)) := by
    apply u256_inj
    have hs : (UInt256.shiftRight w ⟨18⟩).toNat = w.toNat / 2 ^ 18 :=
      wordShiftRight_toNat w 18 (by decide)
    rw [hs, udiv_toNat]
    rfl
  have hleft (w : UInt256) : UInt256.shiftLeft w ⟨238⟩ =
      UInt256.mul w (UInt256.ofNat (2 ^ 238)) := wordShiftLeft_power w 238 (by decide)
  have h := fullMulDivCalculated_correct a b ⟨1000000000000000000⟩ (by decide)
  rw [fullMulDivCalculated, fullDivNumerator, fullDivInverse_wad,
    fullDivTwos_wad, fullDivTwosComplement_wad] at h
  rw [hright, hleft]
  exact h

theorem fullMulDivWadReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hfit : fullMulDivFits a b ⟨1000000000000000000⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16398⟩ ([a, b, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (fullMulDivWord a b ⟨1000000000000000000⟩ :: R) mem aw' rdata σ k' C' := by
  by_cases hp : a.toNat * b.toNat < UInt256.size
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16398_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by change fullProductGuard a b ≠ ⟨0⟩; rw [fullProductGuard_small hp]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16525_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) hret h1
    change RD _ _ _ _ _ (UInt256.div (UInt256.mul a b) ⟨1000000000000000000⟩ :: R)
      _ _ _ _ _ _ at h2
    rw [fullMulDiv_small hp] at h2
    exact ⟨aw2, k2, C2, h2⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16398_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (fullProductGuard_large (Nat.le_of_not_gt hp)) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16429_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by
        change UInt256.isZero (UInt256.gt ⟨1000000000000000000⟩ (fullProductHigh a b)) = ⟨0⟩
        rw [ugt_one ((fullMulDivFits_iff a b _).mp hfit)]; rfl) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_16445_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) hret h2
    change RD _ _ _ _ _
      (UInt256.mul
        (UInt256.lor (UInt256.shiftRight (fullProductLowAdjusted a b ⟨1000000000000000000⟩) ⟨18⟩)
          (UInt256.shiftLeft (fullProductHighAdjusted a b ⟨1000000000000000000⟩) ⟨238⟩))
        (UInt256.ofNat
          78156646155174841979727994598816262306175212592076161876661508869554232690281) :: R)
      _ _ _ _ _ _ at h3
    rw [fullMulDivWadCalculated] at h3
    exact ⟨aw3, k3, C3, h3⟩

theorem fullMulDivWadRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hbad : ¬ fullMulDivFits a b ⟨1000000000000000000⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨16398⟩ ([a, b, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hp : UInt256.size ≤ a.toNat * b.toNat := Nat.le_of_not_gt
    (fun h ↦ hbad ⟨by decide, lt_of_le_of_lt (Nat.div_le_self _ _) h⟩)
  have hle : (⟨1000000000000000000⟩ : UInt256).toNat ≤ (fullProductHigh a b).toNat :=
    Nat.le_of_not_gt (fun h ↦ hbad ((fullMulDivFits_iff a b _).mpr h))
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16398_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (fullProductGuard_large hp) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16429_taken_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by
      change UInt256.isZero (UInt256.gt ⟨1000000000000000000⟩ (fullProductHigh a b)) ≠ ⟨0⟩
      rw [ugt_zero hle]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_16510 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
