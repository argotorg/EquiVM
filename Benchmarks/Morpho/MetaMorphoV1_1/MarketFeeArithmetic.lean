import Benchmarks.Morpho.MetaMorphoV1_1.MarketFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_078

/-! Fee amount, subtraction, and rounded-down share conversion in the deployed runtime. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketFeeArithmeticRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest fee sa ss sharesPtr assetsPtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128) (hf : fee.toNat < 2 ^ 128)
    (ha : sa.toNat < 2 ^ 128) (hs : ss.toNat < 2 ^ 128)
    (hla : memLoad assetsPtr mem = sa) (hls : memLoad sharesPtr mem = ss)
    (rd : RD (deployedRuntime v) I g s0 ⟨17400⟩
      (interest :: fee :: sharesPtr :: assetsPtr :: R) mem aw rdata σ k C) :
    (¬ ((wadMulWord interest fee).toNat ≤ sa.toNat ∧
        sharesDownFits (wadMulWord interest fee) ss) ∧ RDrev (deployedRuntime v) g s0) ∨
    ((wadMulWord interest fee).toNat ≤ sa.toNat ∧
      sharesDownFits (wadMulWord interest fee) ss ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨19367⟩
        (marketFeeShares interest fee sa ss :: ⟨17353⟩ :: ⟨17513⟩ :: uint128Mask ::
          sharesPtr :: assetsPtr :: R) mem aw' rdata σ k' C') := by
  have h0 := metaMorphoV1_1_block_17400 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k1, C1, h1⟩ := checkedMulReturn v
    (by simp only [List.length_cons]; omega) (uint128ProductFits hi hf)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  have h2 := metaMorphoV1_1_block_17418 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have hmaskA := u256LandMaskCleanOfToNat sa uint128Mask (by decide +kernel) ha
  have hmaskS := u256LandMaskCleanOfToNat ss uint128Mask (by decide +kernel) hs
  dsimp only [uint128Mask] at hmaskA hmaskS
  simp only [metaMorphoV1_1_block_17418_stack, hla, hmaskA] at h2
  by_cases hle : (wadMulWord interest fee).toNat ≤ sa.toNat
  · obtain ⟨k3, C3, h3⟩ := checkedSubReturn v
      (by simp only [List.length_cons]; omega) hle
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    have hshares : ss.toNat + (UInt256.ofNat 1000000).toNat < UInt256.size := by
      change ss.toNat + 1000000 < 2 ^ 256
      omega
    have hdelta : (UInt256.sub sa (wadMulWord interest fee)).toNat < 2 ^ 128 := by
      rw [usub_toNat hle]
      omega
    have h4 := metaMorphoV1_1_block_17439_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hls, hmaskS]
          simpa only [u256_add_comm (UInt256.ofNat 1000000) ss] using
            checkedAddNoOverflowGt ss (UInt256.ofNat 1000000) hshares) h3
    simp only [metaMorphoV1_1_block_17439_fallthrough_stack, hls, hmaskS] at h4
    have hdeltaAdd := checkedAddNoOverflowGt (UInt256.sub sa (wadMulWord interest fee))
      (UInt256.ofNat 1) (by
        change (UInt256.sub sa (wadMulWord interest fee)).toNat + 1 < 2 ^ 256
        omega)
    rw [u256_add_comm (UInt256.ofNat 1) (UInt256.sub sa (wadMulWord interest fee))] at hdeltaAdd
    have h5 := metaMorphoV1_1_block_17465_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hdeltaAdd h4
    have h6 := metaMorphoV1_1_block_17476 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
    by_cases hp : sharesDownFits (wadMulWord interest fee) ss
    · obtain ⟨k7, C7, h7⟩ := checkedMulReturn v
        (by simp only [List.length_cons]; omega) hp
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h6
      have h8 := metaMorphoV1_1_block_17503 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h7
      obtain ⟨k9, C9, h9⟩ := checkedDivReturn v
        (by simp only [List.length_cons]; omega) (sharesDownDenominatorNonzero hdelta)
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h8
      have h10 := metaMorphoV1_1_block_17508 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h9
      exact .inr ⟨hle, hp, _, _, _, h10⟩
    · exact .inl ⟨fun h ↦ hp h.2, checkedMulRevert v
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hp) h6⟩
  · exact .inl ⟨fun h ↦ hle h.1, checkedSubRevert v
      (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hle) h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
