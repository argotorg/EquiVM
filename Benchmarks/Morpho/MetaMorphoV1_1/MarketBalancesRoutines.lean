import Benchmarks.Morpho.MetaMorphoV1_1.MarketDecodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic

/-! Elapsed time and the conditional accrual branch in the market-balance routine. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketElapsedRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {params market unused : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hc : (calldataWord out 128).toNat < 2 ^ 128)
    (hread : memLoad (market + ⟨128⟩) mem = calldataWord out 128)
    (rd : RD (deployedRuntime v) I g s0 ⟨16966⟩ (unused :: params :: market :: R)
      mem aw out σ k C) :
    ((UInt256.ofNat I.header.timestamp).toNat < (calldataWord out 128).toNat ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((calldataWord out 128).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16991⟩
        (UInt256.sub (UInt256.ofNat I.header.timestamp) (calldataWord out 128) ::
          (market + ⟨128⟩) :: params :: market :: R) mem aw' out σ k' C') := by
  have hclean : UInt256.land (calldataWord out 128) uint128Mask = calldataWord out 128 :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16966_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨12234⟩
    (UInt256.ofNat I.header.timestamp ::
      UInt256.land (memLoad (market + ⟨128⟩) mem) uint128Mask :: ⟨16991⟩ ::
      (market + ⟨128⟩) :: params :: market :: R) mem aw1 out σ k1 C1 at h1
  rw [hread, hclean] at h1
  by_cases hle : (calldataWord out 128).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat
  · obtain ⟨k2, C2, h2⟩ := checkedSubReturn v (by simp only [List.length_cons]; omega) hle
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    exact .inr ⟨hle, aw1, k2, C2, h2⟩
  · exact .inl ⟨Nat.lt_of_not_ge hle, checkedSubRevert v
      (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hle) h1⟩

-- LIBRARY CANDIDATE: the compiler's double-ISZERO normalization of a word to a boolean.
theorem doubleIsZero_word (word : UInt256) :
    UInt256.isZero (UInt256.isZero word) = if word ≠ ⟨0⟩ then ⟨1⟩ else ⟨0⟩ := by
  by_cases h : word = ⟨0⟩
  · subst word; decide +kernel
  · rw [isZero_eq_zero_of_ne h, if_pos h]
    rfl

set_option maxRecDepth 2000 in
theorem marketAccrualFirstTest {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {params market last elapsed borrow : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hc : borrow.toNat < 2 ^ 128)
    (hborrow : memLoad (market + ⟨64⟩) mem = borrow)
    (rd : RD (deployedRuntime v) I g s0 ⟨16991⟩ (elapsed :: last :: params :: market :: R)
      mem aw out σ k C) :
    ∃ aw1 k1 C1, RD (deployedRuntime v) I g s0 ⟨17001⟩
      ((if elapsed ≠ ⟨0⟩ ∧ borrow ≠ ⟨0⟩ then ⟨1⟩ else ⟨0⟩) ::
        params :: last :: elapsed :: market :: R) mem aw1 out σ k1 C1 := by
  have hclean : UInt256.land borrow uint128Mask = borrow :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc
  by_cases he : elapsed ≠ ⟨0⟩
  · have h1 := metaMorphoV1_1_block_16991_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [doubleIsZero_word, if_pos he]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17600_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    simp only [metaMorphoV1_1_block_17600_stack] at h2
    change RD (deployedRuntime v) I g s0 ⟨17001⟩
      (UInt256.isZero (UInt256.isZero
        (UInt256.land (memLoad (market + UInt256.ofNat 64) mem) uint128Mask)) ::
        params :: last :: elapsed :: market :: R) mem aw2 out σ k2 C2 at h2
    refine ⟨aw2, k2, C2, ?_⟩
    rw [show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl,
      hborrow, hclean, doubleIsZero_word] at h2
    by_cases hb : borrow ≠ ⟨0⟩
    · have hpair : elapsed ≠ ⟨0⟩ ∧ borrow ≠ ⟨0⟩ := ⟨he, hb⟩
      simpa only [if_pos hb, if_pos hpair] using h2
    · have hpair : ¬ (elapsed ≠ ⟨0⟩ ∧ borrow ≠ ⟨0⟩) := fun h ↦ hb h.2
      simpa only [if_neg hb, if_neg hpair] using h2
  · have h1 := metaMorphoV1_1_block_16991_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [doubleIsZero_word, if_neg he]; rfl) rd
    have hpair : ¬ (elapsed ≠ ⟨0⟩ ∧ borrow ≠ ⟨0⟩) := fun h ↦ he h.1
    refine ⟨aw, k + 8, C + 29, ?_⟩
    simpa only [metaMorphoV1_1_block_16991_fallthrough_stack, doubleIsZero_word,
      if_neg he, if_neg hpair] using h1

set_option maxRecDepth 2000 in
theorem marketAccrualBranch {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {params market last elapsed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 8 ≤ 1024)
    (hc : (calldataWord out 64).toNat < 2 ^ 128)
    (hborrow : memLoad (market + ⟨64⟩) mem = calldataWord out 64)
    (hirm : memLoad (params + ⟨96⟩) mem = UInt256.ofNat p.irm.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨16991⟩ (elapsed :: last :: params :: market :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if marketAccrues p elapsed out then ⟨17069⟩ else ⟨17012⟩)
      (params :: last :: elapsed :: market :: R) mem aw' out σ k' C' := by
  have hfirst := marketAccrualFirstTest v (by omega) hc hborrow rd
  obtain ⟨aw1, k1, C1, h1⟩ := hfirst
  have hguard : ∃ aw2 k2 C2, RD (deployedRuntime v) I g s0 ⟨17007⟩
      ((if marketAccrues p elapsed out then ⟨1⟩ else ⟨0⟩) ::
        params :: last :: elapsed :: market :: R) mem aw2 out σ k2 C2 := by
    by_cases hp : elapsed ≠ ⟨0⟩ ∧ calldataWord out 64 ≠ ⟨0⟩
    · have h2 := metaMorphoV1_1_block_17001_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [if_pos hp]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17578_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      have hirmlt : (UInt256.ofNat p.irm.toNat).toNat < EVM.addressModulus := by
        rw [UInt256.toNat_ofNat_of_lt
          (show p.irm.toNat < UInt256.size from lt_trans p.irm.isLt (by decide))]
        exact p.irm.isLt
      have hz := accountAddress_ofNat_zero_iff hirmlt
      rw [show AccountAddress.ofNat (UInt256.ofNat p.irm.toNat).toNat = p.irm from
        accountAddress_of_word_val p.irm] at hz
      simp only [metaMorphoV1_1_block_17578_stack] at h3
      change RD (deployedRuntime v) I g s0 ⟨17007⟩
        (UInt256.isZero (UInt256.isZero
          (UInt256.land solcAddrMask (memLoad (params + UInt256.ofNat 96) mem))) ::
          params :: last :: elapsed :: market :: R) mem aw3 out σ k3 C3 at h3
      refine ⟨aw3, k3, C3, ?_⟩
      rw [show UInt256.ofNat 96 = (⟨96⟩ : UInt256) from rfl,
        hirm, solcAddrMask_clean_left hirmlt, doubleIsZero_word] at h3
      by_cases hi : p.irm ≠ AccountAddress.ofNat 0
      · have hw : UInt256.ofNat p.irm.toNat ≠ ⟨0⟩ := fun h ↦ hi (hz.mpr h)
        have hyes : marketAccrues p elapsed out := ⟨hp.1, hp.2, hi⟩
        simpa only [if_pos hw, if_pos hyes] using h3
      · have hw : ¬ UInt256.ofNat p.irm.toNat ≠ ⟨0⟩ := fun h ↦
          h (hz.mp (Classical.not_not.mp hi))
        have hno : ¬ marketAccrues p elapsed out := fun h ↦ hi h.2.2
        simpa only [if_neg hw, if_neg hno] using h3
    · have h2 := metaMorphoV1_1_block_17001_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [if_neg hp]; rfl) h1
      have hno : ¬ marketAccrues p elapsed out := fun h ↦ hp ⟨h.1, h.2.1⟩
      refine ⟨aw1, k1 + 4, C1 + 17, ?_⟩
      simpa only [if_neg hp, if_neg hno] using h2
  obtain ⟨aw2, k2, C2, h2⟩ := hguard
  by_cases hyes : marketAccrues p elapsed out
  · have h3 := metaMorphoV1_1_block_17007_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [if_pos hyes]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact ⟨_, _, _, by simpa only [if_pos hyes] using h3⟩
  · have h3 := metaMorphoV1_1_block_17007_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [if_neg hyes]; rfl) h2
    exact ⟨_, _, _, by simpa only [if_neg hyes] using h3⟩

theorem marketBalancesReturnRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {params market last elapsed ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hc : MarketChecks out)
    (hread : ∀ i, i < 4 → memLoad (market + UInt256.ofNat (32 * i)) mem =
      calldataWord out (32 * i))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17012⟩
      (params :: last :: elapsed :: market :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (calldataWord out 96 :: calldataWord out 64 :: calldataWord out 32 ::
        calldataWord out 0 :: R) mem aw' out σ k' C' := by
  have h0 : memLoad market mem = calldataWord out 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
      using hread 0 (by decide)
  have h1 : memLoad (market + UInt256.ofNat 32) mem = calldataWord out 32 := hread 1 (by decide)
  have h2 : memLoad (market + UInt256.ofNat 64) mem = calldataWord out 64 := hread 2 (by decide)
  have h3 : memLoad (market + UInt256.ofNat 96) mem = calldataWord out 96 := hread 3 (by decide)
  have hclean (n : Nat) (hc : (calldataWord out n).toNat < 2 ^ 128) :
      UInt256.land (calldataWord out n)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1)) = calldataWord out n :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1_block_17012_packed
    (immWords := wordsOf (immStore v)) hstack hret rd
  simp only [metaMorphoV1_1_block_17012_stack, h0, h1, h2, h3] at hdone
  rw [hclean 0 hc.2.1, hclean 32 hc.2.2.1, hclean 64 hc.2.2.2.1,
    hclean 96 hc.2.2.2.2.1] at hdone
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
