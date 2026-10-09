import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines
import Benchmarks.Morpho.MorphoBlue.AssetsDownSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {a t s ret : UInt256} {R : List UInt256}

theorem morphoAssetsDownReachShares (hstack : R.length + 12 ≤ 1024)
    (hs : t.toNat + 1 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15386)
      (a :: s :: (t + UInt256.ofNat 1) :: ret :: R) mem aw rdata σ k' C' := by
  have hc := checkedAddNoOverflowGt t (UInt256.ofNat 1) hs
  rw [u256_add_comm (UInt256.ofNat 1) t] at hc
  exact ⟨_, _, morphoBlocks.morpho_block_15373_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc h⟩

theorem morphoAssetsDownReachMul (hstack : R.length + 12 ≤ 1024)
    (ht : s.toNat + virtualShares.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15386)
      (a :: s :: (t + UInt256.ofNat 1) :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      (a :: (t + UInt256.ofNat 1) :: UInt256.ofNat 2004 :: (s + virtualShares) ::
        UInt256.ofNat 14109 :: ret :: R) mem aw rdata σ k' C' := by
  have hc := checkedAddNoOverflowGt s virtualShares ht
  rw [u256_add_comm virtualShares s] at hc
  have rd1 := morphoBlocks.morpho_block_15386_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc h
  exact ⟨_, _, morphoBlocks.morpho_block_15399 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoAssetsDownOk (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hfit : AssetsDownFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (assetsDownWord a t s :: R) mem aw rdata σ k' C' := by
  obtain ⟨hs, ht, hp⟩ := hfit
  obtain ⟨k1, C1, rd1⟩ := morphoAssetsDownReachShares (v := v) hstack hs h
  obtain ⟨k2, C2, rd2⟩ := morphoAssetsDownReachMul (v := v) hstack ht rd1
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedMulOk (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hp rd2
  have rd4 := morphoBlocks.morpho_block_2004 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  obtain ⟨k5, C5, rd5⟩ := morphoCheckedDivOk (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (u256_add_ne_zero_of_right_ne_zero (by decide) ht) rd4
  exact ⟨_, _, morphoBlocks.morpho_block_14109 (immWords := wordsOf (immStore v)) (by omega) hvalid rd5⟩

theorem morphoAssetsDownReverts (hstack : R.length + 12 ≤ 1024) (hbad : ¬ AssetsDownFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hs : t.toNat + 1 < UInt256.size
  · obtain ⟨k1, C1, rd1⟩ := morphoAssetsDownReachShares (v := v) hstack hs h
    by_cases ht : s.toNat + virtualShares.toNat < UInt256.size
    · obtain ⟨k2, C2, rd2⟩ := morphoAssetsDownReachMul (v := v) hstack ht rd1
      have hp : UInt256.size ≤ a.toNat * (t + UInt256.ofNat 1).toNat :=
        Nat.le_of_not_gt (fun hp ↦ hbad ⟨hs, ht, hp⟩)
      exact morphoCheckedMulReverts (v := v) (by simp only [List.length_cons]; omega) hp rd2
    · have hc := checkedAddOverflowGt s virtualShares (Nat.le_of_not_gt ht)
      rw [u256_add_comm virtualShares s] at hc
      have rd2 := morphoBlocks.morpho_block_15386_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by change UInt256.gt s (s + virtualShares) ≠ _; rw [hc]; decide)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
        (by simp only [morphoBlocks.morpho_block_15386_taken_stack, List.length_cons]; omega) rd2
  · have hc := checkedAddOverflowGt t (UInt256.ofNat 1) (Nat.le_of_not_gt hs)
    rw [u256_add_comm (UInt256.ofNat 1) t] at hc
    have rd1 := morphoBlocks.morpho_block_15373_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by change UInt256.gt t (t + UInt256.ofNat 1) ≠ _; rw [hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by simp only [morphoBlocks.morpho_block_15373_taken_stack, List.length_cons]; omega) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
