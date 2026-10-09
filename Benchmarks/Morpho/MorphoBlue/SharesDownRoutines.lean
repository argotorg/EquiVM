import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines
import Benchmarks.Morpho.MorphoBlue.SharesMathCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {a t s ret : UInt256} {R : List UInt256}

theorem morphoSharesDownReachAssets (hstack : R.length + 12 ≤ 1024)
    (hs : s.toNat + virtualShares.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15350)
      (a :: t :: (s + virtualShares) :: ret :: R) mem aw rdata σ k' C' := by
  have hc := checkedAddNoOverflowGt s virtualShares hs
  rw [u256_add_comm virtualShares s] at hc
  exact ⟨_, _, morphoBlocks.morpho_block_15336_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc h⟩

theorem morphoSharesDownReachMul (hstack : R.length + 12 ≤ 1024)
    (ht : t.toNat + 1 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15350)
      (a :: t :: (s + virtualShares) :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      (a :: (s + virtualShares) :: UInt256.ofNat 2004 :: (t + UInt256.ofNat 1) ::
        UInt256.ofNat 14109 :: ret :: R) mem aw rdata σ k' C' := by
  have hc := checkedAddNoOverflowGt t (UInt256.ofNat 1) ht
  rw [u256_add_comm (UInt256.ofNat 1) t] at hc
  have rd1 := morphoBlocks.morpho_block_15350_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc h
  exact ⟨_, _, morphoBlocks.morpho_block_15361 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoSharesDownOk (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hfit : SharesDownFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (sharesDownWord a t s :: R) mem aw rdata σ k' C' := by
  obtain ⟨hs, ht, hp⟩ := hfit
  obtain ⟨k1, C1, rd1⟩ := morphoSharesDownReachAssets (v := v) hstack hs h
  obtain ⟨k2, C2, rd2⟩ := morphoSharesDownReachMul (v := v) hstack ht rd1
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedMulOk (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hp rd2
  have rd4 := morphoBlocks.morpho_block_2004 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  obtain ⟨k5, C5, rd5⟩ := morphoCheckedDivOk (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (sharesDownDenom_nonzero t ht) rd4
  exact ⟨_, _, morphoBlocks.morpho_block_14109 (immWords := wordsOf (immStore v)) (by omega) hvalid rd5⟩

theorem morphoSharesDownReverts (hstack : R.length + 12 ≤ 1024) (hbad : ¬ SharesDownFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336) (a :: t :: s :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hs : s.toNat + virtualShares.toNat < UInt256.size
  · obtain ⟨k1, C1, rd1⟩ := morphoSharesDownReachAssets (v := v) hstack hs h
    by_cases ht : t.toNat + 1 < UInt256.size
    · obtain ⟨k2, C2, rd2⟩ := morphoSharesDownReachMul (v := v) hstack ht rd1
      have hp : UInt256.size ≤ a.toNat * (s + virtualShares).toNat :=
        Nat.le_of_not_gt (fun hp ↦ hbad ⟨hs, ht, hp⟩)
      exact morphoCheckedMulReverts (v := v) (by simp only [List.length_cons]; omega) hp rd2
    · have hc := checkedAddOverflowGt t (UInt256.ofNat 1) (Nat.le_of_not_gt ht)
      rw [u256_add_comm (UInt256.ofNat 1) t] at hc
      have rd2 := morphoBlocks.morpho_block_15350_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hc]; decide)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
        (by simp only [morphoBlocks.morpho_block_15350_taken_stack, List.length_cons]; omega) rd2
  · have hc := checkedAddOverflowGt s virtualShares (Nat.le_of_not_gt hs)
    rw [u256_add_comm virtualShares s] at hc
    have rd1 := morphoBlocks.morpho_block_15336_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by change UInt256.gt s (s + virtualShares) ≠ _; rw [hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by simp only [morphoBlocks.morpho_block_15336_taken_stack, List.length_cons]; omega) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
