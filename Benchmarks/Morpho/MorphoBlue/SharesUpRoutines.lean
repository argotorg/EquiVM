import Benchmarks.Morpho.MorphoBlue.SharesUpSource
import Benchmarks.Morpho.MorphoBlue.MulDivUpRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {a t s ret : UInt256} {R : List UInt256}

theorem morphoSharesUpReachAssets (hstack : R.length + 14 ≤ 1024)
    (ht : s.toNat + virtualShares.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411) (a :: t :: s :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15426)
      ((s + virtualShares) :: t :: a :: ret :: R) mem aw out σ k' C' := by
  have hc := checkedAddNoOverflowGt s virtualShares ht
  rw [u256_add_comm virtualShares s] at hc
  exact ⟨_, _, morphoBlocks.morpho_block_15411_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) hc h⟩

theorem morphoSharesUpReachMul (hstack : R.length + 14 ≤ 1024)
    (hs : t.toNat + 1 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15426)
      ((s + virtualShares) :: t :: a :: ret :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14424)
      (a :: (s + virtualShares) :: (t + UInt256.ofNat 1) :: UInt256.ofNat 14109 :: ret :: R)
      mem aw out σ k' C' := by
  have hc := checkedAddNoOverflowGt t (UInt256.ofNat 1) hs
  rw [u256_add_comm (UInt256.ofNat 1) t] at hc
  have rd1 := morphoBlocks.morpho_block_15426_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) hc h
  exact ⟨_, _, morphoBlocks.morpho_block_15437 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoSharesUpOk (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hf : SharesUpFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411) (a :: t :: s :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (sharesUpWord a t s :: R) mem aw out σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoSharesUpReachAssets (v := v) hstack hf.1 h
  obtain ⟨k2, C2, rd2⟩ := morphoSharesUpReachMul (v := v) hstack hf.2.1 rd1
  obtain ⟨k3, C3, rd3⟩ := morphoMulDivUpOk (v := v) (by simp; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf.2.2 rd2
  exact ⟨_, _, morphoBlocks.morpho_block_14109 (immWords := wordsOf (immStore v)) (by simp; omega) hvalid rd3⟩

theorem morphoSharesUpReverts (hstack : R.length + 14 ≤ 1024) (hf : ¬ SharesUpFits a t s)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411) (a :: t :: s :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases ht : s.toNat + virtualShares.toNat < UInt256.size
  swap
  · have hc := checkedAddOverflowGt s virtualShares (Nat.le_of_not_gt ht)
    rw [u256_add_comm virtualShares s] at hc
    have rd1 := morphoBlocks.morpho_block_15411_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (by change UInt256.gt s (s + virtualShares) ≠ _; rw [hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega) rd1
  obtain ⟨k1, C1, rd1⟩ := morphoSharesUpReachAssets (v := v) hstack ht h
  by_cases hs : t.toNat + 1 < UInt256.size
  swap
  · have hc := checkedAddOverflowGt t (UInt256.ofNat 1) (Nat.le_of_not_gt hs)
    rw [u256_add_comm (UInt256.ofNat 1) t] at hc
    have rd2 := morphoBlocks.morpho_block_15426_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (by change UInt256.gt t (t + UInt256.ofNat 1) ≠ _; rw [hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega) rd2
  obtain ⟨k2, C2, rd2⟩ := morphoSharesUpReachMul (v := v) hstack hs rd1
  exact morphoMulDivUpReverts (v := v) (by simp; omega) (fun hp ↦ hf ⟨ht, hs, hp⟩) rd2

end Routines
end Benchmarks.Morpho.MorphoBlue
