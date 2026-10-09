import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem mask104Clean (w : UInt256) (hw : w.toNat < 2^104) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
      (UInt256.ofNat 1)) w = w := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat w _ rfl hw

theorem cometCheckedSub104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^104) (hy : y.toNat < 2^104)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12353⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    (y.toNat ≤ x.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
      mem aw rdata σ k' C') ∨ (¬ y.toNat ≤ x.toNat ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hle : y.toNat ≤ x.toNat
  · have r1 := cometWithExtendedAssetList_block_12353_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask104Clean x hx, mask104Clean y hy]; exact ult_zero hle) h
    simp only [cometWithExtendedAssetList_block_12353_fallthrough_stack,
      mask104Clean x hx, mask104Clean y hy] at r1
    exact Or.inl ⟨hle, _, _, cometWithExtendedAssetList_block_12374
      (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  · have r1 := cometWithExtendedAssetList_block_12353_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask104Clean x hx, mask104Clean y hy, ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7775
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hle, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r2⟩

theorem cometCheckedAdd104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^104) (hy : y.toNat < 2^104)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12293⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    (x.toNat + y.toNat < 2^104 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((x + y) :: R)
      mem aw rdata σ k' C') ∨
    (¬ x.toNat + y.toNat < 2^104 ∧ RDrev (deployedRuntime v) g s0) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hs : (UInt256.sub mask y).toNat = 2^104 - 1 - y.toNat := by
    apply usub_toNat
    change y.toNat ≤ 2^104 - 1; omega
  by_cases hf : x.toNat + y.toNat < 2^104
  · have hg : UInt256.gt x (UInt256.sub mask y) = UInt256.ofNat 0 :=
      ugt_zero (by rw [hs]; omega)
    have r1 := cometWithExtendedAssetList_block_12293_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask104Clean x hx, mask104Clean y hy]; exact hg) h
    simp only [cometWithExtendedAssetList_block_12293_fallthrough_stack,
      mask104Clean x hx, mask104Clean y hy] at r1
    exact Or.inl ⟨hf, _, _, cometWithExtendedAssetList_block_12319
      (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  · have hg : UInt256.gt x (UInt256.sub mask y) = UInt256.ofNat 1 :=
      ugt_one (by rw [hs]; omega)
    have r1 := cometWithExtendedAssetList_block_12293_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask104Clean x hx, mask104Clean y hy]; change UInt256.gt x (UInt256.sub mask y) ≠ _
          rw [hg]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7859
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hf, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
