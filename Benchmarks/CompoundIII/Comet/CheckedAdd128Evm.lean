import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.PackedGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedAdd128 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^128) (hy : y.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨13689⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    (x.toNat + y.toNat < 2^128 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((x + y) :: R)
      mem aw rdata σ k' C') ∨
    (¬ x.toNat + y.toNat < 2^128 ∧ RDrev (deployedRuntime v) g s0) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
    (UInt256.ofNat 1)
  have hs : (UInt256.sub mask y).toNat = 2^128 - 1 - y.toNat := by
    apply usub_toNat
    change y.toNat ≤ 2^128 - 1; omega
  by_cases hf : x.toNat + y.toNat < 2^128
  · have hg : UInt256.gt x (UInt256.sub mask y) = UInt256.ofNat 0 :=
      ugt_zero (by rw [hs]; omega)
    have r1 := cometWithExtendedAssetList_block_13689_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask128Clean x hx, mask128Clean y hy]; exact hg) h
    simp only [cometWithExtendedAssetList_block_13689_fallthrough_stack,
      mask128Clean x hx, mask128Clean y hy] at r1
    exact Or.inl ⟨hf, _, _, cometWithExtendedAssetList_block_13715
      (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  · have hg : UInt256.gt x (UInt256.sub mask y) = UInt256.ofNat 1 :=
      ugt_one (by rw [hs]; omega)
    have r1 := cometWithExtendedAssetList_block_13689_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask128Clean x hx, mask128Clean y hy]; change UInt256.gt x (UInt256.sub mask y) ≠ _
          rw [hg]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7859
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hf, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
