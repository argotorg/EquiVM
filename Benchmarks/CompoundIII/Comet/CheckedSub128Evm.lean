import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.PackedGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedSub128 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^128) (hy : y.toNat < 2^128)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨15305⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    (y.toNat ≤ x.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
        mem aw rdata σ k' C') ∨
    (¬ y.toNat ≤ x.toNat ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hle : y.toNat ≤ x.toNat
  · have r1 := cometWithExtendedAssetList_block_15305_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask128Clean x hx, mask128Clean y hy]; exact ult_zero hle) h
    simp only [cometWithExtendedAssetList_block_15305_fallthrough_stack,
      mask128Clean x hx, mask128Clean y hy] at r1
    have r2 := cometWithExtendedAssetList_block_15326 (immWords := wordsOf (immStore v))
      (by omega) hvalid r1
    exact Or.inl ⟨hle, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_15305_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask128Clean x hx, mask128Clean y hy, ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7775 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hle, cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
