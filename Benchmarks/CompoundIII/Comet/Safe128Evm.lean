import Benchmarks.CompoundIII.Comet.PrincipalWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSafe128 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12207⟩ (n :: ret :: R) mem aw rdata σ k C) :
    (n.toNat < 2^128 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R)
      mem aw rdata σ k' C') ∨ (¬ n.toNat < 2^128 ∧ RDrev (deployedRuntime v) g s0) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
    (UInt256.ofNat 1)
  have hm : mask.toNat = 2^128-1 := by decide
  by_cases hn : n.toNat < 2^128
  · have r1 := cometWithExtendedAssetList_block_12207_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (ugt_zero (by change n.toNat ≤ mask.toNat; rw [hm]; omega)) h
    have r2 := cometWithExtendedAssetList_block_12224
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    change RD _ _ _ _ _ (UInt256.land n mask :: R) _ _ _ _ _ _ at r2
    rw [u256LandMaskCleanOfToNat n mask hm hn] at r2
    exact Or.inl ⟨hn, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_12207_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [ugt_one (by change mask.toNat < n.toNat; rw [hm]; omega)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact Or.inr ⟨hn, cometWithExtendedAssetList_block_12227
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega) r1⟩

end Benchmarks.CompoundIII.Comet
