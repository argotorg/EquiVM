import Benchmarks.CompoundIII.Comet.PackedPresentValueEvm
import Benchmarks.CompoundIII.Comet.Checked104Evm
import Benchmarks.CompoundIII.Comet.TotalsStorage
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyBaseEvents {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw amount sender supplied dst ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (hsupplied : supplied.toNat < 2^104) (hperm : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12604⟩
      (amount :: sender :: supplied :: dst :: ret :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ k' C' := by
  by_cases hz : supplied = UInt256.ofNat 0
  · have r1 := cometWithExtendedAssetList_block_12604_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      hperm (by rw [u256_land_comm, mask104Clean supplied hsupplied]; exact hz) h
    have r2 := cometWithExtendedAssetList_block_12679
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_12604_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      hperm (by rw [u256_land_comm, mask104Clean supplied hsupplied]; exact hz)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_12682
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨_, _, r5⟩ := cometPresentSupplyFromPacked (v := v)
      (by change R.length + 5 + 8 ≤ 1024; omega) hsupplied
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r6 := cometWithExtendedAssetList_block_12721
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    have r7 := cometWithExtendedAssetList_block_12737
      (immWords := wordsOf (immStore v)) (by omega) hperm hret r6
    exact ⟨_, _, _, _, r7⟩

end Benchmarks.CompoundIII.Comet
