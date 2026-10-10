import Benchmarks.CompoundIII.Comet.PresentValueEvm
import Benchmarks.CompoundIII.Comet.TotalsStorage
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometPresentSupplyFromPacked {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret totals principal : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hp : principal.toNat < 2^104)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨2959⟩
      (totals :: UInt256.ofNat 12716 :: principal :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (presentValueWord (totalsIndexWord totals false) principal :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_2959
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have he : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      totals = totalsIndexWord totals false := by
    rw [u256_land_comm]
    exact (totalsIndexWord_eq totals false).symm
  simp only [cometWithExtendedAssetList_block_2959_stack, he] at r1
  have r2 := cometWithExtendedAssetList_block_12716
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometPresentValue hstack (totalsIndexWord_lt totals false) hp hret r2

end Benchmarks.CompoundIII.Comet
