import Benchmarks.CompoundIII.Comet.PackedPresentValueEvm
import Benchmarks.CompoundIII.Comet.Checked104Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_069
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_070

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferBaseMint {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw a b supplied dst ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hS : supplied.toNat < 2^104) (hp : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨14977⟩
      (a :: b :: UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
        (UInt256.ofNat 1) :: supplied :: dst :: ret :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ k' C' := by
  by_cases hz : supplied = UInt256.ofNat 0
  · have r1 := cometWithExtendedAssetList_block_14977_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [u256_land_comm, mask104Clean supplied hS]; exact hz) h
    have r2 := cometWithExtendedAssetList_block_14986
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_14977_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [u256_land_comm, mask104Clean supplied hS]; exact hz)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_14989
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨_, _, r3⟩ := cometPresentSupplyFromPacked (v := v)
      (by change R.length + 5 + 8 ≤ 1024; omega) hS
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_15023
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    have r5 := cometWithExtendedAssetList_block_12737
      (immWords := wordsOf (immStore v)) (by omega) hp hret r4
    exact ⟨_, _, _, _, r5⟩

theorem cometTransferBaseEvents {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw unused withdrawn src supplied dst ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 16 ≤ 1024)
    (hW : withdrawn.toNat < 2^104) (hS : supplied.toNat < 2^104) (hp : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨14959⟩
      (unused :: withdrawn :: src :: supplied :: dst :: ret :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata σ k' C' := by
  by_cases hz : withdrawn = UInt256.ofNat 0
  · have r1 := cometWithExtendedAssetList_block_14959_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
      (by rw [mask104Clean withdrawn hW]; exact hz) h
    exact cometTransferBaseMint (by omega) hS hp hret r1
  · have r1 := cometWithExtendedAssetList_block_14959_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
      (by rw [mask104Clean withdrawn hW]; exact hz)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_15051
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 9 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨_, _, r3⟩ := cometPresentSupplyFromPacked (v := v)
      (by change R.length + 8 + 8 ≤ 1024; omega) hW
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_15085
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    have r5 := cometWithExtendedAssetList_block_15113
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 6 ≤ 1024; omega) hp
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    exact cometTransferBaseMint (by omega) hS hp hret r5

end Benchmarks.CompoundIII.Comet
