import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometRateFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hfit : x.toNat < 2^64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8229⟩
      (x :: UInt256.ofNat 2425 :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (x :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_8229
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨k2, C2, r2⟩ := cometSafe64 (v := v) (by simpa using hstack) hfit
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_2425
    (immWords := wordsOf (immStore v)) (by omega) hvalid r2
  exact ⟨_, _, r3⟩

theorem cometRateFinish_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hfit : ¬ x.toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨8229⟩ (x :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_8229
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometSafe64_revert (v := v) hstack hfit r1

end Benchmarks.CompoundIII.Comet
