import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_076

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedIncrement32 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hn : n.toNat < 2^32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16642⟩ (n :: ret :: R) mem aw rdata σ k C) :
    if n.toNat + 1 < 2^32 then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((n + ⟨1⟩) :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hmask : UInt256.land n (UInt256.ofNat 4294967295) = n :=
    u256LandMaskCleanOfToNat _ _ (bits := 32) rfl hn
  split_ifs with hi
  · have hne : n ≠ (⟨4294967295⟩ : UInt256) := by
      intro he
      have he' := congrArg UInt256.toNat he
      change n.toNat = 4294967295 at he'
      omega
    have r1 := cometWithExtendedAssetList_block_16642_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hmask]; exact u256_eq_of_ne hne) h
    simp only [cometWithExtendedAssetList_block_16642_fallthrough_stack, hmask] at r1
    exact ⟨_, _, cometWithExtendedAssetList_block_16661
      (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  · have he : n = (⟨4294967295⟩ : UInt256) := u256_inj (by change n.toNat = 4294967295; omega)
    have r1 := cometWithExtendedAssetList_block_16642_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hmask, he]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7859
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
