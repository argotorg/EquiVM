import Benchmarks.CompoundIII.Comet.MulFactorEvm
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

attribute [local irreducible] mulFactorWord

theorem cometAbsorbCollateralFactor {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw value delta seized ptr factor : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hf : factor.toNat < 2^64)
    (hm : memLoad (ptr + UInt256.ofNat 192) mem = factor)
    (h : RD (deployedRuntime v) ee g s0 ⟨17769⟩
      (value :: delta :: seized :: ptr :: R) mem aw rdata σ k C) :
    if value.toNat * factor.toNat < UInt256.size ∧
        delta.toNat + (mulFactorWord value factor).toNat < UInt256.size then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17811⟩
        ((delta + mulFactorWord value factor) :: seized :: value :: R)
        mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r5 := cometWithExtendedAssetList_block_17769 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_17769_stack] at r5
  rw [u256_add_comm (UInt256.ofNat 192), hm] at r5
  have r6 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  dsimp only [cometWithExtendedAssetList_block_2959_stack] at r6
  rw [mask64Clean _ hf] at r6
  have r7 := cometWithExtendedAssetList_block_17783 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  have r8 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
  dsimp only [cometWithExtendedAssetList_block_2959_stack] at r8
  rw [mask64Clean _ hf] at r8
  have r9 := cometWithExtendedAssetList_block_17792 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
  dsimp only [cometWithExtendedAssetList_block_17792_stack] at r9
  have hfactor := cometMulFactor (v := v) (ee := ee) (g := g) (s0 := s0)
    (mem := mem) (rdata := rdata) (σ := σ)
    (aw := M aw (ptr + UInt256.ofNat 192) ⟨32⟩) (n := value)
    (factor := factor) (ret := ⟨17802⟩) (R := delta :: seized :: value :: R)
    (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9
  by_cases hv2 : value.toNat *
      factor.toNat < UInt256.size
  · rw [if_pos hv2] at hfactor
    obtain ⟨k10, C10, r10⟩ := hfactor
    have r11 := cometWithExtendedAssetList_block_17802 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r10
    by_cases hv3 : delta.toNat + (mulFactorWord value factor).toNat < UInt256.size
    · rw [if_pos ⟨hv2, hv3⟩]
      obtain ⟨k12, C12, r12⟩ := cometCheckedAdd (v := v) (x := delta)
        (y := mulFactorWord value factor)
        (by change R.length + 2 + 5 ≤ 1024; omega) hv3
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r11
      exact ⟨_, _, _, r12⟩
    · rw [if_neg (fun h ↦ hv3 h.2)]
      exact cometCheckedAdd_revert (v := v) (x := delta)
        (y := mulFactorWord value factor)
        (by change R.length + 3 + 4 ≤ 1024; omega) (Nat.le_of_not_lt hv3) r11
  · rw [if_neg hv2] at hfactor
    rw [if_neg (fun h ↦ hv2 h.1)]
    exact hfactor

end Benchmarks.CompoundIII.Comet
