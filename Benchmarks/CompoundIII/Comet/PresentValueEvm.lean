import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.Unsigned104
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.PresentValue
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_043
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometPresentValue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret index principal : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^104)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9318⟩ (index :: principal :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (presentValueWord index principal :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9318
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
        (UInt256.ofNat 1)) principal = principal := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl hp
  simp only [cometWithExtendedAssetList_block_9318_stack, mask64Clean index hi, hclean] at r1
  obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
    (by simp only [List.length_cons]; omega)
    (lt_trans (presentValue_mul_lt hi hp) (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9192
    (immWords := wordsOf (immStore v)) (by omega) hret r2
  exact ⟨_, _, r3⟩

theorem cometUnsignedPresentValue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret index principal : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^103)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17913⟩
      (principal :: ⟨17536⟩ :: index :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (presentValueWord index principal :: R) mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, r1⟩ := cometUnsigned104 (v := v)
    (by simp only [List.length_cons]; omega) hp
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_17536
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometPresentValue (v := v)
    (by simpa only [List.length_cons] using hstack) hi (lt_trans hp (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  have r4 := cometWithExtendedAssetList_block_2425
    (immWords := wordsOf (immStore v)) (by omega) hret r3
  exact ⟨_, _, r4⟩

end Benchmarks.CompoundIII.Comet
