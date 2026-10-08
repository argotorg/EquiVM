import Benchmarks.CompoundIII.Comet.UtilizationSource
import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometUtilization {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9196⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (utilizationWord (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee) :: R)
      mem aw rdata σ k' C' := by
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let mask64 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
    (UInt256.ofNat 1)
  let mask104 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hiS : totalsIndexWord w0 false = UInt256.land w0 mask64 := totalsIndexWord_eq w0 false
  have hpS : totalsPrincipalWord w1 false = UInt256.land w1 mask104 :=
    totalsPrincipalWord_eq w1 false
  have hiB : totalsIndexWord w0 true =
      UInt256.land (UInt256.shiftRight w0 (UInt256.ofNat 64)) mask64 := totalsIndexWord_eq w0 true
  have hpB : totalsPrincipalWord w1 true =
      UInt256.land (UInt256.shiftRight w1 (UInt256.ofNat 104)) mask104 := totalsPrincipalWord_eq w1 true
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_9196
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ (UInt256.land w1 mask104 :: UInt256.land w0 mask64 ::
    UInt256.ofNat 9246 :: UInt256.ofNat 1000000000000000 :: mask64 :: mask104 :: w1 ::
    UInt256.ofNat 9262 :: UInt256.ofNat 1000000000000000 :: w0 :: ret :: R) _ _ _ _ _ _ at r1
  rw [← hiS, ← hpS] at r1
  have hmul (b : Bool) :
      (totalsPrincipalWord w1 b).toNat * (totalsIndexWord w0 b).toNat < UInt256.size :=
    lt_trans (presentValue_mul_lt (totalsIndexWord_lt _ _) (totalsPrincipalWord_lt _ _)) (by decide)
  obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
    (by simp only [List.length_cons]; omega) (hmul false)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9246
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  change RD _ _ _ _ _ (UInt256.land (UInt256.shiftRight w1 (UInt256.ofNat 104)) mask104 ::
    UInt256.land (UInt256.shiftRight w0 (UInt256.ofNat 64)) mask64 ::
    UInt256.ofNat 9262 :: UInt256.ofNat 1000000000000000 ::
    totalPresentValue w0 w1 false :: ret :: R) _ _ _ _ _ _ at r3
  rw [← hiB, ← hpB] at r3
  obtain ⟨k4, C4, r4⟩ := cometCheckedMul (v := v)
    (by simp only [List.length_cons]; omega) (hmul true)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  by_cases hz : totalPresentValue w0 w1 false = ⟨0⟩
  · have r5 := cometWithExtendedAssetList_block_9262_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hz r4
    have r6 := cometWithExtendedAssetList_block_9269
      (immWords := wordsOf (immStore v)) (by omega) hvalid r5
    refine ⟨k4 + 5 + 5, C4 + 22 + 18, ?_⟩
    change RD _ _ _ _ _ (utilizationWord w0 w1 :: R) _ _ _ _ _ _
    rw [utilizationWord, if_pos hz]
    exact r6
  · have r5 := cometWithExtendedAssetList_block_9262_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hz
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_9275_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (checkedMulGuard_zero (utilizationProduct_lt w0 w1)) r5
    have r7 := cometWithExtendedAssetList_block_9301
      (immWords := wordsOf (immStore v)) (by omega) hvalid r6
    refine ⟨k4 + 5 + 15 + 4, C4 + 22 + 52 + 21, ?_⟩
    change RD _ _ _ _ _ (utilizationWord w0 w1 :: R) _ _ _ _ _ _
    rw [utilizationWord, if_neg hz]
    exact r7

end Benchmarks.CompoundIII.Comet
