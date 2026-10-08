import Benchmarks.CompoundIII.Comet.CurrentIndicesEvm
import Benchmarks.CompoundIII.Comet.TotalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometTotalReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (indexS indexB w1 : UInt256)
    (hstack : R.length + 9 ≤ 1024)
    (hi : (if borrow then indexB else indexS).toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 (totalIndicesReturnPc borrow)
      (indexB :: indexS :: w1 :: ⟨1738⟩ :: ⟨1000000000000000⟩ :: ⟨32⟩ :: R)
      solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (presentValueWord (if borrow then indexB else indexS) (totalsPrincipalWord w1 borrow)).toByteArray := by
  let mask104 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hp (b : Bool) : UInt256.land mask104 (if b then UInt256.shiftRight w1 ⟨104⟩ else w1) =
      totalsPrincipalWord w1 b := by
    rw [u256_land_comm]
    exact (totalsPrincipalWord_eq w1 b).symm
  have hm : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (totalsPrincipalWord w1 borrow :: (if borrow then indexB else indexS) ::
        ⟨1738⟩ :: ⟨1000000000000000⟩ :: ⟨32⟩ :: R) solcFreePtrMem aw rdata σ k' C' := by
    cases borrow
    · have r1 := cometWithExtendedAssetList_block_1713
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      simp only [cometWithExtendedAssetList_block_1713_stack, mask64Clean indexS hi] at r1
      change RD _ _ _ _ _ (UInt256.land mask104 w1 :: indexS :: ⟨1738⟩ ::
        ⟨1000000000000000⟩ :: ⟨32⟩ :: R) _ _ _ _ _ _ at r1
      rw [show UInt256.land mask104 w1 = totalsPrincipalWord w1 false from hp false] at r1
      exact ⟨_, _, r1⟩
    · have r1 := cometWithExtendedAssetList_block_4299
        (immWords := wordsOf (immStore v)) (by simpa using hstack)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      simp only [cometWithExtendedAssetList_block_4299_stack, mask64Clean indexB hi] at r1
      change RD _ _ _ _ _ (UInt256.land mask104 (UInt256.shiftRight w1 ⟨104⟩) :: indexB ::
        ⟨1738⟩ :: ⟨1000000000000000⟩ :: ⟨32⟩ :: R) _ _ _ _ _ _ at r1
      rw [show UInt256.land mask104 (UInt256.shiftRight w1 ⟨104⟩) =
        totalsPrincipalWord w1 true from hp true] at r1
      exact ⟨_, _, r1⟩
  obtain ⟨k1, C1, r1⟩ := hm
  obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v) (by simp only [List.length_cons]; omega)
    (lt_trans (presentValue_mul_lt hi (totalsPrincipalWord_lt _ _)) (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_1738
    (immWords := wordsOf (immStore v)) (by omega) r2
  exact (getterReturnData (presentValueWord (if borrow then indexB else indexS)
    (totalsPrincipalWord w1 borrow))) ▸ r3

end Benchmarks.CompoundIII.Comet
