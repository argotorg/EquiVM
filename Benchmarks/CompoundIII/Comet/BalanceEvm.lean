import Benchmarks.CompoundIII.Comet.BalanceSource
import Benchmarks.CompoundIII.Comet.AccountIndicesEvm
import Benchmarks.CompoundIII.Comet.PresentValueEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_082

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometBalanceReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret indexB indexS account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hi : indexS.toNat < 2^64)
    (haddr : account.toNat < EVM.addressModulus)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨18287⟩
      (indexB :: indexS :: account :: ret :: R) mem aw rdata σ k C) :
    let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      ((if 0 < signed104 basic then presentValueWord indexS (positivePrincipal basic)
        else ⟨0⟩) :: R) (twoWordHashMem account ⟨5⟩ mem) aw' rdata σ k' C' := by
  dsimp only
  let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
  let mem₁ := twoWordHashMem account ⟨5⟩ mem
  have hclean : UInt256.land account (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) = account :=
    solcAddrMask_clean haddr
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ =
      solcMappingSlot ⟨5⟩ account := twoWordHashMem_solcMappingSlot_any ⟨5⟩ account mem
  by_cases hp : 0 < signed104 basic
  · rw [if_pos hp]
    have hcond : UInt256.isZero (UInt256.sgt (UInt256.signextend (UInt256.ofNat 12) basic)
        (UInt256.ofNat 0)) = UInt256.ofNat 0 := by
      exact isZero_eq_zero_of_ne (signed104_sgt_pos hp)
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_18287_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hclean]; change UInt256.isZero (UInt256.sgt (UInt256.signextend _ (solcSlotWordAt
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee)) _) = _
          rw [hhash]; exact hcond) h
    unfold cometWithExtendedAssetList_block_18287_fallthrough_stack
      cometWithExtendedAssetList_block_18287_fallthrough_memory at r1
    rw [hclean] at r1
    change RD _ _ _ _ _ (UInt256.ofNat 0 :: indexS :: UInt256.signextend (UInt256.ofNat 12)
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee) ::
      ret :: R) mem₁ _ _ _ _ _ at r1
    have hsign : UInt256.signextend (UInt256.ofNat 12)
        (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) = positivePrincipal basic :=
      signextend104_nonneg (le_of_lt hp)
    rw [hhash, hsign] at r1
    have r2 := cometWithExtendedAssetList_block_18328
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometUnsignedPresentValue (v := v)
      (by omega) hi (positivePrincipal_lt basic) hret r2
    exact ⟨_, _, _, r3⟩
  · rw [if_neg hp]
    have hcmp : UInt256.sgt (UInt256.signextend (UInt256.ofNat 12)
        (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee)) (UInt256.ofNat 0) = ⟨0⟩ :=
      signed104_sgt_nonpos (le_of_not_gt hp)
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_18287_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hclean]; change UInt256.isZero (UInt256.sgt (UInt256.signextend _ (solcSlotWordAt
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee)) _) ≠ _
          rw [hhash, hcmp]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    unfold cometWithExtendedAssetList_block_18287_taken_stack
      cometWithExtendedAssetList_block_18287_taken_memory at r1
    rw [hclean] at r1
    have r2 := cometWithExtendedAssetList_block_18340
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, _, r2⟩

theorem cometBalance {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 34 ≤ 1024) (haddr : account.toNat < EVM.addressModulus)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨18252⟩ (account :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    if CurrentIndicesValid v w0 w1 (timestampWord ee) then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
        (balanceWord v w0 w1 (timestampWord ee)
          (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) :: R)
        (twoWordHashMem account ⟨5⟩ mem) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have r1 := cometWithExtendedAssetList_block_18252
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hidx := cometAccountIndices (v := v)
    (by simpa only [List.length_cons] using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  dsimp only at hidx
  split at hidx
  · rename_i hv
    rw [if_pos hv]
    obtain ⟨k2, C2, r2⟩ := hidx
    exact cometBalanceReturn (v := v) (by omega) (currentIndex_lt hv false) haddr hret r2
  · rename_i hv
    rw [if_neg hv]
    exact hidx

end Benchmarks.CompoundIII.Comet
