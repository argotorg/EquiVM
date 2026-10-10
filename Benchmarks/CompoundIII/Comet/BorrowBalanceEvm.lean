import Benchmarks.CompoundIII.Comet.BorrowBalanceSource
import Benchmarks.CompoundIII.Comet.AccountIndicesEvm
import Benchmarks.CompoundIII.Comet.PresentValueEvm
import Benchmarks.CompoundIII.Comet.Negate104Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_082

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometBorrowNegativePrincipal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret indexB indexS account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (haddr : account.toNat < EVM.addressModulus)
    (hp : signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) < 0)
    (h : RD (deployedRuntime v) ee g s0 ⟨18357⟩
      (indexB :: indexS :: account :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨10633⟩
      (UInt256.signextend (UInt256.ofNat 12) (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) ::
        ⟨18413⟩ :: ⟨17536⟩ :: indexB :: ⟨2425⟩ :: ret :: R)
      (twoWordHashMem account ⟨5⟩ mem) aw' rdata σ k' C' := by
  let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
  let mem₁ := twoWordHashMem account ⟨5⟩ mem
  have hclean : UInt256.land account (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) = account :=
    solcAddrMask_clean haddr
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ =
      solcMappingSlot ⟨5⟩ account := twoWordHashMem_solcMappingSlot_any ⟨5⟩ account mem
  have hcond : UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) basic)
      (UInt256.ofNat 0)) = UInt256.ofNat 0 :=
    isZero_eq_zero_of_ne (signed104_slt_neg hp)
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_18357_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [hclean]; change UInt256.isZero (UInt256.slt (UInt256.signextend _ (solcSlotWordAt
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee)) _) = _
        rw [hhash]; exact hcond) h
  unfold cometWithExtendedAssetList_block_18357_fallthrough_stack
    cometWithExtendedAssetList_block_18357_fallthrough_memory at r1
  rw [hclean] at r1
  change RD _ _ _ _ _ (UInt256.ofNat 0 :: indexB :: UInt256.signextend (UInt256.ofNat 12)
    (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee) ::
    ret :: R) mem₁ _ _ _ _ _ at r1
  rw [hhash] at r1
  have r2 := cometWithExtendedAssetList_block_18398
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, _, r2⟩

theorem cometBorrowBalanceReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret indexB indexS account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hi : indexB.toNat < 2^64)
    (haddr : account.toNat < EVM.addressModulus)
    (hmin : -(2^103 : Int) < signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨18357⟩
      (indexB :: indexS :: account :: ret :: R) mem aw rdata σ k C) :
    let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      ((if signed104 basic < 0 then presentValueWord indexB (negativePrincipal basic)
        else ⟨0⟩) :: R) (twoWordHashMem account ⟨5⟩ mem) aw' rdata σ k' C' := by
  dsimp only
  let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
  let mem₁ := twoWordHashMem account ⟨5⟩ mem
  have hclean : UInt256.land account (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) = account :=
    solcAddrMask_clean haddr
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁ =
      solcMappingSlot ⟨5⟩ account := twoWordHashMem_solcMappingSlot_any ⟨5⟩ account mem
  by_cases hp : signed104 basic < 0
  · obtain ⟨aw2, k2, C2, r2⟩ :=
      cometBorrowNegativePrincipal (v := v) (by omega) haddr hp h
    rw [if_pos hp]
    obtain ⟨k3, C3, r3⟩ := cometNegate104 (v := v)
      (by simp only [List.length_cons]; omega) (le_of_lt hp) hmin
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_18413
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨k5, C5, r5⟩ := cometUnsignedPresentValue (v := v)
      (by omega) hi (negativePrincipal_lt hmin) hret r4
    exact ⟨_, _, _, r5⟩
  · rw [if_neg hp]
    have hcmp : UInt256.slt (UInt256.signextend (UInt256.ofNat 12)
        (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee)) (UInt256.ofNat 0) = ⟨0⟩ :=
      signed104_slt_nonneg (le_of_not_gt hp)
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_18357_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hclean]; change UInt256.isZero (UInt256.slt (UInt256.signextend _ (solcSlotWordAt
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem₁) σ ee)) _) ≠ _
          rw [hhash, hcmp]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    unfold cometWithExtendedAssetList_block_18357_taken_stack
      cometWithExtendedAssetList_block_18357_taken_memory at r1
    rw [hclean] at r1
    have r2 := cometWithExtendedAssetList_block_18340
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, _, r2⟩

theorem cometBorrowBalanceReturn_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret indexB indexS account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (haddr : account.toNat < EVM.addressModulus)
    (hmin : signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) = -(2^103 : Int))
    (h : RD (deployedRuntime v) ee g s0 ⟨18357⟩
      (indexB :: indexS :: account :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hp : signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) < 0 := by
    rw [hmin]
    norm_num
  obtain ⟨aw2, k2, C2, r2⟩ := cometBorrowNegativePrincipal (v := v) (by omega) haddr hp h
  exact cometNegate104_revert (v := v) (by simp only [List.length_cons]; omega) hmin r2

theorem cometBorrowBalance {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 34 ≤ 1024) (haddr : account.toNat < EVM.addressModulus)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨18346⟩ (account :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    let basic := solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee
    if BorrowBalanceValid v w0 w1 (timestampWord ee) basic then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
        (borrowBalanceWord v w0 w1 (timestampWord ee) basic :: R)
        (twoWordHashMem account ⟨5⟩ mem) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have r1 := cometWithExtendedAssetList_block_18346
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hidx := cometAccountIndices (v := v)
    (by simpa only [List.length_cons] using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  dsimp only at hidx
  split at hidx
  · rename_i hv
    obtain ⟨k2, C2, r2⟩ := hidx
    by_cases hmin : -(2^103 : Int) <
        signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee)
    · rw [if_pos (show BorrowBalanceValid v _ _ _ _ from ⟨hv, hmin⟩)]
      exact cometBorrowBalanceReturn (v := v) (by omega)
        (currentIndex_lt hv true) haddr hmin hret r2
    · rw [if_neg (show ¬ BorrowBalanceValid v _ _ _ _ from fun h ↦ hmin h.2)]
      have heq : signed104 (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee) =
          -(2^103 : Int) := by
        have hb := signed104_bounds (solcSlotWordAt (solcMappingSlot ⟨5⟩ account) σ ee)
        omega
      exact cometBorrowBalanceReturn_revert (v := v) (by omega) haddr heq r2
  · rename_i hv
    simp only [BorrowBalanceValid, hv, false_and, if_false]
    exact hidx

end Benchmarks.CompoundIII.Comet
