import Benchmarks.CompoundIII.Comet.CollateralCheckRead
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCollateralDebtRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 14 ≤ 1024)
    (hp : signed104 (collateralBasicWord evm account) < 0) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (collateralPrincipalPc borrow)
      (UInt256.signextend (UInt256.ofNat 12) (collateralBasicWord evm account) ::
        EVM.word account.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨10688⟩
      (UInt256.signextend (UInt256.ofNat 12) (collateralBasicWord evm account) ::
        ⟨10259⟩ :: collateralLoopInitPc borrow :: userBasicFieldWord
          (collateralBasicWord evm account) 3 :: userBasicFieldWord
          (collateralBasicWord evm account) 2 :: EVM.word account.val :: ⟨0⟩ :: ret :: R)
      (collateralBasicMemory (collateralBasicMemory mem account) account) aw' rdata σ k' C' := by
  let basic := collateralBasicWord evm account
  have hcond : UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 12)
      (UInt256.signextend (UInt256.ofNat 12) basic)) (UInt256.ofNat 0)) = UInt256.ofNat 0 := by
    rw [signextend104_idem]
    exact isZero_eq_zero_of_ne (signed104_slt_neg hp)
  have hstart : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2428⟩
      (⟨5⟩ :: EVM.word account.val :: ⟨10214⟩ :: collateralAssetsPc borrow ::
        UInt256.signextend (UInt256.ofNat 12) basic :: EVM.word account.val :: ⟨0⟩ :: ret :: R)
      mem aw rdata σ k' C' := by
    cases borrow with
    | false =>
        have r1 := cometWithExtendedAssetList_block_10819_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega) hcond h
        exact ⟨_, _, cometWithExtendedAssetList_block_10835
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 7 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1⟩
    | true =>
        have r1 := cometWithExtendedAssetList_block_10185_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega) hcond h
        exact ⟨_, _, cometWithExtendedAssetList_block_10201
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 7 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1⟩
  obtain ⟨k1, C1, r1⟩ := hstart
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 5 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_10214
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
    (by cases borrow <;>
      rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v] <;> jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_10214_stack] at r3
  change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 65535)
    (UInt256.shiftRight (solcSlotWord σ ee (userBasicSlot account)) (UInt256.ofNat 232)) :: _)
    _ _ _ _ _ _ at r3
  rw [← hs.storageRead] at r3
  have hassets : UInt256.land (UInt256.ofNat 65535)
      (UInt256.shiftRight basic (UInt256.ofNat 232)) = userBasicFieldWord basic 2 := by
    rw [u256_land_comm]
    exact (userBasicFieldWords basic).2.2.1.symm
  change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 65535)
    (UInt256.shiftRight basic (UInt256.ofNat 232)) :: _) _ _ _ _ _ _ at r3
  rw [hassets] at r3
  have hreservedStart : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2428⟩
      (⟨5⟩ :: EVM.word account.val :: ⟨10246⟩ :: ⟨10253⟩ :: ⟨10259⟩ ::
        collateralLoopInitPc borrow :: UInt256.signextend (UInt256.ofNat 12) basic ::
        userBasicFieldWord basic 2 :: EVM.word account.val :: ⟨0⟩ :: ret :: R)
      (collateralBasicMemory mem account) aw2 rdata σ k' C' := by
    cases borrow
    · exact ⟨_, _, cometWithExtendedAssetList_block_10848
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3⟩
    · exact ⟨_, _, cometWithExtendedAssetList_block_10225
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3⟩
  obtain ⟨k4, C4, r4⟩ := hreservedStart
  obtain ⟨aw5, k5, C5, r5⟩ := cometMappingHash (v := v)
    (by change R.length + 8 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
  obtain ⟨k6, C6, r6⟩ := cometWithExtendedAssetList_block_10246
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  dsimp only [cometWithExtendedAssetList_block_10246_stack] at r6
  change RD _ _ _ _ _
    (UInt256.shiftRight (solcSlotWord σ ee (userBasicSlot account)) (UInt256.ofNat 248) :: _)
    _ _ _ _ _ _ at r6
  rw [← hs.storageRead] at r6
  have hreserved : UInt256.shiftRight basic (UInt256.ofNat 248) = userBasicFieldWord basic 3 :=
    (userBasicFieldWords basic).2.2.2.symm
  change RD _ _ _ _ _ (UInt256.shiftRight basic (UInt256.ofNat 248) :: _) _ _ _ _ _ _ at r6
  rw [hreserved] at r6
  have r7 := cometWithExtendedAssetList_block_10253 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  exact ⟨_, _, _, r7⟩

end Benchmarks.CompoundIII.Comet
