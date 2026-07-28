import Benchmarks.UniswapV3Pool.BurnSourceSuccess
import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedBridge

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnZeroDeltaPositionUpdateFinish
    {v : PoolImmutables}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ lockedEvm lockedSolm : AccountMap}
    {A : Substate} {I : ExecutionEnv} {g tokensOwed0 tokensOwed1 : UInt256}
    {feeGrowthInside0 feeGrowthInside1 positionBase : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
          (List.map Param.name burnTransition.params)
          (transitionSignature burnTransition).paramTypes I.calldata =
        some (burnStore I))
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon : UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnoDelegate : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hLowerMin : ¬ tickSpacingSint24Value (burnTickLowerWord I) < -887272)
    (hUpperMax : ¬ 887272 < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hAccountsLocked : accountMapEquiv lockedEvm lockedSolm)
    (hlockedSolm :
      lockedSolm =
        sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (hfee0 : feeGrowthInside0 = burnTickGetInside0Word lockedEvm I)
    (hfee1 : feeGrowthInside1 = burnTickGetInside1Word lockedEvm I)
    (hPositionBase : positionBase = positionsBase (burnPositionKeyKey I))
    (hliq :
      burnPositionUpdateSlot0Packed (solcSlotWord lockedEvm I positionBase) ≠ ⟨0⟩)
    (hlow0 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0
                (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord lockedEvm I positionBase)))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed0)
    (hlow1 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1
                (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord lockedEvm I positionBase)))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1)
    (hrdSuccessCases :
      (RDret code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner lockedEvm
                (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
              (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
            ⟨0⟩
            (burnPostPositionUpdateUnlockedSlotWord
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner lockedEvm
                  (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
                (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
              I))
          (UInt256.toByteArray (⟨0⟩ : UInt256) ++
            UInt256.toByteArray (⟨0⟩ : UInt256)) ∧
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩ ∧
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩) ∨
      (RDret code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (burnPostPositionUpdateTokensOwedAccountMap I
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner lockedEvm
                  (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
                (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
              positionBase tokensOwed0 tokensOwed1)
            ⟨0⟩
            (burnPostPositionUpdateUnlockedSlotWord
              (burnPostPositionUpdateTokensOwedAccountMap I
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner lockedEvm
                    (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
                  (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
                positionBase tokensOwed0 tokensOwed1)
              I))
          (UInt256.toByteArray (⟨0⟩ : UInt256) ++
            UInt256.toByteArray (⟨0⟩ : UInt256)) ∧
        (UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 ≠ ⟨0⟩ ∨
          UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 ≠ ⟨0⟩))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hinside0 :
      burnTickGetInside0Value lockedSolm I =
        .int (Int.ofNat feeGrowthInside0.toNat) := by
    rw [burnTickGetInside0Value_eq_word]
    rw [← burnTickGetInside0Word_eq_of_accountMapEquiv hAccountsLocked I]
    rw [hfee0]
  have hinside1 :
      burnTickGetInside1Value lockedSolm I =
        .int (Int.ofNat feeGrowthInside1.toNat) := by
    rw [burnTickGetInside1Value_eq_word]
    rw [← burnTickGetInside1Word_eq_of_accountMapEquiv hAccountsLocked I]
    rw [hfee1]
  have hliqSolm :
      burnPositionUpdateSlot0Packed
          (solcSlotWord lockedSolm I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩ := by
    have hslot := solcSlotWord_eq_of_accountMapEquiv hAccountsLocked I
      (positionsBase (burnPositionKeyKey I))
    have hliqEvm :
        burnPositionUpdateSlot0Packed
            (solcSlotWord lockedEvm I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩ := by
      simpa [hPositionBase] using hliq
    intro hzeroSlot
    exact hliqEvm (by rwa [hslot])
  rcases hrdSuccessCases with hzeroTokens | hsomeTokens
  · rcases hzeroTokens with ⟨hrdRet, htokens0, htokens1⟩
    have htokens0Src :
        burnPositionUpdateSourceTokensOwed0Int lockedSolm I
            (Int.ofNat feeGrowthInside0.toNat) = 0 := by
      rw [← burnPositionUpdateSourceTokensOwed0Int_eq_of_accountMapEquiv
        hAccountsLocked I (Int.ofNat feeGrowthInside0.toNat)]
      exact burnPositionUpdateSourceTokensOwed0Int_eq_zero_of_mask_eq_zero
        (by simpa [hPositionBase] using hlow0.trans htokens0)
    have htokens1Src :
        burnPositionUpdateSourceTokensOwed1Int lockedSolm I
            (Int.ofNat feeGrowthInside1.toNat) = 0 := by
      rw [← burnPositionUpdateSourceTokensOwed1Int_eq_of_accountMapEquiv
        hAccountsLocked I (Int.ofNat feeGrowthInside1.toNat)]
      exact burnPositionUpdateSourceTokensOwed1Int_eq_zero_of_mask_eq_zero
        (by simpa [hPositionBase] using hlow1.trans htokens1)
    let evmFeesSolm :=
      Solm.EVM.storageStore
        (Solm.EVM.storageStore
          (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
          feeGrowthInside0)
        I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
        feeGrowthInside1
    let evmFeesEvm : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner lockedEvm
          (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
        (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1
    have hbody :=
      uniswapV3PoolBurnSourceZeroDeltaReturnsZeroTokens (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) feeGrowthInside0 feeGrowthInside1
          hwv hunlockedSolm hcanon
          (by simpa [hlockedSolm] using hinside0)
          (by simpa [hlockedSolm] using hinside1)
          hnoDelegate htickLt hLowerMin hUpperMax hzero
          (by simpa [hlockedSolm] using hliqSolm)
          (by simpa [hlockedSolm] using htokens0Src)
          (by simpa [hlockedSolm] using htokens1Src)
    have hfeesAccounts : accountMapEquiv evmFeesEvm evmFeesSolm.accountMap := by
      have hstores :=
        accountMapEquiv_sstoreAccountMap I.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1
          (accountMapEquiv_sstoreAccountMap I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
            feeGrowthInside0 hAccountsLocked)
      simpa [evmFeesEvm, evmFeesSolm, storageStore_accountMap, initState,
        hPositionBase] using hstores
    have hfinalAccounts :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner evmFeesEvm ⟨0⟩
            (burnPostPositionUpdateUnlockedSlotWord evmFeesEvm I))
          (slot0AfterUnlockState evmFeesSolm).accountMap := by
        exact burnPostPositionUpdateFinalAccountMapEquiv
          (evm := evmFeesSolm) (σ := evmFeesEvm) (I := I)
          hfeesAccounts
          (by simp [evmFeesSolm, storageStore_executionEnv, initState])
    exact hrdRet.reEquivExecutionGenAccountMapEquiv
      hcode hdispatch hdecode hbody
        (by
          simp [slot0AfterUnlockState,
            storageStore_createdAccounts, initState])
        (by simpa [evmFeesEvm, evmFeesSolm, hlockedSolm] using hfinalAccounts)
        (by
          rw [show burnTransition.returnType = [uint256, uint256] from rfl]
          exact returnEquiv.returned rfl (by native_decide))
  · rcases hsomeTokens with ⟨hrdRet, htokens⟩
    let evmFeesSolm :=
      Solm.EVM.storageStore
        (Solm.EVM.storageStore
          (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
          feeGrowthInside0)
        I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
        feeGrowthInside1
    let evmFeesEvm : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner lockedEvm
          (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
        (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1
    have hcond :
        evalExpr? (config v)
          (burnPositionUpdateValueAfterTokensOwed1Frame v
            lockedSolm I (Int.ofNat feeGrowthInside0.toNat)
            (Int.ofNat feeGrowthInside1.toNat))
          evmFeesSolm
          (orE (gtE (.var "tokensOwed0") (.intLit 0))
            (gtE (.var "tokensOwed1") (.intLit 0))) =
            .ok (.bool true) := by
      rcases htokens with htokens0 | htokens1
      · have hpos0 :
            0 < burnPositionUpdateSourceTokensOwed0Int lockedSolm I
              (Int.ofNat feeGrowthInside0.toNat) := by
          rw [← burnPositionUpdateSourceTokensOwed0Int_eq_of_accountMapEquiv
            hAccountsLocked I (Int.ofNat feeGrowthInside0.toNat)]
          exact burnPositionUpdateSourceTokensOwed0Int_pos_of_mask_ne_zero
            (by
              intro hfast0
              have hfast0' :
                  UInt256.land burnPositionUpdateSlot0Mask
                      (UInt256.div
                        (uniswapV3PoolFullMathMulDivProd0
                          (UInt256.sub feeGrowthInside0
                            (solcSlotWord lockedEvm I
                              (positionBase + (⟨1⟩ : UInt256))))
                          (burnPositionUpdateSlot0Packed
                            (solcSlotWord lockedEvm I positionBase)))
                        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) = ⟨0⟩ := by
                simpa [hPositionBase] using hfast0
              exact htokens0 (by rwa [← hlow0]))
        exact
          burnPositionUpdateValue_evalTokensOwedGtTrueAfterTokensOwed1_left
            (v := v) (evm := evmFeesSolm) (σ := lockedSolm) (I := I)
            feeGrowthInside0 feeGrowthInside1 hpos0
      · have hpos1 :
            0 < burnPositionUpdateSourceTokensOwed1Int lockedSolm I
              (Int.ofNat feeGrowthInside1.toNat) := by
          rw [← burnPositionUpdateSourceTokensOwed1Int_eq_of_accountMapEquiv
            hAccountsLocked I (Int.ofNat feeGrowthInside1.toNat)]
          exact burnPositionUpdateSourceTokensOwed1Int_pos_of_mask_ne_zero
            (by
              intro hfast1
              have hfast1' :
                  UInt256.land burnPositionUpdateSlot0Mask
                      (UInt256.div
                        (uniswapV3PoolFullMathMulDivProd0
                          (UInt256.sub feeGrowthInside1
                            (solcSlotWord lockedEvm I
                              (positionBase + (⟨2⟩ : UInt256))))
                          (burnPositionUpdateSlot0Packed
                            (solcSlotWord lockedEvm I positionBase)))
                        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) = ⟨0⟩ := by
                simpa [hPositionBase] using hfast1
              exact htokens1 (by rwa [← hlow1]))
        by_cases hpos0 :
            0 < burnPositionUpdateSourceTokensOwed0Int lockedSolm I
              (Int.ofNat feeGrowthInside0.toNat)
        · exact
            burnPositionUpdateValue_evalTokensOwedGtTrueAfterTokensOwed1_left
              (v := v) (evm := evmFeesSolm) (σ := lockedSolm) (I := I)
              feeGrowthInside0 feeGrowthInside1 hpos0
        · have hnonneg0 :
              0 ≤ burnPositionUpdateSourceTokensOwed0Int lockedSolm I
                (Int.ofNat feeGrowthInside0.toNat) := by
            rw [burnPositionUpdateSourceTokensOwed0Int_eq_maskedWord]
            exact Int.natCast_nonneg _
          have hzero0 :
              burnPositionUpdateSourceTokensOwed0Int lockedSolm I
                (Int.ofNat feeGrowthInside0.toNat) = 0 := by
            omega
          exact
            burnPositionUpdateValue_evalTokensOwedGtTrueAfterTokensOwed1_right
              (v := v) (evm := evmFeesSolm) (σ := lockedSolm) (I := I)
              feeGrowthInside0 feeGrowthInside1 hzero0 hpos1
    have hbody :=
      uniswapV3PoolBurnSourceZeroDeltaReturnsTokensOwed (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) feeGrowthInside0 feeGrowthInside1
          hwv hunlockedSolm hcanon
          (by simpa [hlockedSolm] using hinside0)
          (by simpa [hlockedSolm] using hinside1)
          hnoDelegate htickLt hLowerMin hUpperMax hzero
          (by simpa [hlockedSolm] using hliqSolm)
          (by simpa [hlockedSolm, evmFeesSolm] using hcond)
    have hfeesAccounts : accountMapEquiv evmFeesEvm evmFeesSolm.accountMap := by
      have hstores :=
        accountMapEquiv_sstoreAccountMap I.codeOwner
          (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1
          (accountMapEquiv_sstoreAccountMap I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
            feeGrowthInside0 hAccountsLocked)
      simpa [evmFeesEvm, evmFeesSolm, storageStore_accountMap, initState,
        hPositionBase] using hstores
    let evmFeesEvmState : EVM.State := { evmFeesSolm with
      accountMap := evmFeesEvm }
    have hfeesState : EVMStateEquiv evmFeesEvmState evmFeesSolm := by
      refine ⟨?_, ?_, hfeesAccounts⟩ <;> simp [evmFeesEvmState]
    have hownerSolm :
        ∃ acc, σ_solm.find? I.codeOwner = some acc :=
      accountMap_find?_codeOwner_exists_of_burnUnlockedByte_ne_zero
        hunlockedSolm
    have hownerLocked :
        ∃ acc, lockedSolm.find? I.codeOwner = some acc := by
      simpa [hlockedSolm] using
        sstoreAccountMap_find?_same_exists (σ := σ_solm)
          (addr := I.codeOwner) (slot := ⟨0⟩)
          (val := burnLockedSlotWord σ_solm I) hownerSolm
    have hownerInit :
        ∃ acc,
          (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
              (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
            some acc := by
      simpa [initState] using hownerLocked
    have hownerFee0 :
        ∃ acc,
          (Solm.EVM.storageStore
                (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner
                (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
                feeGrowthInside0).accountMap.find?
              (Solm.EVM.storageStore
                (initState cA gh bl lockedSolm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner
                (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
                feeGrowthInside0).executionEnv.codeOwner =
            some acc := by
      simpa [initState] using
        storageStore_codeOwner_find?_exists hownerInit
          (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0
    have hownerFees :
        ∃ acc,
          evmFeesSolm.accountMap.find? evmFeesSolm.executionEnv.codeOwner =
            some acc := by
      simpa [evmFeesSolm, storageStore_executionEnv] using
        storageStore_codeOwner_find?_exists hownerFee0
          (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1
    have hload0 :
        Solm.EVM.storageLoad
            (burnPositionUpdateSourceAfterTokensOwed0State evmFeesSolm
              lockedSolm I feeGrowthInside0)
            (burnPositionUpdateSourceAfterTokensOwed0State evmFeesSolm
              lockedSolm I feeGrowthInside0).executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I) =
          burnPositionUpdateSourceTokensOwed0StoreWord evmFeesSolm lockedSolm
            I feeGrowthInside0 := by
      rcases hownerFees with ⟨accFees, haccFees⟩
      unfold burnPositionUpdateSourceAfterTokensOwed0State
      simpa [evmFeesSolm, storageStore_executionEnv] using
        storageLoad_storageStore_same_present evmFeesSolm
        evmFeesSolm.executionEnv.codeOwner
        haccFees
        (burnPositionUpdateSourceTokensOwedSlot I)
        (burnPositionUpdateSourceTokensOwed0StoreWord evmFeesSolm lockedSolm
          I feeGrowthInside0)
    have hslotBaseSolm :
        solcSlotWord lockedSolm I (positionsBase (burnPositionKeyKey I)) =
          solcSlotWord lockedEvm I positionBase := by
      rw [← solcSlotWord_eq_of_accountMapEquiv hAccountsLocked I
        (positionsBase (burnPositionKeyKey I))]
      rw [hPositionBase]
    have hslot1Solm :
        solcSlotWord lockedSolm I
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) =
          solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256)) := by
      rw [← solcSlotWord_eq_of_accountMapEquiv hAccountsLocked I
        (positionsBase (burnPositionKeyKey I) + ⟨1⟩)]
      rw [hPositionBase]
    have hslot2Solm :
        solcSlotWord lockedSolm I
            (positionsBase (burnPositionKeyKey I) + ⟨2⟩) =
          solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256)) := by
      rw [← solcSlotWord_eq_of_accountMapEquiv hAccountsLocked I
        (positionsBase (burnPositionKeyKey I) + ⟨2⟩)]
      rw [hPositionBase]
    have hword :=
      burnPositionUpdateSourceTokensOwedFinalStoreWord_eq_addedSlot3_of_low128
        evmFeesSolm lockedSolm I feeGrowthInside0 feeGrowthInside1
        tokensOwed0 tokensOwed1 hload0
        (by simpa [hslotBaseSolm, hslot1Solm, hPositionBase] using hlow0)
        (by simpa [hslotBaseSolm, hslot2Solm, hPositionBase] using hlow1)
    have hloadFees :=
      EVMStateEquiv.storageLoad_codeOwner hfeesState
        (burnPositionUpdateSourceTokensOwedSlot I)
    have hwordForState :
        burnPositionUpdateSourceTokensOwed1StoreWord
            (burnPositionUpdateSourceAfterTokensOwed0State evmFeesSolm
              lockedSolm I feeGrowthInside0)
            lockedSolm I feeGrowthInside1 =
          burnPositionUpdateTokensOwedAddedSlot3
            (Solm.EVM.storageLoad evmFeesEvmState
              evmFeesEvmState.executionEnv.codeOwner
              (burnPositionUpdateSourceTokensOwedSlot I))
            tokensOwed0 tokensOwed1 := by
      rw [hloadFees]
      exact hword
    have htokensAccountsSource :=
      burnPositionUpdateTokensOwedAccountMapEquiv_of_addedSlot3
        (evmEvm := evmFeesEvmState) (evmSolm := evmFeesSolm)
        (σ := lockedSolm) (I := I)
        (feeGrowthInside0X128 := feeGrowthInside0)
        (feeGrowthInside1X128 := feeGrowthInside1)
        (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
        hfeesState hwordForState
    let evmTokensSolm :=
      burnPositionUpdateSourceAfterTokensOwedState evmFeesSolm lockedSolm I
        feeGrowthInside0 feeGrowthInside1
    let evmTokensEvm : AccountMap :=
      sstoreAccountMap evmFeesEvmState.executionEnv.codeOwner
        evmFeesEvmState.accountMap
        (burnPositionUpdateSourceTokensOwedSlot I)
        (burnPositionUpdateTokensOwedAddedSlot3
          (Solm.EVM.storageLoad evmFeesEvmState
            evmFeesEvmState.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I))
          tokensOwed0 tokensOwed1)
    have htokensAccounts :
        accountMapEquiv evmTokensEvm evmTokensSolm.accountMap := by
      simpa [evmTokensEvm, evmTokensSolm] using htokensAccountsSource
    have htokensEvmPost :
        evmTokensEvm =
          burnPostPositionUpdateTokensOwedAccountMap I evmFeesEvm positionBase
            tokensOwed0 tokensOwed1 := by
      simp [evmTokensEvm, burnPostPositionUpdateTokensOwedAccountMap,
        evmFeesEvmState, evmFeesSolm, burnPositionUpdateSourceTokensOwedSlot,
        Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
        Account.lookupStorage, storageStore_executionEnv, initState,
        hPositionBase]
    have hfinalAccounts :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner evmTokensEvm ⟨0⟩
            (burnPostPositionUpdateUnlockedSlotWord evmTokensEvm I))
          (slot0AfterUnlockState evmTokensSolm).accountMap := by
      exact burnPostPositionUpdateFinalAccountMapEquiv
        (evm := evmTokensSolm) (σ := evmTokensEvm) (I := I)
        htokensAccounts
        (by simp [evmTokensSolm, evmFeesSolm,
          burnPositionUpdateSourceAfterTokensOwedState,
          burnPositionUpdateSourceAfterTokensOwed0State,
          storageStore_executionEnv, initState])
    have hfinalAccountsPost :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner
            (burnPostPositionUpdateTokensOwedAccountMap I evmFeesEvm
              positionBase tokensOwed0 tokensOwed1)
            ⟨0⟩
            (burnPostPositionUpdateUnlockedSlotWord
              (burnPostPositionUpdateTokensOwedAccountMap I evmFeesEvm
                positionBase tokensOwed0 tokensOwed1)
              I))
          (slot0AfterUnlockState evmTokensSolm).accountMap := by
      simpa [htokensEvmPost] using hfinalAccounts
    exact hrdRet.reEquivExecutionGenAccountMapEquiv
      hcode hdispatch hdecode hbody
        (by
          simp [slot0AfterUnlockState,
            burnPositionUpdateSourceAfterTokensOwedState,
            burnPositionUpdateSourceAfterTokensOwed0State,
            storageStore_createdAccounts, initState])
        (by
          simpa [burnPostPositionUpdateTokensOwedAccountMap, evmFeesEvm,
            evmTokensSolm, evmFeesSolm, hlockedSolm] using hfinalAccountsPost)
        (by
          rw [show burnTransition.returnType = [uint256, uint256] from rfl]
          exact returnEquiv.returned rfl (by native_decide))

theorem uniswapV3PoolBurnZeroDeltaMulDivReturnToRuntimeFinish
    {v : PoolImmutables}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ lockedEvm lockedSolm : AccountMap}
    {A : Substate} {I : ExecutionEnv} {g tokensOwed0 tokensOwed1 : UInt256}
    {feeGrowthInside0 feeGrowthInside1 positionBase : UInt256} {code : ByteArray}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
          (List.map Param.name burnTransition.params)
          (transitionSignature burnTransition).paramTypes I.calldata =
        some (burnStore I))
    (hwv : I.weiValue = ⟨0⟩)
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon : UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnoDelegate : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hLowerMin : ¬ tickSpacingSint24Value (burnTickLowerWord I) < -887272)
    (hUpperMax : ¬ 887272 < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hAccountsLocked : accountMapEquiv lockedEvm lockedSolm)
    (hlockedSolm :
      lockedSolm =
        sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (hfee0 : feeGrowthInside0 = burnTickGetInside0Word lockedEvm I)
    (hfee1 : feeGrowthInside1 = burnTickGetInside1Word lockedEvm I)
    (hPositionBase : positionBase = positionsBase (burnPositionKeyKey I))
    (hliq :
      burnPositionUpdateSlot0Packed (solcSlotWord lockedEvm I positionBase) ≠ ⟨0⟩)
    (hrd21861 :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨21861⟩
        (tokensOwed1 :: tokensOwed0 ::
          burnPositionUpdateSlot0Packed (solcSlotWord lockedEvm I positionBase) ::
          burnPositionKeyNewFreePtrWord :: feeGrowthInside1 :: feeGrowthInside0 ::
          UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
          positionBase :: ⟨19527⟩ :: feeGrowthInside1 :: feeGrowthInside0 ::
          ⟨0⟩ :: ⟨0⟩ ::
          solcSlotWord lockedEvm I ⟨2⟩ :: solcSlotWord lockedEvm I ⟨1⟩ ::
          positionBase :: slot0TickReturnWord lockedEvm I ::
          UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
          UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
        (burnPositionUpdateMem5 lockedEvm I (solcSlotWord lockedEvm I positionBase)
          positionBase)
        (UInt256.ofNat 22) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner lockedEvm
            (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
          (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1) k C)
    (hlow0 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0
                (solcSlotWord lockedEvm I (positionBase + (⟨1⟩ : UInt256))))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord lockedEvm I positionBase)))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed0)
    (hlow1 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1
                (solcSlotWord lockedEvm I (positionBase + (⟨2⟩ : UInt256))))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord lockedEvm I positionBase)))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmload224 := burnPositionUpdateMem5_mload224 lockedEvm I
    (solcSlotWord lockedEvm I positionBase) positionBase
  have hdelta :
      UInt256.slt
          (UInt256.signextend ⟨15⟩
            (UInt256.signextend ⟨15⟩
              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))
          ⟨0⟩ = ⟨0⟩ := by
    rw [hzero]
    native_decide
  have hdest9737 :
      (D_J code 0).contains (⟨9737⟩ : UInt256) = true := by
    have hpreserve :
        D_J_auxPreservesTargetBool uniswapV3PoolBytecode
            uniswapV3PoolPatchOffsets (⟨9737⟩ : UInt256) 0 =
          true := by
      native_decide
    exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
      (uniswapV3PoolPatchOffsetMem v) hpreserve
  have hrdSuccessCases :=
    uniswapV3PoolBurnZeroDeltaPositionUpdateToFinalReturnCases
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord lockedEvm I positionBase))
      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
      (delta := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
      (posBase := positionBase)
      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
      (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
      (tick := slot0TickReturnWord lockedEvm I)
      (delta' := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
      (owner := UInt256.ofNat I.source.val) (free := ⟨256⟩) (r3 := ⟨0⟩)
      (amount := burnAmountCleanWord I) (eventUpper := burnTickUpperCleanWord I)
      (eventLower := burnTickLowerCleanWord I) (R := [solcSelectorWord I])
      (σmem := lockedEvm) (pos0 := solcSlotWord lockedEvm I positionBase)
      (rdata := ByteArray.empty) (cA := cA)
      (σ := sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner lockedEvm
          (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
        (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
      hpatch hdest9737 hperm hzero hmload224 hrd21861 hdelta
      (by simp only [List.length_singleton]; omega)
  exact
    uniswapV3PoolBurnZeroDeltaPositionUpdateFinish
      (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
      (lockedEvm := lockedEvm) (lockedSolm := lockedSolm)
      (A := A) (I := I) (g := g)
      (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
      (feeGrowthInside0 := feeGrowthInside0) (feeGrowthInside1 := feeGrowthInside1)
      (positionBase := positionBase) (code := code)
      hcode hdispatch hdecode hwv hunlockedSolm hcanon hnoDelegate
      htickLt hLowerMin hUpperMax hzero hAccountsLocked hlockedSolm
      hfee0 hfee1 hPositionBase (by simpa using hliq) hlow0 hlow1
      hrdSuccessCases

end Benchmarks.UniswapV3Pool
