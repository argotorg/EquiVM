import Examples.UniswapV2Pair.SwapCommon
import Examples.UniswapV2Pair.SwapLock
import Examples.UniswapV2Pair.SwapOutputGuardRuntime
import Examples.UniswapV2Pair.SwapOutputSource
import Examples.UniswapV2Pair.SwapReserveGuardRuntime
import Examples.UniswapV2Pair.SwapReserveSource
import Examples.UniswapV2Pair.SwapRecipientRuntime
import Examples.UniswapV2Pair.SwapRecipientSource
import Examples.UniswapV2Pair.SwapTransfersAnyDepth
import Examples.UniswapV2Pair.BalanceCallSource
import Examples.UniswapV2Pair.SwapCallbackCases
import Examples.UniswapV2Pair.SwapBalanceSource
import Examples.UniswapV2Pair.SwapInputGuardRuntime
import Examples.UniswapV2Pair.SwapInputGuardSource
import Examples.UniswapV2Pair.SwapAdjustmentPrefix
import Examples.UniswapV2Pair.SwapInvariantSource
import Examples.UniswapV2Pair.SwapUpdateRuntime
import Examples.UniswapV2Pair.SwapTailSource
import Examples.UniswapV2Pair.SwapEventRuntime
import Examples.UniswapV2Pair.UpdateDynamicCallRuntimeCases
import Examples.UniswapV2Pair.SwapCallbackInput
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
namespace UniswapV2Pair

theorem uniswapSwapBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz132 : 132 ≤ I.calldata.size
  · by_cases hoff : solcLegacyMaxU32 < swapDataOffset I
    · exact uniswapSwapBodyDecodeFailed_offsetHuge hcode hsize hwv hsel hsz132 hoff
        hdispatch
    · by_cases hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size
      · by_cases hlenHuge : solcLegacyMaxU32 < swapDataSize I
        · exact uniswapSwapBodyDecodeFailed_lengthHuge hcode hsize hwv hsel hsz132
            hoff hlenWord hlenHuge hdispatch
        · by_cases hpayload : (((I.calldata.toList.drop 4).drop
              (swapDataOffset I + 32)).take (swapDataSize I)).length = swapDataSize I
          · have hpayloadLe := swapPayloadPresent_le (I := I) hlenWord hpayload
            have hsz4 : 4 ≤ I.calldata.size := by omega
            obtain ⟨_, _, rd1475⟩ := uniswapSwapDecodeRuntimeOk hsize hsz132 hoff hlenWord hlenHuge hpayloadLe
              (uniswapReachSwapBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
            let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hstorage : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ =
                (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) := by
              have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
              simpa [evmS, initState] using hword.symm
            by_cases hlocked : (σ_evm.find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
            · have rdRev := RD.uniswapSwapLockedReverts rd1475 hlocked (by simp only [List.length_cons, List.length_nil]; omega)
              exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                (uniswapSwapBodyReverts_locked evmS I (by simpa only [evmS, initState] using hwv)
                  (by rw [hstorage]; exact hlocked))
            · have hunlocked := not_not.mp hlocked
              obtain ⟨_, _, rd1556⟩ := RD.uniswapSwapLockEntered rd1475 hunlocked hperm
                (by simp only [List.length_cons, List.length_nil]; omega)
              have hlockSource := uniswapLockEnterPrefix evmS (swapStore I)
                (by simpa only [evmS, initState] using hwv) (by simp [swapStore]) (hstorage.trans hunlocked)
              let evmL := uniswapLockEnteredState evmS
              have hpost : accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) evmL.accountMap := by
                simpa only [evmL, uniswapLockEnteredState, uniswapUnlockedState, storageStore_accountMap,
                  evmS, initState] using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
              have heL : evmL.executionEnv = I := by
                simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState, storageStore_executionEnv, evmS, initState]
              rcases uniswapSwapOutputGuardRuntimeCases rd1556 (by simp only [List.length_cons, List.length_nil]; omega) with
                ⟨hzero, rdRev⟩ | ⟨hpos, _, _, rd1628⟩
              · exact rdRev.reEquivExecutionRevert hcode hdispatch
                  (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                  (uniswapSwapBodyReverts_outputZero evmS I hlockSource hzero)
              · have houtputSource := uniswapSwapOutputPrefix evmS I hlockSource hpos
                obtain ⟨_, _, rd1645⟩ := uniswapSwapRuntimeReservesLoaded rd1628
                  (by simp only [List.length_cons, List.length_nil]; omega)
                have hreserveSource := uniswapSwapReservePrefix evmS I houtputSource
                have hr0 : uniswapReserve0Word evmL =
                    reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                  mintReserve0Word_initState_eq_evm hAccounts
                have hr1 : uniswapReserve1Word evmL =
                    reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                  mintReserve1Word_initState_eq_evm hAccounts
                have hc0 : UInt256.land (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                    reserve112Mask = reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                  reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
                have hc1 : UInt256.land (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                    reserve112Mask = reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                  reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
                rcases uniswapSwapReserveGuardRuntimeCases rd1645 hc0 hc1
                    (by simp only [List.length_cons, List.length_nil]; omega) with
                  ⟨hnot, rdRev⟩ | ⟨hfit, _, _, rd1735⟩
                · exact rdRev.reEquivExecutionRevert hcode hdispatch
                    (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                    (uniswapSwapBodyReverts_reserveGuard evmS I hreserveSource
                      (by change ¬ ((swapAmount0OutWord I).toNat < (uniswapReserve0Word evmL).toNat ∧
                            (swapAmount1OutWord I).toNat < (uniswapReserve1Word evmL).toNat)
                          rw [hr0, hr1]; exact hnot))
                · have hreserveGuardSource := uniswapSwapReserveGuardPrefix evmS I hreserveSource
                    (by change (swapAmount0OutWord I).toNat < (uniswapReserve0Word evmL).toNat ∧
                          (swapAmount1OutWord I).toNat < (uniswapReserve1Word evmL).toNat
                        rw [hr0, hr1]; exact hfit)
                  obtain ⟨_, _, rd1765⟩ := uniswapSwapRuntimeTokensLoaded rd1735
                    (by simp only [List.length_cons, List.length_nil]; omega)
                  have htokenSource := uniswapSwapTokenPrefix evmS I hreserveGuardSource
                  have ht1clean : UInt256.land
                      (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) solcAddrMask =
                      UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) :=
                    solcAddrMask_clean (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _)
                  have hvalidIff := swapRecipientValid_iff_runtime hpost heL
                  rcases uniswapSwapRecipientGuardRuntimeCases rd1765 ht1clean
                      solcFreePtrMem_size solcFreePtrMem_read64
                      (by simp only [List.length_cons, List.length_nil]; omega) with
                    ⟨hnot, rdRev⟩ | ⟨hvalid, _, _, rd1870⟩
                  · exact rdRev.reEquivExecutionRevert hcode hdispatch
                      (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                      (uniswapSwapBodyReverts_recipientGuard evmS I htokenSource
                        (fun h ↦ hnot (hvalidIff.mp h)))
                  · have hrecipientSource := uniswapSwapRecipientGuardPrefix evmS I htokenSource
                      (hvalidIff.mpr hvalid)
                    obtain ⟨ht0, ht1, hto, ha0, ha1⟩ := swapTokenStore_transferGets evmL I
                    have htarget0 : EVM.address (uniswapAddressAtSlot evmL ⟨6⟩) =
                        AccountAddress.ofUInt256 (UInt256.land
                          (UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) solcAddrMask) := by
                      rw [uniswapAddress_self, uniswapAddressAtSlot_eq_runtime ⟨6⟩ hpost heL]
                      exact congrArg AccountAddress.ofUInt256
                        ((u256_land_comm _ solcAddrMask).trans (u256_land_solcAddrMask_idem_left _)).symm
                    have htarget1 : EVM.address (uniswapAddressAtSlot evmL ⟨7⟩) =
                        AccountAddress.ofUInt256 (UInt256.land
                          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) solcAddrMask) := by
                      rw [uniswapAddress_self, uniswapAddressAtSlot_eq_runtime ⟨7⟩ hpost heL]
                      exact congrArg AccountAddress.ofUInt256
                        ((u256_land_comm _ solcAddrMask).trans (u256_land_solcAddrMask_idem_left _)).symm
                    have hrecipient : UInt256.ofNat (AccountAddress.ofNat (swapToWord I).toNat).val =
                        UInt256.land solcAddrMask (swapToMaskedWord I) := by
                      rw [swapToMaskedWord, u256_land_solcAddrMask_idem_left]
                      exact (keyValueToWord_address _).symm.trans
                        (keyValueToWord_address_ofNat_mask (swapToWord I))
                    rcases uniswapSwapTransfersAnyDepthCases evmL (uniswapAddressAtSlot evmL ⟨6⟩)
                        (uniswapAddressAtSlot evmL ⟨7⟩) (AccountAddress.ofNat (swapToWord I).toNat)
                        rd1870 hpost heL
                        (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                          storageStore_createdAccounts, evmS, initState])
                        (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                          balanceCallStorageStore_sigma0, evmS, initState])
                        (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                          balanceCallStorageStore_genesisBlockHeader, evmS, initState])
                        (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                          balanceCallStorageStore_blocks, evmS, initState])
                        (caller := { contract := contract, locals := swapTokenStore evmL I })
                        rfl ht0 ht1 hto ha0 ha1 htarget0 htarget1 hrecipient hperm
                        safeTransferMemoryReady_initial (by native_decide)
                        (by simp only [List.length_cons, List.length_nil]; omega) with
                      ⟨htransfers, rdRev⟩ | ⟨evmT, σT, cAT, memT, awT, ptrT, dataT, kT, CT,
                        htransfers, haT, hcT, hsT, hgT, hbT, heT, hreadyT, hcapT, rd1904⟩
                    · exact rdRev.reEquivExecutionRevert hcode hdispatch
                        (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                        (uniswapSwapBodyReverts_transfers evmS evmL I _ hrecipientSource htransfers)
                    · have htransferPrefix := execBlock_append hrecipientSource htransfers
                      obtain ⟨htoT, ha0T, ha1T, hbytesT⟩ := swapAfterTransfersFrame_callbackGets evmL I
                      rw [swapDataValue, swapDataBytes_eq_runtimeExtract hoff] at hbytesT
                      have htargetCb : EVM.address (AccountAddress.ofNat (swapToWord I).toNat) =
                          AccountAddress.ofUInt256 (UInt256.land solcAddrMask (swapToMaskedWord I)) := by
                        rw [← hrecipient, accountAddress_roundtrip, uniswapAddress_self]
                      have hlenB : swapDataSize I ≤ 4294967296 := by
                        simpa only [solcLegacyMaxU32] using Nat.le_of_not_gt hlenHuge
                      have hcallbackData : (swapRuntimePayloadPtr I).toNat + (swapDataSizeWord I).toNat ≤ I.calldata.size := by
                        rw [(swapRuntimeWords_eq hoff).2]
                        exact hpayloadLe
                      have hcallbackFit : ptrT.toNat + (swapDataSizeWord I).toNat + 227 < UInt256.size := by
                        have hnum : 128 + 2 * (2 ^ 138 + 227) + 4294967296 + 227 < UInt256.size := by native_decide
                        change ptrT.toNat ≤ 128 + 2 * (2 ^ 138 + 227) at hcapT
                        change ptrT.toNat + swapDataSize I + 227 < UInt256.size
                        omega
                      have hcallbackSmall : (swapDataSizeWord I).toNat + 196 < 2 ^ 64 := by
                        change swapDataSize I + 196 < 2 ^ 64
                        omega
                      rcases uniswapSwapCallbackCases evmT (AccountAddress.ofNat (swapToWord I).toNat)
                          rd1904 haT heT hcT hsT hgT hbT htoT ha0T ha1T hbytesT htargetCb
                          hreadyT hcallbackData hcallbackFit hcallbackSmall hperm
                          (by simp only [List.length_cons, List.length_nil]; omega) with
                        ⟨hcallback, rdRev⟩ | ⟨evmCb, σCb, cACb, memCb, awCb, dataCb, kCb, CCb,
                          hcallback, haCb, hcCb, hsCb, hgCb, hbCb, heCb, hmCb, hgapCb, hawCb, hloCb, hreadCb, rd2091⟩
                      · exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                          (uniswapSwapBodyReverts_callback evmS evmT I _ htransferPrefix hcallback)
                      · have hcallbackPrefix := execBlock_append htransferPrefix (ExecBlock.consNormal hcallback ExecBlock.nil)
                        have ht0Cb : (swapAfterCallbackFrame
                            (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evmL I }
                              (swapAmount0OutWord I) (swapAmount1OutWord I)) (swapDataSizeWord I)).locals.get? "_token0" =
                            some (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
                          rw [swapAfterCallbackFrame_get_ne _ _ _ (by decide),
                            swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]
                          exact ht0
                        have ht1Cb : (swapAfterCallbackFrame
                            (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evmL I }
                              (swapAmount0OutWord I) (swapAmount1OutWord I)) (swapDataSizeWord I)).locals.get? "_token1" =
                            some (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
                          rw [swapAfterCallbackFrame_get_ne _ _ _ (by decide),
                            swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]
                          exact ht1
                        rcases uniswapSwapBalancesCases evmCb (uniswapAddressAtSlot evmL ⟨6⟩)
                            (uniswapAddressAtSlot evmL ⟨7⟩) rd2091 haCb heCb hcCb hsCb hgCb hbCb
                            (by rw [swapAfterCallbackFrame_contract, swapAfterTransfersFrame_contract])
                            ht0Cb ht1Cb htarget0 htarget1 hmCb hgapCb
                            (by have := hreadyT.ptrLo; omega) hawCb hloCb (by omega) hreadCb
                            (by simp only [List.length_cons, List.length_nil]; omega) with
                          ⟨hbalances, rdRev⟩ | ⟨evmB, σB, cAB, memB, awB, dataB, balance0, balance1, kB, CB,
                            hbalances, haB, hcB, hsB, hgB, hbB, heB, hmB, hgapB, hawB, hloB, hreadB, rd2331⟩
                        · exact rdRev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                            (uniswapSwapBodyReverts_balances evmS evmCb I _ hcallbackPrefix hbalances)
                        · have hbalancesPrefix := execBlock_append hcallbackPrefix hbalances
                          obtain ⟨hb0Source, hb1Source, hr0Source, hr1Source, ho0Source, ho1Source⟩ :=
                            swapBeforeInputsFrame_gets evmL I balance0 balance1
                          have hinputs := uniswapSwapInputsSource evmB balance0 balance1
                            (uniswapReserve0Word evmL) (uniswapReserve1Word evmL)
                            (swapAmount0OutWord I) (swapAmount1OutWord I)
                            hb0Source hb1Source hr0Source hr1Source ho0Source ho1Source
                            (by rw [hr0]; exact Nat.le_of_lt hfit.1)
                            (by rw [hr1]; exact Nat.le_of_lt hfit.2)
                          rw [hr0, hr1] at hinputs
                          have hinputsPrefix := execBlock_append hbalancesPrefix hinputs
                          obtain ⟨_, _, rd2374⟩ := RD.uniswapSwapAmount0In rd2331 hc0
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          obtain ⟨_, _, rd2418⟩ := RD.uniswapSwapAmount1In rd2374 hc1
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          rcases uniswapSwapInputGuardRuntimeCases rd2418
                              (by simp only [List.length_cons, List.length_nil]; omega) with
                            ⟨hnotInput, rdRev⟩ | ⟨hposInput, _, _, rd2491⟩
                          · exact rdRev.reEquivExecutionRevert hcode hdispatch
                              (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                              (uniswapSwapBodyReverts_inputGuard evmS evmB I _ _ _ hinputsPrefix hnotInput)
                          · have hinputGuardPrefix := execBlock_append hinputsPrefix
                              (uniswapSwapInputGuardSource evmB _ _ hposInput)
                            let amount0In := swapAmountInWord balance0
                              (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) (swapAmount0OutWord I)
                            let amount1In := swapAmountInWord balance1
                              (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) (swapAmount1OutWord I)
                            obtain ⟨hb0Adj, hb1Adj, hi0Adj, hi1Adj⟩ := swapAfterInputsFrame_adjustmentGets
                              (swapBeforeInputsFrame evmL I balance0 balance1) amount0In amount1In
                              balance0 balance1 hb0Source hb1Source
                            rcases uniswapSwapAdjustmentsCases evmB rd2491 hb0Adj hb1Adj hi0Adj hi1Adj
                                (swapAmountInWord_le _ _ _) (swapAmountInWord_le _ _ _)
                                hmB (by have := hreadyT.ptrLo; omega) hgapB (by omega) hawB hloB hreadB
                                (by simp only [List.length_cons, List.length_nil]; omega) with
                              ⟨hadjustment, rdRev⟩ | ⟨hadjustment, hfitBalance0, hfitBalance1, _, _, rd2570⟩
                            · exact rdRev.reEquivExecutionRevert hcode hdispatch
                                (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                                (uniswapSwapBodyReverts_adjustment evmS evmB I _ hinputGuardPrefix hadjustment)
                            · have hadjustmentPrefix := execBlock_append hinputGuardPrefix hadjustment
                              obtain ⟨hadj0Inv, hadj1Inv, hr0Inv, hr1Inv⟩ :=
                                swapAfterAdjustmentsFrame_invariantGets
                                  (swapAfterInputsFrame (swapBeforeInputsFrame evmL I balance0 balance1) amount0In amount1In)
                                  (swapAdjustedWord balance0 amount0In) (swapAdjustedWord balance1 amount1In)
                                  (uniswapReserve0Word evmL) (uniswapReserve1Word evmL)
                                  (by rw [swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)]; exact hr0Source)
                                  (by rw [swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)]; exact hr1Source)
                              rw [hr0] at hr0Inv
                              rw [hr1] at hr1Inv
                              rcases uniswapSwapInvariantRuntimeCases rd2570 hc0 hc1
                                  hmB (by have := hreadyT.ptrLo; omega) hgapB (by omega) hawB hloB hreadB
                                  (by simp only [List.length_cons, List.length_nil]; omega) with
                                ⟨hnotInvariant, rdRev⟩ | ⟨hvalidInvariant, _, _, rd2701⟩
                              · exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                                  (uniswapSwapBodyReverts_invariant evmS evmB I _ hadjustmentPrefix
                                    (uniswapSwapInvariantSourceRevert evmB _ _ _ _ hadj0Inv hadj1Inv
                                      hr0Inv hr1Inv hc0 hc1 hnotInvariant))
                              · have hrequire := uniswapSwapInvariantSourceSuccess evmB _ _ _ _
                                  hadj0Inv hadj1Inv hr0Inv hr1Inv hc0 hc1 hvalidInvariant
                                have hinvariantPrefix := execBlock_append hadjustmentPrefix
                                  (ExecBlock.consNormal hrequire ExecBlock.nil)
                                obtain ⟨hb0U, hb1U⟩ := swapBeforeUpdateFrame_balances evmL I
                                  balance0 balance1 amount0In amount1In
                                have hargsU := evalExprs_swap_updateArgs evmB balance0 balance1 _ _
                                  hb0U hb1U hr0Inv hr1Inv
                                have hframeU := frame_eq_of_contract
                                  (swapBeforeUpdateFrame_contract evmL I balance0 balance1 amount0In amount1In)
                                rw [hframeU] at hargsU
                                dsimp only [swapBeforeUpdateFrame] at hframeU
                                rw [hframeU] at hinvariantPrefix
                                obtain ⟨_, _, rd6959⟩ := RD.uniswapSwapUpdateEntry rd2701
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                                rcases uniswapUpdateCallRuntimeCases_dynamic (retVar := "_updateResult") evmB rd6959
                                    haB heB hargsU hc0 hc1 hperm hmB
                                    (by have := hreadyT.ptrLo; omega) hgapB (by omega) hawB hloB hreadB
                                    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega) with
                                  ⟨hupdate, rdRev⟩ | ⟨evmU, σU, packedU, kU, CU, hupdate, haU, heU, hcU, rd2712, hsizeU, hreadU⟩
                                · exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload)
                                    (uniswapSwapBodyReverts_updateCall evmS evmB I _ hinvariantPrefix hupdate)
                                · have hmU : 96 ≤ (pairDynamicMem memB ptrT
                                      (uniswapSyncReserve0Word packedU) (uniswapSyncReserve1Word packedU)).size := by
                                    rw [hsizeU]; omega
                                  have hgapU : ptrT.toNat - (pairDynamicMem memB ptrT
                                      (uniswapSyncReserve0Word packedU) (uniswapSyncReserve1Word packedU)).size < USize.size := by
                                    rw [hsizeU]
                                    have hz : 0 < USize.size := lt_usize 0 (by omega)
                                    omega
                                  obtain ⟨hawU, hcoverU⟩ := pairDynamicWords_bounds awB ptrT hawB (by omega)
                                  obtain ⟨_, _, rd2797⟩ := RD.uniswapSwapEmitEvent rd2712 hmU
                                    (by have := hreadyT.ptrLo; omega) hgapU (by omega) hawU hcoverU hreadU hperm
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                  have rdRet := RD.uniswapSwapUnlockAndStop rd2797 hperm
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                  have hbody := uniswapSwapBodyReturns_afterUpdate evmS evmB evmU I _
                                    hinvariantPrefix hupdate
                                    (swapBeforeUpdateFrame_unlocked evmL I balance0 balance1 amount0In amount1In)
                                  have haFinal : accountMapEquiv (sstoreAccountMap I.codeOwner σU ⟨12⟩ ⟨1⟩)
                                      (uniswapLockExitedState evmU).accountMap := by
                                    simpa only [uniswapLockExitedState, uniswapUnlockedState,
                                      storageStore_accountMap, heU] using
                                      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ haU
                                  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                    (uniswapDecode_swap_ok hsz132 hoff hlenWord hlenHuge hpayload) hbody
                                    (by simp only [uniswapLockExitedState, uniswapUnlockedState,
                                      storageStore_createdAccounts, hcU, hcB]) haFinal
                                    (returnEquiv.fallthrough rfl rfl (by native_decide))
          · exact uniswapSwapBodyDecodeFailed_payloadShort hcode hsize hwv hsel hsz132
              hoff hlenWord hlenHuge hpayload hdispatch
      · exact uniswapSwapBodyDecodeFailed_lengthShort hcode hsize hwv hsel hsz132
          hoff (by omega) hdispatch
  · exact uniswapSwapBodyDecodeFailed_headShort hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
