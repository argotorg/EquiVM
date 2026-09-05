import Benchmarks.Dss.Clipper.TakeBodyEntry
import Benchmarks.Dss.Clipper.TakeCallbackSuccessContinuationEquiv
import Benchmarks.Dss.Clipper.TakeCallbackSkipSuccessContinuationEquiv
import Benchmarks.Dss.Clipper.TakeOweGtTabEquiv
import Benchmarks.Dss.Clipper.TakeOweLeTabEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 0 in
theorem clipperTakeBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 22))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hStorageWF : clipperStorageWF σ_evm I) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hcalldataSmall : I.calldata.size < 2 ^ 255 :=
    clipperStorageWF_calldata_lt_sign hStorageWF
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 22) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v) :=
    clipperDispatch_take v hsel
  have hreach := clipperReachTakeBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz164 : 164 ≤ I.calldata.size
  · have hreachHead := clipperTakeX_head_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := clipperSelWord I) (v := v) hpatch hsz164 hsize hreach
    by_cases hoffHuge :
        solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataOffsetWord I).toNat
    · have hdec := clipperDecode_take_none_offset_huge v (I := I)
        hcalldataSmall hsz164 hoffHuge
      have hgtWord :
          UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨1⟩ := by
        exact ugt_one (by
          rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
          simpa [solcMaxLen, solcMaxLenV1] using hoffHuge)
      exact (clipperTakeX_offset_huge (v := v) (g := Sat256.ofUInt256 g) hpatch
        hgtWord hreachHead)
        |>.reEquivDecodingFailed hcode hdispatch hdec
    · have hgtOffsetOk :
          UInt256.gt (clipperTakeDataOffsetWord I) (⟨4294967296⟩ : UInt256) = ⟨0⟩ := by
        exact ugt_zero (by
          have hle : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
            exact Nat.le_of_not_gt (by
              simpa [solcMaxLen, solcMaxLenV1] using hoffHuge)
          rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
          exact hle)
      have hreachOffsetOk := clipperTakeX_offset_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (sel := clipperSelWord I) (v := v) hpatch hgtOffsetOk hreachHead
      by_cases hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size
      · have hgtLenOk := clipperTakeLenWordGt_zero hsize hsz4 hoffHuge hlenWord
        have hreachLenOk := clipperTakeX_length_ok (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := clipperSelWord I) (v := v) hpatch hgtLenOk hreachOffsetOk
        by_cases hlenHuge :
            solcMaxLen DecodeMode.solcV1Signed < (clipperTakeDataLenWord I).toNat
        · have hdec := clipperDecode_take_none_length_huge v (I := I)
            hcalldataSmall hsz164 hoffHuge hlenWord hlenHuge
          exact (clipperTakeX_length_huge (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenHuge hreachLenOk)
            |>.reEquivDecodingFailed hcode hdispatch hdec
        · have hlenMax := hlenHuge
          by_cases hpayloadOk :
              (((I.calldata.toList.drop 4).drop
                ((clipperTakeDataOffsetWord I).toNat + 32)).take
                (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat
          · have hdec := clipperDecode_take_ok v (I := I)
              hcalldataSmall hsz164 hoffHuge hlenWord hlenMax hpayloadOk
            have hpayloadGt := clipperTakePayloadGt_zero hsize hsz4 hoffHuge hlenWord
              hlenMax hpayloadOk
            have hreachDecoded := clipperTakeX_decode_ok (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenMax hpayloadGt
              hreachLenOk
            by_cases hlockedEvm : solcSlotWord σ_evm I ⟨13⟩ = ⟨0⟩
            · obtain ⟨_, _, rd3527⟩ := hreachDecoded
              obtain ⟨_, _, rd3604⟩ := clipperTakeX_lockOpen (cA := cA)
                (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch hlockedEvm rd3527
              obtain ⟨_, _, rd3610⟩ := clipperTakeX_lockStore (cA := cA)
                (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch hperm rd3604
              have hlockWord :
                  solcSlotWord σ_evm I ⟨13⟩ = solcSlotWord σ_solm I ⟨13⟩ := by
                simpa [solcSlotWord] using
                  accountMapEquiv_storage_findD hAccounts I.codeOwner (⟨13⟩ : UInt256) ⟨0⟩
              have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩ := by
                rw [← hlockWord]
                exact hlockedEvm
              let σLockEvm := sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩
              let σLockSolm := sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩
              have hAccountsLock : accountMapEquiv σLockEvm σLockSolm := by
                simpa [σLockEvm, σLockSolm] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
              have hstoppedWord :
                  solcSlotWord σLockEvm I ⟨14⟩ = solcSlotWord σLockSolm I ⟨14⟩ := by
                simpa [solcSlotWord] using
                  accountMapEquiv_storage_findD hAccountsLock I.codeOwner (⟨14⟩ : UInt256) ⟨0⟩
              by_cases hstoppedLt : (solcSlotWord σLockEvm I ⟨14⟩).toNat < 3
              · have hstoppedSolmLt : (solcSlotWord σLockSolm I ⟨14⟩).toNat < 3 := by
                  rw [← hstoppedWord]
                  exact hstoppedLt
                obtain ⟨_, _, rd3694⟩ := clipperTakeX_stoppedOpen (v := v)
                  (σ := σLockEvm) hpatch (by simpa [σLockEvm] using hstoppedLt)
                  (by simpa [σLockEvm] using rd3610)
                have husrWord :
                    clipperTakeSalesUsrWord σLockEvm I =
                      clipperTakeSalesUsrWord σLockSolm I := by
                  unfold clipperTakeSalesUsrWord solcSlotWord
                  rw [accountMapEquiv_storage_findD hAccountsLock I.codeOwner
                    (clipperTakeSalesPackedSlot I) ⟨0⟩]
                by_cases husrEvm : clipperTakeSalesUsrWord σLockEvm I = ⟨0⟩
                · have husrSolm : clipperTakeSalesUsrWord σLockSolm I = ⟨0⟩ := by
                    rw [← husrWord]
                    exact husrEvm
                  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody (config v) (contract v) evmSolm
                        (clipperTakeStore I) (takeTransition v).body .reverted := by
                    simpa [evmSolm, σLockSolm] using
                      (clipperTakeInactiveSourceReverts (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                        hlockedSolm hstoppedSolmLt husrSolm)
                  have hrev := clipperTakeX_usrZero (v := v) (σ := σLockEvm)
                    hpatch husrEvm (by simpa [σLockEvm] using rd3694)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                · have husrSolm : clipperTakeSalesUsrWord σLockSolm I ≠ ⟨0⟩ := by
                    intro hbad
                    exact husrEvm (by rw [husrWord, hbad])
                  obtain ⟨_, _, _rd3821⟩ := clipperTakeX_usrNonzero (v := v)
                    (σ := σLockEvm) hpatch (by simpa [σLockEvm] using husrEvm)
                    (by simpa [σLockEvm] using rd3694)
                  obtain ⟨_, _, _hreachStatus⟩ := clipperTakeX_enterStatus (v := v)
                    (σ := σLockEvm) hpatch _rd3821
                  have hpackedWord :
                      solcSlotWord σLockEvm I (clipperTakeSalesPackedSlot I) =
                        solcSlotWord σLockSolm I (clipperTakeSalesPackedSlot I) := by
                    simpa [solcSlotWord] using
                      accountMapEquiv_storage_findD hAccountsLock I.codeOwner
                        (clipperTakeSalesPackedSlot I) ⟨0⟩
                  have hticStackWord :
                      clipperTakeSalesTicStackWord σLockEvm I =
                        clipperTakeSalesTicStackWord σLockSolm I := by
                    simpa [clipperTakeSalesTicStackWord] using congrArg
                      (fun w =>
                        UInt256.land
                          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)
                          (UInt256.div w (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
                      hpackedWord
                  have hticEVMWord :
                      clipperTakeSalesTicEVMWord
                          (initState cA gh bl σLockSolm σ₀ (Sat256.ofUInt256 g) A I) I =
                        clipperTakeSalesTicStackWord σLockSolm I := by
                    simp [clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                      initState, Solm.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, solcSlotWord, u256_land_comm]
                  have htopWord :
                      clipperTakeSalesTopWord σLockEvm I =
                        clipperTakeSalesTopWord σLockSolm I := by
                    simpa [clipperTakeSalesTopWord, solcSlotWord] using
                      accountMapEquiv_storage_findD hAccountsLock I.codeOwner
                        (clipperTakeSalesTopSlot I) (⟨0⟩ : UInt256)
                  have htopSolmLoad :
                      clipperTakeSalesTopEVMWord
                          (initState cA gh bl σLockSolm σ₀ (Sat256.ofUInt256 g) A I) I =
                        clipperTakeSalesTopWord σLockSolm I := by
                    simp [clipperTakeSalesTopEVMWord, clipperTakeSalesTopWord,
                      initState, Solm.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, solcSlotWord]
                  have hmask96 : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by
                    native_decide
                  have hticLt :
                      (clipperTakeSalesTicStackWord σLockEvm I).toNat <
                        EVM.twoPow 96 := by
                    simpa [clipperTakeSalesTicStackWord, clipperSalesUint96Mask,
                      u256_land_comm] using
                      u256LandMaskToNatLtOfToNat
                        (UInt256.div
                          (solcSlotWord σLockEvm I (clipperTakeSalesPackedSlot I))
                          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                        clipperSalesUint96Mask hmask96
                  have hticClean :
                      UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                          clipperSalesUint96Mask =
                        clipperTakeSalesTicStackWord σLockEvm I := by
                    exact u256LandMaskCleanOfToNat
                      (clipperTakeSalesTicStackWord σLockEvm I)
                      clipperSalesUint96Mask hmask96 hticLt
                  by_cases hlePrice :
                      (clipperTakeSalesTicStackWord σLockEvm I).toNat ≤
                        (UInt256.ofNat I.header.timestamp).toNat
                  · let calcAddr : UInt256 :=
                      UInt256.land (solcSlotWord σLockEvm I ⟨4⟩) solcAddrMask
                    obtain ⟨_, _, rd8502⟩ :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPrice
                        (v := v) hpatch _hreachStatus
                        (by simpa [hticClean] using hlePrice)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    obtain ⟨_, _, rd8549⟩ :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceExtcodesizeGuard
                        (v := v) hpatch (by simpa [calcAddr] using rd8502)
                        (mloadFreePtrValue (by rw [clipperTakeSalesTopHashMem_size I]; decide)
                          (by decide) (clipperTakeSalesTopHashMem_read64 I))
                        (clipperTakeSalesTopHashMem_size I)
                        (clipperTakeSalesTopHashMem_read64 I)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    let evmLockSolm :=
                      Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                    have hcalcSlotSolm :
                        solcSlotWord σLockEvm I ⟨4⟩ = solcSlotWord σLockSolm I ⟨4⟩ := by
                      exact accountMapEquiv_storage_findD (σ := σLockEvm) (τ := σLockSolm)
                        hAccountsLock I.codeOwner ⟨4⟩ (⟨0⟩ : UInt256)
                    have hticSolmLoad :
                        clipperTakeSalesTicEVMWord evmLockSolm I =
                          clipperTakeSalesTicStackWord σLockSolm I := by
                      simp [σLockSolm, evmLockSolm, evmSolm, initState,
                        clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord, storageStore_accountMap, storageStore_executionEnv,
                        u256_land_comm]
                    have htimestampSolm :
                        clipperTimestampWord evmLockSolm = UInt256.ofNat I.header.timestamp := by
                      simp [evmLockSolm, evmSolm, initState, clipperTimestampWord,
                        storageStore_executionEnv]
                    have hlePriceSolm :
                        (clipperTakeSalesTicEVMWord evmLockSolm I).toNat ≤
                          (clipperTimestampWord evmLockSolm).toNat := by
                      simpa [hticSolmLoad, htimestampSolm, ← hticStackWord] using hlePrice
                    have htopSolmLoadLock :
                        clipperTakeSalesTopEVMWord evmLockSolm I =
                          clipperTakeSalesTopWord σLockSolm I := by
                      simp [σLockSolm, evmLockSolm, evmSolm, initState,
                        clipperTakeSalesTopEVMWord, clipperTakeSalesTopWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord, storageStore_accountMap, storageStore_executionEnv]
                    have hticCleanSolm :
                        UInt256.land (clipperTakeSalesTicStackWord σLockSolm I)
                            clipperSalesUint96Mask =
                          clipperTakeSalesTicStackWord σLockSolm I := by
                      rw [← hticStackWord]
                      exact hticClean
                    by_cases hcalcCode :
                        Reasoning.Theory.extCodeSizeWord σLockEvm calcAddr ≠ ⟨0⟩
                    · have hcalcAddrSolm :
                          clipperStatusCalcAddress evmLockSolm =
                            AccountAddress.ofUInt256 calcAddr := by
                        simp [σLockSolm, evmLockSolm, evmSolm, clipperStatusCalcAddress,
                          clipperStatusCalcWord, calcAddr, initState, Solm.EVM.storageLoad,
                          State.lookupAccount, Account.lookupStorage, solcSlotWord,
                          storageStore_accountMap, storageStore_executionEnv, hcalcSlotSolm]
                      have hcalcCodeSolmNE :
                          Reasoning.Theory.extCodeSizeWord σLockSolm calcAddr ≠ ⟨0⟩ := by
                        intro hzero
                        exact hcalcCode (by
                          rw [Reasoning.Theory.extCodeSizeWord_accountMapEquiv
                            hAccountsLock calcAddr]
                          exact hzero)
                      have hcalcCodeSolm :
                          0 < (UInt256.ofNat
                            ((evmLockSolm.lookupAccount
                              (clipperStatusCalcAddress evmLockSolm)).option 0
                              (fun acc => acc.code.size))).toNat := by
                        simpa [σLockSolm, evmLockSolm, evmSolm, State.lookupAccount,
                          initState, storageStore_accountMap] using
                          clipperGetStatusExtCodeSizeWord_ne_zero_lookup_code_pos
                            (σ := σLockSolm) (target := calcAddr)
                            (addr := clipperStatusCalcAddress evmLockSolm)
                            hcalcAddrSolm hcalcCodeSolmNE
                      by_cases hdepth : I.depth.val < 1024
                      · obtain ⟨cA', σ', z, o, A', k8565, C8565, rd8565,
                            hcallPrice, hout⟩ :=
                          RD.clipperStatusPricePostStaticcallFromCurrent
                            (v := v) (cA := cA) (gh := gh) (bl := bl)
                            (σ := σLockEvm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hpatch rd8549
                            (by simp [initState])
                            (by simp [initState])
                            (by simp [initState])
                            (by simpa [calcAddr] using hcalcCode)
                            hdepth
                            (clipperTakeSalesTopHashMem_size I)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        cases z
                        · have hrev :=
                            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
                              (v := v) hpatch (by simpa using rd8565) hout
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, _hPostAccounts⟩ :=
                            typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                          let evmPriceSolm : EVM.State :=
                            { evmLockSolm with
                              accountMap := σ'_solm
                              substate := A'_solm
                              createdAccounts := cA' }
                          have hlockStateSolm :
                              evmLockSolm =
                                initState cA gh bl σLockSolm σ₀
                                  (Sat256.ofUInt256 g) A I := by
                            unfold evmLockSolm evmSolm σLockSolm
                            have hOne : ({ val := 1 } : UInt256) ≠ default := by
                              native_decide
                            cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                              simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                                State.setAccount, sstoreAccountMap, Account.updateStorage,
                                Option.option, hOne, hacc]
                          have hcallPriceSolm :
                              typedCallViaEVM (config v) evmLockSolm
                                (EVM.address (clipperStatusCalcAddress evmLockSolm))
                                "price" 0
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                  .int (Int.ofNat
                                    (UInt256.sub (clipperTimestampWord evmLockSolm)
                                      (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)]
                                (false, evmPriceSolm, o) false := by
                            simpa [evmPriceSolm, hlockStateSolm,
                              σLockSolm, initState, clipperStatusCalcAddress,
                              clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                              clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                              clipperTakeSalesTicStackWord, clipperTimestampWord,
                              Solm.EVM.storageLoad, State.lookupAccount,
                              Account.lookupStorage, solcSlotWord,
                              hcalcSlotSolm, hcalcAddrSolm, htopSolmLoadLock, htopWord,
                              hticSolmLoad, hticStackWord, htimestampSolm, hticClean,
                              hticCleanSolm, u256_land_comm, calcAddr]
                              using hcallPriceSolmRaw
                          have hstatus :
                              let evm0 := initState cA gh bl σ_solm σ₀
                                (Sat256.ofUInt256 g) A I
                              let evmLock :=
                                Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                  ⟨13⟩ ⟨1⟩
                              ExecStmt (config v)
                                { contract := contract v,
                                  locals := clipperTakeLocalsTic evmLock I }
                                evmLock
                                (.internalCall "status"
                                  [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                .reverted := by
                            simpa [evmSolm, evmLockSolm] using
                              clipperTakeStatusCallRevertsPriceCallFailure v
                                (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                I hlePriceSolm hcalcCodeSolm hcallPriceSolm
                          have hbody :
                              ExecTransitionBody (config v) (contract v) evmSolm
                                (clipperTakeStore I) (takeTransition v).body .reverted := by
                            simpa [evmSolm, σLockSolm] using
                              (clipperTakeStatusSourceRevertsOfStatus
                                (cA := cA) (gh := gh) (bl := bl)
                                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                hstatus)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                        · obtain ⟨_, _, rd8583⟩ :=
                            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallSuccessToDecode
                              (v := v) hpatch (by simpa using rd8565)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          by_cases hshortOut : o.size < 32
                          · have hrev :=
                              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeShortReverts
                                (v := v) hpatch (by simpa using rd8583)
                                (clipperTakeSalesTopHashMem_size I)
                                (clipperTakeSalesTopHashMem_read64 I)
                                hshortOut hout
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have hpriceDecode :
                                (config v).externalABI.decode? "price" o = none :=
                              clipperStatusPriceDecode_none_short hshortOut
                            obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, hPostAccounts⟩ :=
                              typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                            let evmPriceSolm : EVM.State :=
                              { evmLockSolm with
                                accountMap := σ'_solm
                                substate := A'_solm
                                createdAccounts := cA' }
                            have hlockStateSolm :
                                evmLockSolm =
                                  initState cA gh bl σLockSolm σ₀
                                    (Sat256.ofUInt256 g) A I := by
                              unfold evmLockSolm evmSolm σLockSolm
                              have hOne : ({ val := 1 } : UInt256) ≠ default := by
                                native_decide
                              cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                                simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                                  State.setAccount, sstoreAccountMap, Account.updateStorage,
                                  Option.option, hOne, hacc]
                            have hcallPriceSolm :
                                typedCallViaEVM (config v) evmLockSolm
                                  (EVM.address (clipperStatusCalcAddress evmLockSolm))
                                  "price" 0
                                  [.int (Int.ofNat
                                    (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                    .int (Int.ofNat
                                      (UInt256.sub (clipperTimestampWord evmLockSolm)
                                        (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)]
                                  (true, evmPriceSolm, o) false := by
                              simpa [evmPriceSolm, hlockStateSolm,
                                σLockSolm, initState, clipperStatusCalcAddress,
                                clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                                clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                                clipperTakeSalesTicStackWord, clipperTimestampWord,
                                Solm.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, solcSlotWord,
                                hcalcSlotSolm, hcalcAddrSolm, htopSolmLoadLock, htopWord,
                                hticSolmLoad, hticStackWord, htimestampSolm, hticClean,
                                hticCleanSolm, u256_land_comm, calcAddr]
                                using hcallPriceSolmRaw
                            have hstatus :
                                let evm0 := initState cA gh bl σ_solm σ₀
                                  (Sat256.ofUInt256 g) A I
                                let evmLock :=
                                  Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                    ⟨13⟩ ⟨1⟩
                                ExecStmt (config v)
                                  { contract := contract v,
                                    locals := clipperTakeLocalsTic evmLock I }
                                  evmLock
                                  (.internalCall "status"
                                    [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                  .reverted := by
                              simpa [evmSolm, evmLockSolm] using
                                clipperTakeStatusCallRevertsPriceDecode v
                                  (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                  I hlePriceSolm hcalcCodeSolm hcallPriceSolm hpriceDecode
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm
                                  (clipperTakeStore I) (takeTransition v).body .reverted := by
                              simpa [evmSolm, σLockSolm] using
                                (clipperTakeStatusSourceRevertsOfStatus
                                  (cA := cA) (gh := gh) (bl := bl)
                                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                  (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                  hstatus)
                            exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                          · have hloOut : 32 ≤ o.size := by
                              omega
                            obtain ⟨_, _, rd8606⟩ :=
                              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeOk
                                (v := v) hpatch rd8583
                                (clipperTakeSalesTopHashMem_size I)
                                (clipperTakeSalesTopHashMem_read64 I)
                                hloOut hout
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            let priceWord : UInt256 := clipperStatusPriceWord o
                            have hdecPrice :
                                (config v).externalABI.decode? "price" o =
                                  some [.int (Int.ofNat priceWord.toNat)] := by
                              simpa [priceWord, clipperStatusPriceValues] using
                                (clipperStatusPriceDecode_ok (v := v) (out := o) hloOut)
                            obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, hPostAccounts⟩ :=
                              typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                            let evmPriceSolm : EVM.State :=
                              { evmLockSolm with
                                accountMap := σ'_solm
                                substate := A'_solm
                                createdAccounts := cA' }
                            have hlockStateSolm :
                                evmLockSolm =
                                  initState cA gh bl σLockSolm σ₀
                                    (Sat256.ofUInt256 g) A I := by
                              unfold evmLockSolm evmSolm σLockSolm
                              have hOne : ({ val := 1 } : UInt256) ≠ default := by
                                native_decide
                              cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                                simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                                  State.setAccount, sstoreAccountMap, Account.updateStorage,
                                  Option.option, hOne, hacc]
                            have hevmPriceAccounts : evmPriceSolm.accountMap = σ'_solm := rfl
                            have hevmPriceSigma0 : evmPriceSolm.σ₀ = σ₀ := by
                              change evmLockSolm.σ₀ = σ₀
                              simpa [initState] using congrArg (fun s : EVM.State => s.σ₀)
                                hlockStateSolm
                            have hevmPriceCreated : evmPriceSolm.createdAccounts = cA' := rfl
                            have hevmPriceGenesis : evmPriceSolm.genesisBlockHeader = gh := by
                              change evmLockSolm.genesisBlockHeader = gh
                              simpa [initState] using congrArg
                                (fun s : EVM.State => s.genesisBlockHeader) hlockStateSolm
                            have hevmPriceBlocks : evmPriceSolm.blocks = bl := by
                              change evmLockSolm.blocks = bl
                              simpa [initState] using congrArg (fun s : EVM.State => s.blocks)
                                hlockStateSolm
                            have hevmPriceEnv : evmPriceSolm.executionEnv = I := by
                              change evmLockSolm.executionEnv = I
                              simpa [initState] using congrArg
                                (fun s : EVM.State => s.executionEnv) hlockStateSolm
                            have hcallPriceSolm :
                                typedCallViaEVM (config v) evmLockSolm
                                  (EVM.address (clipperStatusCalcAddress evmLockSolm))
                                  "price" 0
                                  [.int (Int.ofNat
                                    (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                    .int (Int.ofNat
                                      (UInt256.sub (clipperTimestampWord evmLockSolm)
                                        (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)]
                                  (true, evmPriceSolm, o) false := by
                              simpa [evmPriceSolm, hlockStateSolm,
                                σLockSolm, initState, clipperStatusCalcAddress,
                                clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                                clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                                clipperTakeSalesTicStackWord, clipperTimestampWord,
                                Solm.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, solcSlotWord,
                                hcalcSlotSolm, hcalcAddrSolm, htopSolmLoadLock, htopWord,
                                hticSolmLoad, hticStackWord, htimestampSolm, hticClean,
                                hticCleanSolm, u256_land_comm, calcAddr]
                                using hcallPriceSolmRaw
                            by_cases hleDone :
                                (clipperTakeSalesTicStackWord σLockEvm I).toNat ≤
                                  (UInt256.ofNat I.header.timestamp).toNat
                            · have hleDoneSolm :
                                  (clipperTakeSalesTicEVMWord evmLockSolm I).toNat ≤
                                    (clipperTimestampWord evmPriceSolm).toNat := by
                                simpa [evmPriceSolm, htimestampSolm, hticSolmLoad,
                                  ← hticStackWord] using hleDone
                              by_cases htailLt :
                                  (solcSlotWord σ' I ⟨6⟩).toNat <
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                                        clipperSalesUint96Mask)).toNat
                              · obtain ⟨_, _, rd3852⟩ :=
                                  Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceDoneTailTrue
                                    (v := v) (hpatch := hpatch) rd8606
                                    (by simpa [hticClean] using hleDone) htailLt
                                    (clipperTakeJumpDest3852 v hpatch)
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have hrev :=
                                  RD.clipperTakeStatusDoneTrueReverts (v := v)
                                    (hpatch := hpatch)
                                    (by simpa [priceWord] using rd3852)
                                    (clipperStatusPricePostCallMem_size
                                      (clipperTakeSalesTopWord σLockEvm I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                                          clipperSalesUint96Mask))
                                      (clipperTakeSalesTopHashMem_size I) hout)
                                    (clipperStatusPricePostCallMem_read64
                                      (clipperTakeSalesTopWord σLockEvm I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                                          clipperSalesUint96Mask))
                                      (clipperTakeSalesTopHashMem_size I)
                                      (clipperTakeSalesTopHashMem_read64 I) hout)
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have htailSlotSolm :
                                    solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_solm I ⟨6⟩ := by
                                  exact accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                                    hPostAccounts I.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
                                have hlockOwner :
                                    evmLockSolm.executionEnv.codeOwner = I.codeOwner := by
                                  rw [hlockStateSolm]
                                  simp [initState]
                                have htailSolm :
                                    (clipperStatusTailWord evmPriceSolm).toNat <
                                      (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                        (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat := by
                                  simpa [evmPriceSolm, clipperStatusTailWord,
                                    clipperTimestampWord, Solm.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage, solcSlotWord,
                                    htailSlotSolm, htimestampSolm, hticSolmLoad,
                                    ← hticStackWord, hticClean, hlockOwner] using htailLt
                                have hstatus :
                                    let evm0 := initState cA gh bl σ_solm σ₀
                                      (Sat256.ofUInt256 g) A I
                                    let evmLock :=
                                      Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                        ⟨13⟩ ⟨1⟩
                                    ExecStmt (config v)
                                      { contract := contract v,
                                        locals := clipperTakeLocalsTic evmLock I }
                                      evmLock
                                      (.internalCall "status"
                                        [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                      (.ok
                                        { contract := contract v,
                                          locals := clipperTakeLocalsSt evmLock I true priceWord }
                                        evmPriceSolm) := by
                                  simpa [evmSolm, evmLockSolm] using
                                    clipperTakeStatusCallReturnsDoneTailTrue v
                                      (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                      I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                      hcallPriceSolm hdecPrice hleDoneSolm htailSolm
                                have hbody :
                                    ExecTransitionBody (config v) (contract v) evmSolm
                                      (clipperTakeStore I) (takeTransition v).body .reverted := by
                                  simpa [evmSolm, σLockSolm] using
                                    (clipperTakeStatusDoneTrueSourceReverts
                                      (cA := cA) (gh := gh) (bl := bl)
                                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                      (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                      priceWord hstatus)
                                exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                              · have htailLe :
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                                          clipperSalesUint96Mask)).toNat ≤
                                      (solcSlotWord σ' I ⟨6⟩).toNat := by
                                  exact Nat.le_of_not_gt htailLt
                                have htailSlotSolm :
                                    solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_solm I ⟨6⟩ := by
                                  exact accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                                    hPostAccounts I.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
                                have hlockOwner :
                                    evmLockSolm.executionEnv.codeOwner = I.codeOwner := by
                                  rw [hlockStateSolm]
                                  simp [initState]
                                have htailSolm :
                                    (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                        (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat ≤
                                      (clipperStatusTailWord evmPriceSolm).toNat := by
                                  simpa [evmPriceSolm, clipperStatusTailWord,
                                    clipperTimestampWord, Solm.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage, solcSlotWord,
                                    htailSlotSolm, htimestampSolm, hticSolmLoad,
                                    ← hticStackWord, hticClean, hlockOwner] using htailLe
                                by_cases hmul :
                                    priceWord.toNat * clipperRayWord.toNat < UInt256.size
                                · by_cases htopZero :
                                      clipperTakeSalesTopWord σLockEvm I = ⟨0⟩
                                  · have hinv :=
                                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivDivZeroInvalid
                                        (v := v) (hpatch := hpatch) rd8606
                                        (by simpa [hticClean] using hleDone) htailLe
                                        (by simpa [priceWord] using hmul) htopZero
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have htopSolmZero :
                                        clipperTakeSalesTopEVMWord evmLockSolm I = ⟨0⟩ := by
                                      simpa [htopSolmLoadLock, ← htopWord] using htopZero
                                    have hstatus :
                                        let evm0 := initState cA gh bl σ_solm σ₀
                                          (Sat256.ofUInt256 g) A I
                                        let evmLock :=
                                          Solm.EVM.storageStore evm0
                                            evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                        ExecStmt (config v)
                                          { contract := contract v,
                                            locals := clipperTakeLocalsTic evmLock I }
                                          evmLock
                                          (.internalCall "status"
                                            [.var "tic",
                                              .storage (salesF (.var "id") "top")] "st")
                                          .reverted := by
                                      simpa [evmSolm, evmLockSolm] using
                                        clipperTakeStatusCallRevertsRdivDivZero v
                                          (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                          I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                          hcallPriceSolm hdecPrice hleDoneSolm htailSolm
                                          hmul htopSolmZero
                                    have hbody :
                                        ExecTransitionBody (config v) (contract v) evmSolm
                                          (clipperTakeStore I) (takeTransition v).body
                                          .reverted := by
                                      simpa [evmSolm, σLockSolm] using
                                        (clipperTakeStatusSourceRevertsOfStatus
                                          (cA := cA) (gh := gh) (bl := bl)
                                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                          (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                          hstatus)
                                    exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch
                                      hdec hbody
                                  · obtain ⟨_, _, rd3852⟩ :=
                                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivBranch
                                        (v := v) (hpatch := hpatch) rd8606
                                        (by simpa [hticClean] using hleDone) htailLe
                                        (by simpa [priceWord] using hmul) htopZero
                                        (clipperTakeJumpDest3852 v hpatch)
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    let ratioWord : UInt256 :=
                                      UInt256.div (UInt256.mul priceWord clipperRayWord)
                                        (clipperTakeSalesTopWord σLockEvm I)
                                    let cuspWord : UInt256 := solcSlotWord σ' I ⟨7⟩
                                    let doneWord : UInt256 := UInt256.lt ratioWord cuspWord
                                    have hcuspWordSolm :
                                        cuspWord = clipperStatusCuspWord evmPriceSolm := by
                                      have hslot :=
                                        accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                                          hPostAccounts I.codeOwner ⟨7⟩ (⟨0⟩ : UInt256)
                                      simpa [cuspWord, evmPriceSolm, hlockOwner,
                                        clipperStatusCuspWord, initState,
                                        Solm.EVM.storageLoad, State.lookupAccount,
                                        Account.lookupStorage, solcSlotWord] using hslot
                                    have hratioWordSolm :
                                        ratioWord =
                                          UInt256.div (UInt256.mul priceWord clipperRayWord)
                                            (clipperTakeSalesTopEVMWord evmLockSolm I) := by
                                      simp [ratioWord, htopSolmLoadLock, ← htopWord]
                                    by_cases hratio :
                                        ratioWord.toNat <
                                          (clipperStatusCuspWord evmPriceSolm).toNat
                                    · have hdoneEval :
                                          evalExpr? (config v)
                                            { contract := contract v,
                                              locals := clipperStatusRatioLocals
                                                (clipperTakeSalesTicEVMWord evmLockSolm I)
                                                (clipperTakeSalesTopEVMWord evmLockSolm I)
                                                (UInt256.sub (clipperTimestampWord evmLockSolm)
                                                  (clipperTakeSalesTicEVMWord evmLockSolm I))
                                                priceWord
                                                (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                                  (clipperTakeSalesTicEVMWord evmLockSolm I))
                                                (UInt256.div
                                                  (UInt256.mul priceWord clipperRayWord)
                                                  (clipperTakeSalesTopEVMWord evmLockSolm I)) }
                                            evmPriceSolm
                                            (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                              .ok (.bool true) := by
                                        rw [← hratioWordSolm]
                                        exact clipperEvalStatusRatioCuspCond_true v
                                          evmPriceSolm
                                          (clipperTakeSalesTicEVMWord evmLockSolm I)
                                          (clipperTakeSalesTopEVMWord evmLockSolm I)
                                          (UInt256.sub (clipperTimestampWord evmLockSolm)
                                            (clipperTakeSalesTicEVMWord evmLockSolm I))
                                          priceWord
                                          (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                            (clipperTakeSalesTicEVMWord evmLockSolm I))
                                          ratioWord hratio
                                      have hdoneWordOne : doneWord = ⟨1⟩ := by
                                        unfold doneWord
                                        exact ult_one
                                          (by simpa [cuspWord, hcuspWordSolm] using hratio)
                                      have hrev :=
                                        RD.clipperTakeStatusDoneTrueReverts (v := v)
                                          (hpatch := hpatch)
                                          (by
                                            simpa [priceWord, ratioWord, cuspWord, doneWord,
                                              hdoneWordOne] using rd3852)
                                          (clipperStatusPricePostCallMem_size
                                            (clipperTakeSalesTopWord σLockEvm I)
                                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                              (UInt256.land
                                                (clipperTakeSalesTicStackWord σLockEvm I)
                                                clipperSalesUint96Mask))
                                            (clipperTakeSalesTopHashMem_size I) hout)
                                          (clipperStatusPricePostCallMem_read64
                                            (clipperTakeSalesTopWord σLockEvm I)
                                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                              (UInt256.land
                                                (clipperTakeSalesTicStackWord σLockEvm I)
                                                clipperSalesUint96Mask))
                                            (clipperTakeSalesTopHashMem_size I)
                                            (clipperTakeSalesTopHashMem_read64 I) hout)
                                          (by simp only [List.length_cons, List.length_nil]; omega)
                                      have hstatus :
                                          let evm0 := initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I
                                          let evmLock :=
                                            Solm.EVM.storageStore evm0
                                              evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                          ExecStmt (config v)
                                            { contract := contract v,
                                              locals := clipperTakeLocalsTic evmLock I }
                                            evmLock
                                            (.internalCall "status"
                                              [.var "tic",
                                                .storage (salesF (.var "id") "top")] "st")
                                            (.ok
                                              { contract := contract v,
                                                locals :=
                                                  clipperTakeLocalsSt evmLock I true priceWord }
                                              evmPriceSolm) := by
                                        simpa [evmSolm, evmLockSolm] using
                                          clipperTakeStatusCallReturnsRdivBranch v
                                            (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                            I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                            hcallPriceSolm hdecPrice hleDoneSolm htailSolm
                                            hmul
                                            (by
                                              intro hzero
                                              exact htopZero
                                                (by
                                                  simpa [htopSolmLoadLock, ← htopWord]
                                                    using hzero))
                                            true hdoneEval
                                      have hbody :
                                          ExecTransitionBody (config v) (contract v) evmSolm
                                            (clipperTakeStore I) (takeTransition v).body
                                            .reverted := by
                                        simpa [evmSolm, σLockSolm] using
                                          (clipperTakeStatusDoneTrueSourceReverts
                                            (cA := cA) (gh := gh) (bl := bl)
                                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                            (g := g) v hwv hlockedSolm hstoppedSolmLt
                                            husrSolm priceWord hstatus)
                                      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                                    · have hratioLe :
                                          (clipperStatusCuspWord evmPriceSolm).toNat ≤
                                            ratioWord.toNat := by
                                        exact Nat.le_of_not_gt hratio
                                      have hdoneEval :
                                          evalExpr? (config v)
                                            { contract := contract v,
                                              locals := clipperStatusRatioLocals
                                                (clipperTakeSalesTicEVMWord evmLockSolm I)
                                                (clipperTakeSalesTopEVMWord evmLockSolm I)
                                                (UInt256.sub (clipperTimestampWord evmLockSolm)
                                                  (clipperTakeSalesTicEVMWord evmLockSolm I))
                                                priceWord
                                                (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                                  (clipperTakeSalesTicEVMWord evmLockSolm I))
                                                (UInt256.div
                                                  (UInt256.mul priceWord clipperRayWord)
                                                  (clipperTakeSalesTopEVMWord evmLockSolm I)) }
                                            evmPriceSolm
                                            (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                              .ok (.bool false) := by
                                        rw [← hratioWordSolm]
                                        exact clipperEvalStatusRatioCuspCond_false v
                                          evmPriceSolm
                                          (clipperTakeSalesTicEVMWord evmLockSolm I)
                                          (clipperTakeSalesTopEVMWord evmLockSolm I)
                                          (UInt256.sub (clipperTimestampWord evmLockSolm)
                                            (clipperTakeSalesTicEVMWord evmLockSolm I))
                                          priceWord
                                          (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                            (clipperTakeSalesTicEVMWord evmLockSolm I))
                                          ratioWord hratioLe
                                      have hdoneWordZero : doneWord = ⟨0⟩ := by
                                        unfold doneWord
                                        exact ult_zero
                                          (by
                                            simpa [ratioWord, cuspWord, hcuspWordSolm]
                                              using hratioLe)
                                      have hstatus :
                                          let evm0 := initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I
                                          let evmLock :=
                                            Solm.EVM.storageStore evm0
                                              evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                          ExecStmt (config v)
                                            { contract := contract v,
                                              locals := clipperTakeLocalsTic evmLock I }
                                            evmLock
                                            (.internalCall "status"
                                              [.var "tic",
                                                .storage (salesF (.var "id") "top")] "st")
                                            (.ok
                                              { contract := contract v,
                                                locals :=
                                                  clipperTakeLocalsSt evmLock I false priceWord }
                                              evmPriceSolm) := by
                                        simpa [evmSolm, evmLockSolm] using
                                          clipperTakeStatusCallReturnsRdivBranch v
                                            (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                            I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                            hcallPriceSolm hdecPrice hleDoneSolm htailSolm
                                            hmul
                                            (by
                                              intro hzero
                                              exact htopZero
                                                (by
                                                  simpa [htopSolmLoadLock, ← htopWord]
                                                    using hzero))
                                            false hdoneEval
                                      by_cases hmaxLt :
                                          (clipperTakeMaxWord I).toNat < priceWord.toNat
                                      · have hrev :=
                                          RD.clipperTakeStatusFalseTooExpensiveReverts
                                            (v := v) (hpatch := hpatch)
                                            (by
                                              simpa [priceWord, ratioWord, cuspWord, doneWord,
                                                hdoneWordZero] using rd3852)
                                            hmaxLt
                                            (clipperStatusPricePostCallMem_size
                                              (clipperTakeSalesTopWord σLockEvm I)
                                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                                (UInt256.land
                                                  (clipperTakeSalesTicStackWord σLockEvm I)
                                                  clipperSalesUint96Mask))
                                              (clipperTakeSalesTopHashMem_size I) hout)
                                            (clipperStatusPricePostCallMem_read64
                                              (clipperTakeSalesTopWord σLockEvm I)
                                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                                (UInt256.land
                                                  (clipperTakeSalesTicStackWord σLockEvm I)
                                                  clipperSalesUint96Mask))
                                              (clipperTakeSalesTopHashMem_size I)
                                              (clipperTakeSalesTopHashMem_read64 I) hout)
                                            (by
                                              simp only [List.length_cons, List.length_nil]
                                              omega)
                                        have hbody :
                                            ExecTransitionBody (config v) (contract v) evmSolm
                                              (clipperTakeStore I) (takeTransition v).body
                                              .reverted := by
                                          simpa [evmSolm, σLockSolm] using
                                            (clipperTakeTooExpensiveSourceReverts
                                              (cA := cA) (gh := gh) (bl := bl)
                                              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                              (g := g) v hwv hlockedSolm hstoppedSolmLt
                                              husrSolm priceWord hmaxLt hstatus)
                                        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                                      · have hmaxLe :
                                            priceWord.toNat ≤ (clipperTakeMaxWord I).toNat :=
                                          Nat.le_of_not_gt hmaxLt
                                        obtain ⟨k4007, C4007, rd4007⟩ :=
                                          Benchmarks.Dss.Clipper.RD.clipperTakeStatusFalseMaxOk
                                            (v := v) (hpatch := hpatch)
                                            (by
                                              simpa [priceWord, ratioWord, cuspWord, doneWord,
                                                hdoneWordZero] using rd3852)
                                            hmaxLe
                                            (by
                                              simp only [List.length_cons, List.length_nil]
                                              omega)
                                        have hpostMem64 :
                                            64 ≤
                                              (clipperStatusPricePostCallMem
                                                (clipperTakeSalesTopWord σLockEvm I)
                                                ((UInt256.ofNat I.header.timestamp).sub
                                                  ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                    clipperSalesUint96Mask))
                                                (clipperTakeSalesTopHashMem I) o).size := by
                                          rw [clipperStatusPricePostCallMem_size
                                            (clipperTakeSalesTopWord σLockEvm I)
                                            ((UInt256.ofNat I.header.timestamp).sub
                                              ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                clipperSalesUint96Mask))
                                            (clipperTakeSalesTopHashMem_size I) hout]
                                          norm_num
                                        obtain ⟨k8686, C8686, rd8686⟩ :=
                                          Benchmarks.Dss.Clipper.RD.clipperTakeAfterMaxToMul
                                            (v := v) (hpatch := hpatch) rd4007
                                            hpostMem64 (by
                                              simp only [List.length_cons, List.length_nil]; omega)
                                        let lotE := solcSlotWord σ' I (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)
                                        let sliceE := clipperMinWord (clipperTakeAmtWord I) lotE
                                        by_cases howeMul : priceWord.toNat * sliceE.toNat < UInt256.size
                                        · by_cases hcase :
                                            (solcSlotWord σ' I
                                                (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) +
                                                  ⟨1⟩)).toNat <
                                                (UInt256.mul priceWord sliceE).toNat ∧
                                              Reasoning.Theory.extCodeSizeWord σ'
                                                (clipperTakeVatTarget v) = (⟨0⟩ : UInt256)
                                          · have htab :=
                                              clipperTakePostTabWord_eq (σ := σ') (τ := σ'_solm)
                                                (evm := evmPriceSolm) (I := I)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceSolm])
                                                (by simpa [evmPriceSolm] using hlockOwner)
                                            have hlot :=
                                              clipperTakePostLotWord_eq (σ := σ') (τ := σ'_solm)
                                                (evm := evmPriceSolm) (I := I)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceSolm])
                                                (by simpa [evmPriceSolm] using hlockOwner)
                                            have hbaseMem196 :
                                                (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o).size =
                                                  196 := by
                                              exact
                                                clipperStatusPricePostCallMem_size
                                                  (clipperTakeSalesTopWord σLockEvm I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I) hout
                                            have hbaseRead64 :
                                                (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o).readWithPadding
                                                    64 32 =
                                                  UInt256.toByteArray ⟨128⟩ := by
                                              exact
                                                clipperStatusPricePostCallMem_read64
                                                  (clipperTakeSalesTopWord σLockEvm I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I)
                                                  (clipperTakeSalesTopHashMem_read64 I) hout
                                            have hmem196 :
                                                (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                  (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)).size =
                                                  196 := by
                                              have hsize :=
                                                twoWordHashMem_size_of_ge_64'
                                                  (clipperTakeIdWord I) (⟨12⟩ : UInt256)
                                                  (mem := clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)
                                                  (by rw [hbaseMem196]; norm_num)
                                              rw [hsize, hbaseMem196]
                                            have hread64 :
                                                (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                  (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)).readWithPadding
                                                    64 32 =
                                                  UInt256.toByteArray ⟨128⟩ := by
                                              exact
                                                twoWordHashMem_read64_of_ge_96 (clipperTakeIdWord I)
                                                  (⟨12⟩ : UInt256)
                                                  (by rw [hbaseMem196]; norm_num) hbaseRead64
                                            exact
                                              clipperTakeOweGtTabVatFluxNoCodeRevertEquivFromPostAccounts
                                                (v := v) (hpatch := hpatch) hcode hwv hdispatch hdec
                                                hlockedSolm hstoppedSolmLt husrSolm
                                                (by simpa [sliceE, lotE] using rd8686)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceSolm])
                                                htab hlot (by rfl) hmaxLe howeMul hcase.1
                                                hmem196 hread64 hcase.2
                                                (by
                                                  simp only [List.length_cons, List.length_nil]
                                                  omega)
                                                hstatus
                                          · by_cases hgt :
                                              (solcSlotWord σ' I
                                                  (solcMappingSlot ⟨12⟩
                                                    (clipperTakeIdWord I) + ⟨1⟩)).toNat <
                                                (UInt256.mul priceWord sliceE).toNat
                                            · exact clipperTakeOweGtTabEquiv v hpatch hcode hwv
                                                hdispatch hdec hAccounts hlockedSolm
                                                hstoppedSolmLt husrSolm
                                                (by simpa [sliceE, lotE] using rd8686)
                                                hout (by simpa using hPostAccounts)
                                                hevmPriceAccounts hevmPriceSigma0
                                                hevmPriceCreated hevmPriceGenesis
                                                hevmPriceBlocks hevmPriceEnv hlenMax hoffHuge
                                                hpayloadOk hmaxLe
                                                (by simpa [sliceE, lotE] using howeMul)
                                                (by simpa [sliceE, lotE] using hgt)
                                                hstatus hdepth hperm
                                            · have htab :=
                                                clipperTakePostTabWord_eq (σ := σ')
                                                  (τ := σ'_solm) (evm := evmPriceSolm)
                                                  (I := I) (by simpa using hPostAccounts)
                                                  (by simp [evmPriceSolm])
                                                  (by simpa [evmPriceSolm] using hlockOwner)
                                              have hlot :=
                                                clipperTakePostLotWord_eq (σ := σ')
                                                  (τ := σ'_solm) (evm := evmPriceSolm)
                                                  (I := I) (by simpa using hPostAccounts)
                                                  (by simp [evmPriceSolm])
                                                  (by simpa [evmPriceSolm] using hlockOwner)
                                              have hbaseMem196 :
                                                  (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLockEvm I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o).size =
                                                    196 := by
                                                exact clipperStatusPricePostCallMem_size
                                                  (clipperTakeSalesTopWord σLockEvm I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I) hout
                                              have hbaseRead64 :
                                                  (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLockEvm I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o).readWithPadding
                                                      64 32 = UInt256.toByteArray ⟨128⟩ := by
                                                exact clipperStatusPricePostCallMem_read64
                                                  (clipperTakeSalesTopWord σLockEvm I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I)
                                                  (clipperTakeSalesTopHashMem_read64 I) hout
                                              have hmem196 :
                                                  (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                    (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLockEvm I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o)).size =
                                                    196 := by
                                                have hmemSize := twoWordHashMem_size_of_ge_64'
                                                  (clipperTakeIdWord I) (⟨12⟩ : UInt256)
                                                  (mem := clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLockEvm I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)
                                                  (by rw [hbaseMem196]; norm_num)
                                                rw [hmemSize, hbaseMem196]
                                              have hread64 :
                                                  (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                    (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLockEvm I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLockEvm I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o)).readWithPadding
                                                      64 32 = UInt256.toByteArray ⟨128⟩ := by
                                                exact twoWordHashMem_read64_of_ge_96
                                                  (clipperTakeIdWord I) (⟨12⟩ : UInt256)
                                                  (by rw [hbaseMem196]; norm_num) hbaseRead64
                                              have hlenMaxNat :
                                                  (clipperTakeDataLenWord I).toNat ≤
                                                    4294967296 := by
                                                simpa [solcMaxLen, solcMaxLenV1] using
                                                  Nat.le_of_not_gt hlenMax
                                              have hoffMaxNat :
                                                  (clipperTakeDataOffsetWord I).toNat ≤
                                                    4294967296 := by
                                                simpa [solcMaxLen, solcMaxLenV1] using
                                                  Nat.le_of_not_gt hoffHuge
                                              have hdataStartEq :
                                                  (((⟨32⟩ : UInt256) +
                                                        ((⟨4⟩ : UInt256) +
                                                          clipperTakeDataOffsetWord I)).toNat) =
                                                    32 + (4 +
                                                      (clipperTakeDataOffsetWord I).toNat) := by
                                                rw [uadd_toNat, uadd_toNat]
                                                rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
                                                rw [show (⟨4⟩ : UInt256).toNat = 4 by decide]
                                                nth_rewrite 2 [Nat.mod_eq_of_lt (by
                                                  have hbound :
                                                      4 + 4294967296 < UInt256.size := by
                                                    native_decide
                                                  omega)]
                                                rw [Nat.mod_eq_of_lt (by
                                                  have hbound :
                                                      32 + (4 + 4294967296) <
                                                        UInt256.size := by
                                                    native_decide
                                                  omega)]
                                              exact clipperTakeOweLeTabEquiv v hpatch hcode hwv
                                                hdispatch hdec
                                                (by simpa [sliceE, lotE] using rd8686)
                                                hmem196 hread64
                                                (by simpa using hPostAccounts)
                                                hevmPriceSigma0 hevmPriceCreated
                                                hevmPriceGenesis hevmPriceBlocks hevmPriceEnv
                                                (by rfl) hdataStartEq hlenMaxNat hpayloadOk
                                                (by
                                                  exact solcAddrMask_clean
                                                    (solcAddrMask_result_canonical
                                                      (clipperTakeWhoWord I)))
                                                (by rfl) (by rfl)
                                                (by
                                                  simpa [σLockSolm,
                                                    clipperTakeSalesUsrWord] using
                                                    congrArg
                                                      (fun w => UInt256.land w solcAddrMask)
                                                      hpackedWord)
                                                htab hlot
                                                (by simpa [sliceE, lotE, hlot,
                                                  clipperMinWord_comm])
                                                (by simpa [sliceE, lotE] using howeMul)
                                                (by simpa [sliceE, lotE] using
                                                  Nat.le_of_not_gt hgt)
                                                hlockedSolm hstoppedSolmLt husrSolm hmaxLe
                                                hstatus hdepth hperm
                                        · have hrev :=
                                            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMulRevert
                                              (v := v) (hpatch := hpatch) rd8686
                                              (by simpa [sliceE, lotE] using Nat.le_of_not_gt howeMul)
                                              (by simp only [List.length_cons, List.length_nil]; omega)
                                          have hlot := clipperTakePostLotWord_eq (σ := σ') (τ := σ'_solm) (evm := evmPriceSolm) (I := I)
                                            (by simpa using hPostAccounts) (by simp [evmPriceSolm]) (by simpa [evmPriceSolm] using hlockOwner)
                                          have hsrcHover : UInt256.size ≤
                                              (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceSolm I)
                                                (clipperTakeAmtWord I)).toNat * priceWord.toNat := by
                                            simpa [sliceE, lotE, hlot, clipperMinWord_comm, Nat.mul_comm]
                                              using Nat.le_of_not_gt howeMul
                                          have hbody := by
                                            simpa [evmSolm, σLockSolm] using
                                              (clipperTakeOwe0MulOverflowSourceReverts
                                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                                (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                                                hlockedSolm hstoppedSolmLt husrSolm priceWord hmaxLe
                                                hsrcHover hstatus)
                                          exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                                · have hover :
                                      UInt256.size ≤ priceWord.toNat * clipperRayWord.toNat := by
                                    exact Nat.le_of_not_gt hmul
                                  have hrev :=
                                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivMulRevert
                                      (v := v) (hpatch := hpatch) rd8606
                                      (by simpa [hticClean] using hleDone) htailLe
                                      (by simpa [priceWord] using hover)
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  have hstatus :
                                      let evm0 := initState cA gh bl σ_solm σ₀
                                        (Sat256.ofUInt256 g) A I
                                      let evmLock :=
                                        Solm.EVM.storageStore evm0
                                          evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                      ExecStmt (config v)
                                        { contract := contract v,
                                          locals := clipperTakeLocalsTic evmLock I }
                                        evmLock
                                        (.internalCall "status"
                                          [.var "tic",
                                            .storage (salesF (.var "id") "top")] "st")
                                        .reverted := by
                                    simpa [evmSolm, evmLockSolm] using
                                      clipperTakeStatusCallRevertsRdivMul v
                                        (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                        I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                        hcallPriceSolm hdecPrice hleDoneSolm htailSolm hover
                                  have hbody :
                                      ExecTransitionBody (config v) (contract v) evmSolm
                                        (clipperTakeStore I) (takeTransition v).body
                                        .reverted := by
                                    simpa [evmSolm, σLockSolm] using
                                      (clipperTakeStatusSourceRevertsOfStatus
                                        (cA := cA) (gh := gh) (bl := bl)
                                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                        (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                        hstatus)
                                  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                            · have hltDone :
                                  (UInt256.ofNat I.header.timestamp).toNat <
                                    (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                                      clipperSalesUint96Mask).toNat := by
                                simpa [hticClean] using Nat.lt_of_not_ge hleDone
                              have hrev :=
                                Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForDoneRevert
                                  (v := v) (hpatch := hpatch) rd8606 hltDone
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hltDoneSolm :
                                  (clipperTimestampWord evmPriceSolm).toNat <
                                    (clipperTakeSalesTicEVMWord evmLockSolm I).toNat := by
                                simpa [evmPriceSolm, htimestampSolm, hticSolmLoad,
                                  ← hticStackWord] using Nat.lt_of_not_ge hleDone
                              have hstatus :
                                  let evm0 := initState cA gh bl σ_solm σ₀
                                    (Sat256.ofUInt256 g) A I
                                  let evmLock :=
                                    Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                      ⟨13⟩ ⟨1⟩
                                  ExecStmt (config v)
                                    { contract := contract v,
                                      locals := clipperTakeLocalsTic evmLock I }
                                    evmLock
                                    (.internalCall "status"
                                      [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                    .reverted := by
                                simpa [evmSolm, evmLockSolm] using
                                  clipperTakeStatusCallRevertsAgeForDone v
                                    (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                    I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                    hcallPriceSolm hdecPrice hltDoneSolm
                              have hbody :
                                  ExecTransitionBody (config v) (contract v) evmSolm
                                    (clipperTakeStore I) (takeTransition v).body .reverted := by
                                simpa [evmSolm, σLockSolm] using
                                  (clipperTakeStatusSourceRevertsOfStatus
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                    hstatus)
                              exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                      · have hdepthEq : I.depth = (1024 : Fin 1025) := by
                          have hval : I.depth.val = 1024 := by
                            have hleDepth : I.depth.val ≤ 1024 :=
                              Nat.le_of_lt_succ I.depth.isLt
                            have hgeDepth : 1024 ≤ I.depth.val :=
                              Nat.le_of_not_gt hdepth
                            exact Nat.le_antisymm hleDepth hgeDepth
                          apply Fin.ext
                          simpa using hval
                        obtain ⟨_, _, rd8565⟩ :=
                          RD.clipperStatusPriceCallDepthLimitFromCurrent
                            (v := v) hpatch rd8549
                            (by simpa [calcAddr] using hcalcCode)
                            hdepthEq
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        have hrev :=
                          Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
                            (v := v) hpatch (by simpa using rd8565) (by native_decide)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        let ageForPrice : UInt256 :=
                          UInt256.sub (UInt256.ofNat I.header.timestamp)
                            (UInt256.land (clipperTakeSalesTicStackWord σLockEvm I)
                              clipperSalesUint96Mask)
                        have hdepthInit : evmLockSolm.executionEnv.depth = 1024 := by
                          simpa [evmLockSolm, evmSolm, initState,
                            storageStore_executionEnv] using hdepthEq
                        let evmPriceSolm : EVM.State :=
                          { evmLockSolm with
                            substate :=
                              (evmLockSolm.addAccessedAccount
                                (EVM.address (clipperStatusCalcAddress evmLockSolm))).substate }
                        have hcd :
                            (config v).externalABI.encode? "price"
                              [.int (Int.ofNat
                                (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                .int (Int.ofNat
                                  (UInt256.sub (clipperTimestampWord evmLockSolm)
                                    (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)] =
                              some ((clipperStatusPriceCalldataMem
                                (clipperTakeSalesTopWord σLockEvm I) ageForPrice
                                (clipperTakeSalesTopHashMem I)).readWithPadding 128 68) := by
                          have hcdRaw :
                              (config v).externalABI.encode? "price"
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopWord σLockEvm I).toNat),
                                  .int (Int.ofNat ageForPrice.toNat)] =
                                some ((clipperStatusPriceCalldataMem
                                  (clipperTakeSalesTopWord σLockEvm I) ageForPrice
                                  (clipperTakeSalesTopHashMem I)).readWithPadding 128 68) := by
                            simpa using
                              clipperStatusPriceEncode_eq v
                                (clipperTakeSalesTopWord σLockEvm I) ageForPrice
                                (clipperTakeSalesTopHashMem_size I)
                          have htopEvmSolm :
                              clipperTakeSalesTopEVMWord evmLockSolm I =
                                clipperTakeSalesTopWord σLockEvm I := by
                            rw [htopSolmLoadLock, ← htopWord]
                          have hageForPriceSolm :
                              UInt256.sub (clipperTimestampWord evmLockSolm)
                                  (clipperTakeSalesTicEVMWord evmLockSolm I) =
                                ageForPrice := by
                            simp [ageForPrice, htimestampSolm, hticSolmLoad,
                              ← hticStackWord, hticClean]
                          rw [htopEvmSolm, hageForPriceSolm]
                          exact hcdRaw
                        have hcallPriceSolm :
                            typedCallViaEVM (config v) evmLockSolm
                              (EVM.address (clipperStatusCalcAddress evmLockSolm))
                              "price" 0
                              [.int (Int.ofNat
                                (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                .int (Int.ofNat
                                  (UInt256.sub (clipperTimestampWord evmLockSolm)
                                    (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)]
                              (false, evmPriceSolm, ByteArray.empty) false := by
                          simpa [evmPriceSolm] using
                            (callNotMade_depthLimit (cfg := config v) (evm := evmLockSolm)
                              (tgt := EVM.address (clipperStatusCalcAddress evmLockSolm))
                              (name := "price")
                              (args :=
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopEVMWord evmLockSolm I).toNat),
                                  .int (Int.ofNat
                                    (UInt256.sub (clipperTimestampWord evmLockSolm)
                                      (clipperTakeSalesTicEVMWord evmLockSolm I)).toNat)])
                              (callPerm := false)
                              (calldata :=
                                (clipperStatusPriceCalldataMem
                                  (clipperTakeSalesTopWord σLockEvm I) ageForPrice
                                  (clipperTakeSalesTopHashMem I)).readWithPadding 128 68)
                              hcd hdepthInit)
                        have hstatus :
                            let evm0 := initState cA gh bl σ_solm σ₀
                              (Sat256.ofUInt256 g) A I
                            let evmLock :=
                              Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                ⟨13⟩ ⟨1⟩
                            ExecStmt (config v)
                              { contract := contract v,
                                locals := clipperTakeLocalsTic evmLock I }
                              evmLock
                              (.internalCall "status"
                                [.var "tic", .storage (salesF (.var "id") "top")] "st")
                              .reverted := by
                          simpa [evmSolm, evmLockSolm] using
                            clipperTakeStatusCallRevertsPriceCallFailure v
                              (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                              I (out := ByteArray.empty) hlePriceSolm hcalcCodeSolm
                              hcallPriceSolm
                        have hbody :
                            ExecTransitionBody (config v) (contract v) evmSolm
                              (clipperTakeStore I) (takeTransition v).body .reverted := by
                          simpa [evmSolm, σLockSolm] using
                            (clipperTakeStatusSourceRevertsOfStatus
                              (cA := cA) (gh := gh) (bl := bl)
                              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm hstatus)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                    · have hcalcZero :
                          Reasoning.Theory.extCodeSizeWord σLockEvm calcAddr = ⟨0⟩ :=
                        not_ne_iff.mp hcalcCode
                      have hrev :=
                        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceNoCode
                          (v := v) hpatch rd8549
                          (by simpa [calcAddr] using hcalcZero)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hcalcAddrSolm :
                          clipperStatusCalcAddress evmLockSolm =
                            AccountAddress.ofUInt256 calcAddr := by
                        simp [σLockSolm, evmLockSolm, evmSolm, clipperStatusCalcAddress,
                          clipperStatusCalcWord, calcAddr, initState, Solm.EVM.storageLoad,
                          State.lookupAccount, Account.lookupStorage, solcSlotWord,
                          storageStore_accountMap, storageStore_executionEnv, hcalcSlotSolm]
                      have hcalcZeroSolm :
                          Reasoning.Theory.extCodeSizeWord σLockSolm calcAddr = ⟨0⟩ := by
                        rw [← Reasoning.Theory.extCodeSizeWord_accountMapEquiv
                          hAccountsLock calcAddr]
                        exact hcalcZero
                      have hnoCodeSolm :
                          (UInt256.ofNat
                            ((evmLockSolm.lookupAccount
                              (clipperStatusCalcAddress evmLockSolm)).option 0
                              (fun acc => acc.code.size))).toNat = 0 := by
                        rw [hcalcAddrSolm]
                        unfold Reasoning.Theory.extCodeSizeWord at hcalcZeroSolm
                        simp [evmLockSolm, evmSolm, State.lookupAccount, initState,
                          storageStore_accountMap] at hcalcZeroSolm ⊢
                        cases hacc : σLockSolm.find? (AccountAddress.ofUInt256 calcAddr) with
                        | none =>
                            native_decide
                        | some acc =>
                            simp [hacc] at hcalcZeroSolm ⊢
                            exact congrArg UInt256.toNat hcalcZeroSolm
                      have hstatus :
                          let evm0 := initState cA gh bl σ_solm σ₀
                            (Sat256.ofUInt256 g) A I
                          let evmLock :=
                            Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                          ExecStmt (config v)
                            { contract := contract v,
                              locals := clipperTakeLocalsTic evmLock I }
                            evmLock
                            (.internalCall "status"
                              [.var "tic", .storage (salesF (.var "id") "top")] "st")
                            .reverted := by
                        simpa [evmSolm, evmLockSolm] using
                          clipperTakeStatusCallRevertsPriceNoCode v evmLockSolm I
                            hlePriceSolm hnoCodeSolm
                      have hbody :
                          ExecTransitionBody (config v) (contract v) evmSolm
                            (clipperTakeStore I) (takeTransition v).body .reverted := by
                        simpa [evmSolm, σLockSolm] using
                          (clipperTakeStatusSourceRevertsOfStatus
                            (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            v hwv hlockedSolm hstoppedSolmLt husrSolm hstatus)
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                  · have hltEvm :
                        (UInt256.ofNat I.header.timestamp).toNat <
                          (clipperTakeSalesTicStackWord σLockEvm I).toNat := by
                      omega
                    have hltSolm :
                        (UInt256.ofNat I.header.timestamp).toNat <
                          (clipperTakeSalesTicStackWord σLockSolm I).toNat := by
                      rw [← hticStackWord]
                      exact hltEvm
                    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    let evmLockSolm :=
                      Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                    have hltLoad :
                        (clipperTimestampWord evmLockSolm).toNat <
                          (clipperTakeSalesTicEVMWord evmLockSolm I).toNat := by
                      simpa [evmLockSolm, evmSolm, clipperTimestampWord,
                        clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                        initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                        storageStore_accountMap, storageStore_executionEnv, u256_land_comm]
                        using hltSolm
                    have hstatus :
                        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                        let evmLock :=
                          Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                        ExecStmt (config v)
                          { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
                          evmLock
                          (.internalCall "status"
                            [.var "tic", .storage (salesF (.var "id") "top")] "st")
                          .reverted := by
                      simpa [evmSolm, evmLockSolm] using
                        clipperTakeStatusCallRevertsAgeForPrice v evmLockSolm I hltLoad
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm
                          (clipperTakeStore I) (takeTransition v).body .reverted := by
                      simpa [evmSolm, σLockSolm] using
                        (clipperTakeStatusSourceRevertsOfStatus
                          (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          v hwv hlockedSolm hstoppedSolmLt husrSolm hstatus)
                    have hrev :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPriceRevert
                        (v := v) hpatch _hreachStatus
                        (by simpa [hticClean] using hltEvm)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
              · have hstoppedEvmGe : 3 ≤ (solcSlotWord σLockEvm I ⟨14⟩).toNat := by
                  omega
                have hstoppedSolmGe : 3 ≤ (solcSlotWord σLockSolm I ⟨14⟩).toNat := by
                  rw [← hstoppedWord]
                  exact hstoppedEvmGe
                let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm
                      (clipperTakeStore I) (takeTransition v).body .reverted := by
                  simpa [evmSolm, σLockSolm] using
                    (clipperTakeStoppedSourceReverts (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                      hlockedSolm hstoppedSolmGe)
                have hrev := clipperTakeX_stoppedClosed (v := v) (σ := σLockEvm)
                  hpatch (by simpa [σLockEvm] using hstoppedEvmGe)
                  (by simpa [σLockEvm] using rd3610)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
            · have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ ≠ ⟨0⟩ := by
                have hword :
                    solcSlotWord σ_evm I ⟨13⟩ = solcSlotWord σ_solm I ⟨13⟩ :=
                  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨13⟩ ⟨0⟩
                intro hbad
                exact hlockedEvm (by rw [hword, hbad])
              have hbody :
                  ExecTransitionBody (config v) (contract v)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (clipperTakeStore I) (takeTransition v).body .reverted :=
                clipperTakeBodyRevertsLocked (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                  hlockedSolm
              obtain ⟨_, _, rd3527⟩ := hreachDecoded
              have hrev := clipperTakeX_locked (cA := cA) (σ := σ_evm) (I := I)
                (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch hlockedEvm rd3527
              exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
          · have hpayloadShort :
                (((I.calldata.toList.drop 4).drop
                  ((clipperTakeDataOffsetWord I).toNat + 32)).take
                  (clipperTakeDataLenWord I).toNat).length ≠
                    (clipperTakeDataLenWord I).toNat := hpayloadOk
            have hdec := clipperDecode_take_none_payload_short v (I := I)
              hcalldataSmall hsz164 hoffHuge hlenWord hlenMax hpayloadShort
            have hpayloadGt := clipperTakePayloadGt_one hsize hsz4 hoffHuge hlenWord
              hlenMax hpayloadShort
            exact (clipperTakeX_payload_short (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenMax hpayloadGt hreachLenOk)
              |>.reEquivDecodingFailed hcode hdispatch hdec
      · have hlenShort : I.calldata.size <
            4 + (clipperTakeDataOffsetWord I).toNat + 32 := by
          omega
        have hdec := clipperDecode_take_none_length_short v (I := I)
          hcalldataSmall hsz164 hoffHuge hlenShort
        have hgtLen := clipperTakeLenWordGt_one hsize hsz4 hoffHuge hlenShort
        exact (clipperTakeX_length_short (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := clipperSelWord I) (v := v) hpatch hgtLen hreachOffsetOk)
          |>.reEquivDecodingFailed hcode hdispatch hdec
  · have hshort : I.calldata.size < 164 := by omega
    have hdec := clipperDecode_take_none_short v (I := I) hsz4 hshort
    exact (clipperTakeX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4 hsize
      hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdec

end Benchmarks.Dss.Clipper
