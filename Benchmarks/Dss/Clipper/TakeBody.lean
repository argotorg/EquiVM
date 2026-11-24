import Benchmarks.Dss.Clipper.TakeBodyEntry
import Benchmarks.Dss.Clipper.TakeCallbackSuccessContinuationEquiv
import Benchmarks.Dss.Clipper.TakeCallbackSkipSuccessContinuationEquiv
import Benchmarks.Dss.Clipper.TakeOweGtTabEquiv
import Benchmarks.Dss.Clipper.TakeOweLeTabEquiv

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 0 in
theorem clipperTakeBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 22))
    (hStorageWF : clipperStorageWF σ I) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hcalldataSmall : I.calldata.size < 2 ^ 255 :=
    clipperStorageWF_calldata_lt_sign hStorageWF
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 22) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some takeTransition :=
    clipperDispatch_take hsel
  have hreach := clipperReachTakeBody (fork := fork)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz164 : 164 ≤ I.calldata.size
  · have hreachHead := clipperTakeX_head_ok
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (sel := clipperSelWord I) (v := v) hpatch hsz164 hsize hreach
    by_cases hoffHuge :
        solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat
    · have hdec := clipperDecode_take_none_offset_huge (I := I)
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
      have hreachOffsetOk := clipperTakeX_offset_ok
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (sel := clipperSelWord I) (v := v) hpatch hgtOffsetOk hreachHead
      by_cases hlenWord : 4 + (clipperTakeDataOffsetWord I).toNat + 32 ≤ I.calldata.size
      · have hgtLenOk := clipperTakeLenWordGt_zero hsize hsz4 hoffHuge hlenWord
        have hreachLenOk := clipperTakeX_length_ok
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := clipperSelWord I) (v := v) hpatch hgtLenOk hreachOffsetOk
        by_cases hlenHuge :
            solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat
        · have hdec := clipperDecode_take_none_length_huge (I := I)
            hcalldataSmall hsz164 hoffHuge hlenWord hlenHuge
          exact (clipperTakeX_length_huge
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenHuge hreachLenOk)
            |>.reEquivDecodingFailed hcode hdispatch hdec
        · have hlenMax := hlenHuge
          by_cases hpayloadOk :
              (((I.calldata.toList.drop 4).drop
                ((clipperTakeDataOffsetWord I).toNat + 32)).take
                (clipperTakeDataLenWord I).toNat).length = (clipperTakeDataLenWord I).toNat
          · have hdec := clipperDecode_take_ok (I := I)
              hcalldataSmall hsz164 hoffHuge hlenWord hlenMax hpayloadOk
            have hpayloadGt := clipperTakePayloadGt_zero hsize hsz4 hoffHuge hlenWord
              hlenMax hpayloadOk
            have hreachDecoded := clipperTakeX_decode_ok
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenMax hpayloadGt
              hreachLenOk
            by_cases hlockedEvm : solcSlotWord σ I ⟨13⟩ = ⟨0⟩
            · obtain ⟨_, _, rd3527⟩ := hreachDecoded
              obtain ⟨_, _, rd3604⟩ := clipperTakeX_lockOpen
                (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch hlockedEvm rd3527
              have hfirstWrite := clipperTakeX_lockStoreSplit
                (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch rd3604
              rcases hfirstWrite with ⟨hperm, _, _, rd3610⟩ | ⟨hperm, hstatic⟩
              swap
              · exact hstatic.reEquivStaticHalt hcode hdispatch hdec
                  ((clipperTakeStoppedSourceRevertsSplit v hwv hlockedEvm).2 hperm)
              let σLock := sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩
              by_cases hstoppedLt : (solcSlotWord σLock I ⟨14⟩).toNat < 3
              · obtain ⟨_, _, rd3694⟩ := clipperTakeX_stoppedOpen (v := v)
                  (σ := σLock) hpatch (by simpa [σLock] using hstoppedLt)
                  (by simpa [σLock] using rd3610)
                by_cases husrEvm : clipperTakeSalesUsrWord σLock I = ⟨0⟩
                · let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody fork config contract evmStele
                        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                    simpa [evmStele, σLock] using
                      (clipperTakeInactiveSourceReverts (fork := fork) (hperm := by assumption)
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                        hlockedEvm hstoppedLt husrEvm)
                  have hrev := clipperTakeX_usrZero (v := v) (σ := σLock)
                    hpatch husrEvm (by simpa [σLock] using rd3694)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                · obtain ⟨_, _, _rd3821⟩ := clipperTakeX_usrNonzero (v := v)
                    (σ := σLock) hpatch (by simpa [σLock] using husrEvm)
                    (by simpa [σLock] using rd3694)
                  obtain ⟨_, _, _hreachStatus⟩ := clipperTakeX_enterStatus (v := v)
                    (σ := σLock) hpatch _rd3821
                  have hpackedWord :
                      solcSlotWord σLock I (clipperTakeSalesPackedSlot I) =
                        solcSlotWord σLock I (clipperTakeSalesPackedSlot I) := rfl
                  have hticStackWord :
                      clipperTakeSalesTicStackWord σLock I =
                        clipperTakeSalesTicStackWord σLock I := by
                    simpa [clipperTakeSalesTicStackWord] using congrArg
                      (fun w =>
                        UInt256.land
                          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)
                          (UInt256.div w (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))
                      hpackedWord
                  have hticEVMWord :
                      clipperTakeSalesTicEVMWord
                          (initState σLock σ₀ (Sat256.ofUInt256 g) A I) I =
                        clipperTakeSalesTicStackWord σLock I := by
                    simp [clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                      initState, Stele.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, solcSlotWord, u256_land_comm]
                  have htopWord :
                      clipperTakeSalesTopWord σLock I =
                        clipperTakeSalesTopWord σLock I := rfl
                  have htopSteleLoad :
                      clipperTakeSalesTopEVMWord
                          (initState σLock σ₀ (Sat256.ofUInt256 g) A I) I =
                        clipperTakeSalesTopWord σLock I := by
                    simp [clipperTakeSalesTopEVMWord, clipperTakeSalesTopWord,
                      initState, Stele.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, solcSlotWord]
                  have hmask96 : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by
                    native_decide
                  have hticLt :
                      (clipperTakeSalesTicStackWord σLock I).toNat <
                        EVM.twoPow 96 := by
                    simpa [clipperTakeSalesTicStackWord, clipperSalesUint96Mask,
                      u256_land_comm] using
                      u256LandMaskToNatLtOfToNat
                        (UInt256.div
                          (solcSlotWord σLock I (clipperTakeSalesPackedSlot I))
                          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                        clipperSalesUint96Mask hmask96
                  have hticClean :
                      UInt256.land (clipperTakeSalesTicStackWord σLock I)
                          clipperSalesUint96Mask =
                        clipperTakeSalesTicStackWord σLock I := by
                    exact u256LandMaskCleanOfToNat
                      (clipperTakeSalesTicStackWord σLock I)
                      clipperSalesUint96Mask hmask96 hticLt
                  by_cases hlePrice :
                      (clipperTakeSalesTicStackWord σLock I).toNat ≤
                        (UInt256.ofNat I.header.timestamp).toNat
                  · let calcAddr : UInt256 :=
                      UInt256.land (solcSlotWord σLock I ⟨4⟩) solcAddrMask
                    obtain ⟨_, _, rd8502⟩ :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPrice
                        (v := v) hpatch _hreachStatus
                        (by simpa [hticClean] using hlePrice)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    obtain ⟨_, _, rd8549⟩ :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceExtcodesizeGuard
                        (v := v) hpatch (by simpa [calcAddr] using rd8502)
                        (mloadFreePtrValue (by rw [clipperTakeSalesTopHashMem_size I]; decide) (clipperTakeSalesTopHashMem_read64 I))
                        (clipperTakeSalesTopHashMem_size I)
                        (clipperTakeSalesTopHashMem_read64 I)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                    let evmLockStele :=
                      Stele.EVM.storageStore evmStele evmStele.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                    have hcalcSlotStele :
                        solcSlotWord σLock I ⟨4⟩ = solcSlotWord σLock I ⟨4⟩ := rfl
                    have hticSteleLoad :
                        clipperTakeSalesTicEVMWord evmLockStele I =
                          clipperTakeSalesTicStackWord σLock I := by
                      simp [σLock, evmLockStele, evmStele, initState,
                        clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord, storageStore_accountMap, storageStore_executionEnv,
                        u256_land_comm]
                    have htimestampStele :
                        clipperTimestampWord evmLockStele = UInt256.ofNat I.header.timestamp := by
                      simp [evmLockStele, evmStele, initState, clipperTimestampWord,
                        storageStore_executionEnv]
                    have hlePriceStele :
                        (clipperTakeSalesTicEVMWord evmLockStele I).toNat ≤
                          (clipperTimestampWord evmLockStele).toNat := by
                      simpa [hticSteleLoad, htimestampStele, ← hticStackWord] using hlePrice
                    have htopSteleLoadLock :
                        clipperTakeSalesTopEVMWord evmLockStele I =
                          clipperTakeSalesTopWord σLock I := by
                      simp [σLock, evmLockStele, evmStele, initState,
                        clipperTakeSalesTopEVMWord, clipperTakeSalesTopWord,
                        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord, storageStore_accountMap, storageStore_executionEnv]
                    have hticCleanStele :
                        UInt256.land (clipperTakeSalesTicStackWord σLock I)
                            clipperSalesUint96Mask =
                          clipperTakeSalesTicStackWord σLock I := by
                      rw [← hticStackWord]
                      exact hticClean
                    by_cases hcalcCode :
                        Reasoning.Theory.extCodeSizeWord σLock calcAddr ≠ ⟨0⟩
                    · have hcalcAddrStele :
                          clipperStatusCalcAddress evmLockStele =
                            AccountAddress.ofUInt256 calcAddr := by
                        simp [σLock, evmLockStele, evmStele, clipperStatusCalcAddress,
                          clipperStatusCalcWord, calcAddr, initState, Stele.EVM.storageLoad,
                          State.lookupAccount, Account.lookupStorage, solcSlotWord,
                          storageStore_accountMap, storageStore_executionEnv, hcalcSlotStele]
                      have hcalcCodeSteleNE :
                          Reasoning.Theory.extCodeSizeWord σLock calcAddr ≠ ⟨0⟩ := by
                        exact hcalcCode
                      have hcalcCodeStele :
                          0 < (UInt256.ofNat
                            ((evmLockStele.lookupAccount
                              (clipperStatusCalcAddress evmLockStele)).option 0
                              (fun acc => acc.code.size))).toNat := by
                        simpa [σLock, evmLockStele, evmStele, State.lookupAccount,
                          initState, storageStore_accountMap] using
                          extCodeSizeWord_ne_zero_lookup_code_pos
                            (σ := σLock) (target := calcAddr)
                            (addr := clipperStatusCalcAddress evmLockStele)
                            hcalcAddrStele hcalcCodeSteleNE
                      by_cases hdepth : I.depth.val < 1024
                      · obtain ⟨σ', z, o, A', k8565, C8565, rd8565,
                            hcallPrice, hout⟩ :=
                          RD.clipperStatusPricePostStaticcallFromCurrent
                            (v := v)
                            (σ := σLock) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hpatch rd8549
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
                          have hcallPriceSteleRaw := hcallPrice
                          let evmPriceStele : EVM.State :=
                            { evmLockStele with accountMap := σ', substate := A' }
                          have hlockStateStele :
                              evmLockStele =
                                initState σLock σ₀
                                  (Sat256.ofUInt256 g) A I := by
                            unfold evmLockStele evmStele σLock
                            have hOne : ({ val := 1 } : UInt256) ≠ default := by
                              native_decide
                            cases hacc : σ.get? I.codeOwner <;>
                              simp [-Std.ExtTreeMap.get?_eq_getElem?, initState, Stele.EVM.storageStore, State.lookupAccount,
                                State.setAccount, sstoreAccountMap, Account.updateStorage,
                                Option.option, hOne, hacc]
                          have hcallPriceStele :
                              typedCallViaEVM fork config evmLockStele
                                (EVM.address (clipperStatusCalcAddress evmLockStele))
                                "price" 0
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                  .int (Int.ofNat
                                    (UInt256.sub (clipperTimestampWord evmLockStele)
                                      (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)]
                                (false, evmPriceStele, o) false := by
                            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmPriceStele, hlockStateStele,
                              σLock, initState, clipperStatusCalcAddress,
                              clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                              clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                              clipperTakeSalesTicStackWord, clipperTimestampWord,
                              Stele.EVM.storageLoad, State.lookupAccount,
                              Account.lookupStorage, solcSlotWord,
                              hcalcSlotStele, hcalcAddrStele, htopSteleLoadLock, htopWord,
                              hticSteleLoad, hticStackWord, htimestampStele, hticClean,
                              hticCleanStele, u256_land_comm, calcAddr]
                              using hcallPriceSteleRaw
                          have hstatus :
                              let evm0 := initState σ σ₀
                                (Sat256.ofUInt256 g) A I
                              let evmLock :=
                                Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                  ⟨13⟩ ⟨1⟩
                              ExecStmt fork config
                                { contract := contract,
                                  locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                evmLock
                                (.internalCall "status"
                                  [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                .reverted := by
                            simpa [evmStele, evmLockStele] using
                              clipperTakeStatusCallRevertsPriceCallFailure v
                                (evm := evmLockStele) (evmPrice := evmPriceStele)
                                I hlePriceStele hcalcCodeStele hcallPriceStele
                          have hbody :
                              ExecTransitionBody fork config contract evmStele
                                (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                            simpa [evmStele, σLock] using
                              (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                (g := g) v hwv hlockedEvm hstoppedLt husrEvm
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
                                config.externalABI.decode? "price" o = none :=
                              clipperStatusPriceDecode_none_short hshortOut
                            have hcallPriceSteleRaw := hcallPrice
                            let evmPriceStele : EVM.State :=
                              { evmLockStele with accountMap := σ', substate := A' }
                            have hPostAccounts : Eq σ' evmPriceStele.accountMap := rfl
                            have hlockStateStele :
                                evmLockStele =
                                  initState σLock σ₀
                                    (Sat256.ofUInt256 g) A I := by
                              unfold evmLockStele evmStele σLock
                              have hOne : ({ val := 1 } : UInt256) ≠ default := by
                                native_decide
                              cases hacc : σ.get? I.codeOwner <;>
                                simp [-Std.ExtTreeMap.get?_eq_getElem?, initState, Stele.EVM.storageStore, State.lookupAccount,
                                  State.setAccount, sstoreAccountMap, Account.updateStorage,
                                  Option.option, hOne, hacc]
                            have hcallPriceStele :
                                typedCallViaEVM fork config evmLockStele
                                  (EVM.address (clipperStatusCalcAddress evmLockStele))
                                  "price" 0
                                  [.int (Int.ofNat
                                    (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                    .int (Int.ofNat
                                      (UInt256.sub (clipperTimestampWord evmLockStele)
                                        (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)]
                                  (true, evmPriceStele, o) false := by
                              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmPriceStele, hlockStateStele,
                                σLock, initState, clipperStatusCalcAddress,
                                clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                                clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                                clipperTakeSalesTicStackWord, clipperTimestampWord,
                                Stele.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, solcSlotWord,
                                hcalcSlotStele, hcalcAddrStele, htopSteleLoadLock, htopWord,
                                hticSteleLoad, hticStackWord, htimestampStele, hticClean,
                                hticCleanStele, u256_land_comm, calcAddr]
                                using hcallPriceSteleRaw
                            have hstatus :
                                let evm0 := initState σ σ₀
                                  (Sat256.ofUInt256 g) A I
                                let evmLock :=
                                  Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                    ⟨13⟩ ⟨1⟩
                                ExecStmt fork config
                                  { contract := contract,
                                    locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                  evmLock
                                  (.internalCall "status"
                                    [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                  .reverted := by
                              simpa [evmStele, evmLockStele] using
                                clipperTakeStatusCallRevertsPriceDecode v
                                  (evm := evmLockStele) (evmPrice := evmPriceStele)
                                  I hlePriceStele hcalcCodeStele hcallPriceStele hpriceDecode
                            have hbody :
                                ExecTransitionBody fork config contract evmStele
                                  (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                              simpa [evmStele, σLock] using
                                (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                  (g := g) v hwv hlockedEvm hstoppedLt husrEvm
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
                                config.externalABI.decode? "price" o =
                                  some [.int (Int.ofNat priceWord.toNat)] := by
                              simpa [priceWord, clipperStatusPriceValues] using
                                (clipperStatusPriceDecode_ok (out := o) hloOut)
                            have hcallPriceSteleRaw := hcallPrice
                            let evmPriceStele : EVM.State :=
                              { evmLockStele with accountMap := σ', substate := A' }
                            have hPostAccounts : Eq σ' evmPriceStele.accountMap := rfl
                            have hlockStateStele :
                                evmLockStele =
                                  initState σLock σ₀
                                    (Sat256.ofUInt256 g) A I := by
                              unfold evmLockStele evmStele σLock
                              have hOne : ({ val := 1 } : UInt256) ≠ default := by
                                native_decide
                              cases hacc : σ.get? I.codeOwner <;>
                                simp [-Std.ExtTreeMap.get?_eq_getElem?, initState, Stele.EVM.storageStore, State.lookupAccount,
                                  State.setAccount, sstoreAccountMap, Account.updateStorage,
                                  Option.option, hOne, hacc]
                            have hevmPriceAccounts : evmPriceStele.accountMap = σ' := rfl
                            have hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀ := by
                              change evmLockStele.σ₀ = σ₀
                              simpa [initState] using congrArg (fun s : EVM.State => s.σ₀)
                                hlockStateStele
                            have hevmPriceEnv : evmPriceStele.executionEnv = I := by
                              change evmLockStele.executionEnv = I
                              simpa [initState] using congrArg
                                (fun s : EVM.State => s.executionEnv) hlockStateStele
                            have hcallPriceStele :
                                typedCallViaEVM fork config evmLockStele
                                  (EVM.address (clipperStatusCalcAddress evmLockStele))
                                  "price" 0
                                  [.int (Int.ofNat
                                    (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                    .int (Int.ofNat
                                      (UInt256.sub (clipperTimestampWord evmLockStele)
                                        (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)]
                                  (true, evmPriceStele, o) false := by
                              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmPriceStele, hlockStateStele,
                                σLock, initState, clipperStatusCalcAddress,
                                clipperStatusCalcWord, clipperTakeSalesTopEVMWord,
                                clipperTakeSalesTopWord, clipperTakeSalesTicEVMWord,
                                clipperTakeSalesTicStackWord, clipperTimestampWord,
                                Stele.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, solcSlotWord,
                                hcalcSlotStele, hcalcAddrStele, htopSteleLoadLock, htopWord,
                                hticSteleLoad, hticStackWord, htimestampStele, hticClean,
                                hticCleanStele, u256_land_comm, calcAddr]
                                using hcallPriceSteleRaw
                            by_cases hleDone :
                                (clipperTakeSalesTicStackWord σLock I).toNat ≤
                                  (UInt256.ofNat I.header.timestamp).toNat
                            · have hleDoneStele :
                                  (clipperTakeSalesTicEVMWord evmLockStele I).toNat ≤
                                    (clipperTimestampWord evmPriceStele).toNat := by
                                simpa [evmPriceStele, htimestampStele, hticSteleLoad,
                                  ← hticStackWord] using hleDone
                              by_cases htailLt :
                                  (solcSlotWord σ' I ⟨6⟩).toNat <
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperTakeSalesTicStackWord σLock I)
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
                                      (clipperTakeSalesTopWord σLock I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLock I)
                                          clipperSalesUint96Mask))
                                      (clipperTakeSalesTopHashMem_size I) hout)
                                    (clipperStatusPricePostCallMem_read64
                                      (clipperTakeSalesTopWord σLock I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLock I)
                                          clipperSalesUint96Mask))
                                      (clipperTakeSalesTopHashMem_size I)
                                      (clipperTakeSalesTopHashMem_read64 I) hout)
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have htailSlotStele :
                                    solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ' I ⟨6⟩ := rfl
                                have hlockOwner :
                                    evmLockStele.executionEnv.codeOwner = I.codeOwner := by
                                  rw [hlockStateStele]
                                  simp [initState]
                                have htailStele :
                                    (clipperStatusTailWord evmPriceStele).toNat <
                                      (UInt256.sub (clipperTimestampWord evmPriceStele)
                                        (clipperTakeSalesTicEVMWord evmLockStele I)).toNat := by
                                  simpa [evmPriceStele, clipperStatusTailWord,
                                    clipperTimestampWord, Stele.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage, solcSlotWord,
                                    htailSlotStele, htimestampStele, hticSteleLoad,
                                    ← hticStackWord, hticClean, hlockOwner] using htailLt
                                have hstatus :
                                    let evm0 := initState σ σ₀
                                      (Sat256.ofUInt256 g) A I
                                    let evmLock :=
                                      Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                        ⟨13⟩ ⟨1⟩
                                    ExecStmt fork config
                                      { contract := contract,
                                        locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                      evmLock
                                      (.internalCall "status"
                                        [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                      (.ok
                                        { contract := contract,
                                          locals := clipperTakeLocalsSt evmLock I true priceWord, immutables := immStore v }
                                        evmPriceStele) := by
                                  simpa [evmStele, evmLockStele] using
                                    clipperTakeStatusCallReturnsDoneTailTrue v
                                      (evm := evmLockStele) (evmPrice := evmPriceStele)
                                      I priceWord (out := o) hlePriceStele hcalcCodeStele
                                      hcallPriceStele hdecPrice hleDoneStele htailStele
                                have hbody :
                                    ExecTransitionBody fork config contract evmStele
                                      (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                                  simpa [evmStele, σLock] using
                                    (clipperTakeStatusDoneTrueSourceReverts (fork := fork) (hperm := by assumption)
                                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                      (g := g) v hwv hlockedEvm hstoppedLt husrEvm
                                      priceWord hstatus)
                                exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                              · have htailLe :
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperTakeSalesTicStackWord σLock I)
                                          clipperSalesUint96Mask)).toNat ≤
                                      (solcSlotWord σ' I ⟨6⟩).toNat := by
                                  exact Nat.le_of_not_gt htailLt
                                have htailSlotStele :
                                    solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ' I ⟨6⟩ := rfl
                                have hlockOwner :
                                    evmLockStele.executionEnv.codeOwner = I.codeOwner := by
                                  rw [hlockStateStele]
                                  simp [initState]
                                have htailStele :
                                    (UInt256.sub (clipperTimestampWord evmPriceStele)
                                        (clipperTakeSalesTicEVMWord evmLockStele I)).toNat ≤
                                      (clipperStatusTailWord evmPriceStele).toNat := by
                                  simpa [evmPriceStele, clipperStatusTailWord,
                                    clipperTimestampWord, Stele.EVM.storageLoad,
                                    State.lookupAccount, Account.lookupStorage, solcSlotWord,
                                    htailSlotStele, htimestampStele, hticSteleLoad,
                                    ← hticStackWord, hticClean, hlockOwner] using htailLe
                                by_cases hmul :
                                    priceWord.toNat * clipperRayWord.toNat < UInt256.size
                                · by_cases htopZero :
                                      clipperTakeSalesTopWord σLock I = ⟨0⟩
                                  · have hinv :=
                                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivDivZeroInvalid
                                        (v := v) (hpatch := hpatch) rd8606
                                        (by simpa [hticClean] using hleDone) htailLe
                                        (by simpa [priceWord] using hmul) htopZero
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have htopSteleZero :
                                        clipperTakeSalesTopEVMWord evmLockStele I = ⟨0⟩ := by
                                      simpa [htopSteleLoadLock, ← htopWord] using htopZero
                                    have hstatus :
                                        let evm0 := initState σ σ₀
                                          (Sat256.ofUInt256 g) A I
                                        let evmLock :=
                                          Stele.EVM.storageStore evm0
                                            evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                        ExecStmt fork config
                                          { contract := contract,
                                            locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                          evmLock
                                          (.internalCall "status"
                                            [.var "tic",
                                              .storage (salesF (.var "id") "top")] "st")
                                          .reverted := by
                                      simpa [evmStele, evmLockStele] using
                                        clipperTakeStatusCallRevertsRdivDivZero v
                                          (evm := evmLockStele) (evmPrice := evmPriceStele)
                                          I priceWord (out := o) hlePriceStele hcalcCodeStele
                                          hcallPriceStele hdecPrice hleDoneStele htailStele
                                          hmul htopSteleZero
                                    have hbody :
                                        ExecTransitionBody fork config contract evmStele
                                          (clipperTakeStore I) takeTransition.body
                                          .reverted (immStore v) := by
                                      simpa [evmStele, σLock] using
                                        (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                                          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                          (g := g) v hwv hlockedEvm hstoppedLt husrEvm
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
                                        (clipperTakeSalesTopWord σLock I)
                                    let cuspWord : UInt256 := solcSlotWord σ' I ⟨7⟩
                                    let doneWord : UInt256 := UInt256.lt ratioWord cuspWord
                                    have hcuspWordStele :
                                        cuspWord = clipperStatusCuspWord evmPriceStele := by
                                      simpa [cuspWord, evmPriceStele, hlockOwner,
                                        clipperStatusCuspWord, initState,
                                        Stele.EVM.storageLoad, State.lookupAccount,
                                        Account.lookupStorage, solcSlotWord]
                                    have hratioWordStele :
                                        ratioWord =
                                          UInt256.div (UInt256.mul priceWord clipperRayWord)
                                            (clipperTakeSalesTopEVMWord evmLockStele I) := by
                                      simp [ratioWord, htopSteleLoadLock, ← htopWord]
                                    by_cases hratio :
                                        ratioWord.toNat <
                                          (clipperStatusCuspWord evmPriceStele).toNat
                                    · have hdoneEval :
                                          evalExpr? config
                                            { contract := contract,
                                              locals := clipperStatusRatioLocals
                                                (clipperTakeSalesTicEVMWord evmLockStele I)
                                                (clipperTakeSalesTopEVMWord evmLockStele I)
                                                (UInt256.sub (clipperTimestampWord evmLockStele)
                                                  (clipperTakeSalesTicEVMWord evmLockStele I))
                                                priceWord
                                                (UInt256.sub (clipperTimestampWord evmPriceStele)
                                                  (clipperTakeSalesTicEVMWord evmLockStele I))
                                                (UInt256.div
                                                  (UInt256.mul priceWord clipperRayWord)
                                                  (clipperTakeSalesTopEVMWord evmLockStele I)), immutables := immStore v }
                                            evmPriceStele
                                            (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                              .ok (.bool true) := by
                                        rw [← hratioWordStele]
                                        exact clipperEvalStatusRatioCuspCond_true v
                                          evmPriceStele
                                          (clipperTakeSalesTicEVMWord evmLockStele I)
                                          (clipperTakeSalesTopEVMWord evmLockStele I)
                                          (UInt256.sub (clipperTimestampWord evmLockStele)
                                            (clipperTakeSalesTicEVMWord evmLockStele I))
                                          priceWord
                                          (UInt256.sub (clipperTimestampWord evmPriceStele)
                                            (clipperTakeSalesTicEVMWord evmLockStele I))
                                          ratioWord hratio
                                      have hdoneWordOne : doneWord = ⟨1⟩ := by
                                        unfold doneWord
                                        exact ult_one
                                          (by simpa [cuspWord, hcuspWordStele] using hratio)
                                      have hrev :=
                                        RD.clipperTakeStatusDoneTrueReverts (v := v)
                                          (hpatch := hpatch)
                                          (by
                                            simpa [priceWord, ratioWord, cuspWord, doneWord,
                                              hdoneWordOne] using rd3852)
                                          (clipperStatusPricePostCallMem_size
                                            (clipperTakeSalesTopWord σLock I)
                                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                              (UInt256.land
                                                (clipperTakeSalesTicStackWord σLock I)
                                                clipperSalesUint96Mask))
                                            (clipperTakeSalesTopHashMem_size I) hout)
                                          (clipperStatusPricePostCallMem_read64
                                            (clipperTakeSalesTopWord σLock I)
                                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                              (UInt256.land
                                                (clipperTakeSalesTicStackWord σLock I)
                                                clipperSalesUint96Mask))
                                            (clipperTakeSalesTopHashMem_size I)
                                            (clipperTakeSalesTopHashMem_read64 I) hout)
                                          (by simp only [List.length_cons, List.length_nil]; omega)
                                      have hstatus :
                                          let evm0 := initState σ σ₀
                                            (Sat256.ofUInt256 g) A I
                                          let evmLock :=
                                            Stele.EVM.storageStore evm0
                                              evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                          ExecStmt fork config
                                            { contract := contract,
                                              locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                            evmLock
                                            (.internalCall "status"
                                              [.var "tic",
                                                .storage (salesF (.var "id") "top")] "st")
                                            (.ok
                                              { contract := contract,
                                                locals :=
                                                  clipperTakeLocalsSt evmLock I true priceWord, immutables := immStore v }
                                              evmPriceStele) := by
                                        simpa [evmStele, evmLockStele] using
                                          clipperTakeStatusCallReturnsRdivBranch v
                                            (evm := evmLockStele) (evmPrice := evmPriceStele)
                                            I priceWord (out := o) hlePriceStele hcalcCodeStele
                                            hcallPriceStele hdecPrice hleDoneStele htailStele
                                            hmul
                                            (by
                                              intro hzero
                                              exact htopZero
                                                (by
                                                  simpa [htopSteleLoadLock, ← htopWord]
                                                    using hzero))
                                            true hdoneEval
                                      have hbody :
                                          ExecTransitionBody fork config contract evmStele
                                            (clipperTakeStore I) takeTransition.body
                                            .reverted (immStore v) := by
                                        simpa [evmStele, σLock] using
                                          (clipperTakeStatusDoneTrueSourceReverts (fork := fork) (hperm := by assumption)
                                            (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                            (g := g) v hwv hlockedEvm hstoppedLt
                                            husrEvm priceWord hstatus)
                                      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                                    · have hratioLe :
                                          (clipperStatusCuspWord evmPriceStele).toNat ≤
                                            ratioWord.toNat := by
                                        exact Nat.le_of_not_gt hratio
                                      have hdoneEval :
                                          evalExpr? config
                                            { contract := contract,
                                              locals := clipperStatusRatioLocals
                                                (clipperTakeSalesTicEVMWord evmLockStele I)
                                                (clipperTakeSalesTopEVMWord evmLockStele I)
                                                (UInt256.sub (clipperTimestampWord evmLockStele)
                                                  (clipperTakeSalesTicEVMWord evmLockStele I))
                                                priceWord
                                                (UInt256.sub (clipperTimestampWord evmPriceStele)
                                                  (clipperTakeSalesTicEVMWord evmLockStele I))
                                                (UInt256.div
                                                  (UInt256.mul priceWord clipperRayWord)
                                                  (clipperTakeSalesTopEVMWord evmLockStele I)), immutables := immStore v }
                                            evmPriceStele
                                            (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                              .ok (.bool false) := by
                                        rw [← hratioWordStele]
                                        exact clipperEvalStatusRatioCuspCond_false v
                                          evmPriceStele
                                          (clipperTakeSalesTicEVMWord evmLockStele I)
                                          (clipperTakeSalesTopEVMWord evmLockStele I)
                                          (UInt256.sub (clipperTimestampWord evmLockStele)
                                            (clipperTakeSalesTicEVMWord evmLockStele I))
                                          priceWord
                                          (UInt256.sub (clipperTimestampWord evmPriceStele)
                                            (clipperTakeSalesTicEVMWord evmLockStele I))
                                          ratioWord hratioLe
                                      have hdoneWordZero : doneWord = ⟨0⟩ := by
                                        unfold doneWord
                                        exact ult_zero
                                          (by
                                            simpa [ratioWord, cuspWord, hcuspWordStele]
                                              using hratioLe)
                                      have hstatus :
                                          let evm0 := initState σ σ₀
                                            (Sat256.ofUInt256 g) A I
                                          let evmLock :=
                                            Stele.EVM.storageStore evm0
                                              evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                          ExecStmt fork config
                                            { contract := contract,
                                              locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                            evmLock
                                            (.internalCall "status"
                                              [.var "tic",
                                                .storage (salesF (.var "id") "top")] "st")
                                            (.ok
                                              { contract := contract,
                                                locals :=
                                                  clipperTakeLocalsSt evmLock I false priceWord, immutables := immStore v }
                                              evmPriceStele) := by
                                        simpa [evmStele, evmLockStele] using
                                          clipperTakeStatusCallReturnsRdivBranch v
                                            (evm := evmLockStele) (evmPrice := evmPriceStele)
                                            I priceWord (out := o) hlePriceStele hcalcCodeStele
                                            hcallPriceStele hdecPrice hleDoneStele htailStele
                                            hmul
                                            (by
                                              intro hzero
                                              exact htopZero
                                                (by
                                                  simpa [htopSteleLoadLock, ← htopWord]
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
                                              (clipperTakeSalesTopWord σLock I)
                                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                                (UInt256.land
                                                  (clipperTakeSalesTicStackWord σLock I)
                                                  clipperSalesUint96Mask))
                                              (clipperTakeSalesTopHashMem_size I) hout)
                                            (clipperStatusPricePostCallMem_read64
                                              (clipperTakeSalesTopWord σLock I)
                                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                                (UInt256.land
                                                  (clipperTakeSalesTicStackWord σLock I)
                                                  clipperSalesUint96Mask))
                                              (clipperTakeSalesTopHashMem_size I)
                                              (clipperTakeSalesTopHashMem_read64 I) hout)
                                            (by
                                              simp only [List.length_cons, List.length_nil]
                                              omega)
                                        have hbody :
                                            ExecTransitionBody fork config contract evmStele
                                              (clipperTakeStore I) takeTransition.body
                                              .reverted (immStore v) := by
                                          simpa [evmStele, σLock] using
                                            (clipperTakeTooExpensiveSourceReverts (fork := fork) (hperm := by assumption)
                                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                              (g := g) v hwv hlockedEvm hstoppedLt
                                              husrEvm priceWord hmaxLt hstatus)
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
                                                (clipperTakeSalesTopWord σLock I)
                                                ((UInt256.ofNat I.header.timestamp).sub
                                                  ((clipperTakeSalesTicStackWord σLock I).land
                                                    clipperSalesUint96Mask))
                                                (clipperTakeSalesTopHashMem I) o).size := by
                                          rw [clipperStatusPricePostCallMem_size
                                            (clipperTakeSalesTopWord σLock I)
                                            ((UInt256.ofNat I.header.timestamp).sub
                                              ((clipperTakeSalesTicStackWord σLock I).land
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
                                              clipperTakePostTabWord_eq (σ := σ') (τ := σ')
                                                (evm := evmPriceStele) (I := I)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceStele])
                                                (by simpa [evmPriceStele] using hlockOwner)
                                            have hlot :=
                                              clipperTakePostLotWord_eq (σ := σ') (τ := σ')
                                                (evm := evmPriceStele) (I := I)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceStele])
                                                (by simpa [evmPriceStele] using hlockOwner)
                                            have hbaseMem196 :
                                                (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o).size =
                                                  196 := by
                                              exact
                                                clipperStatusPricePostCallMem_size
                                                  (clipperTakeSalesTopWord σLock I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLock I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I) hout
                                            have hbaseRead64 :
                                                (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o).readWithPadding
                                                    64 32 =
                                                  UInt256.toByteArray ⟨128⟩ := by
                                              exact
                                                clipperStatusPricePostCallMem_read64
                                                  (clipperTakeSalesTopWord σLock I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLock I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I)
                                                  (clipperTakeSalesTopHashMem_read64 I) hout
                                            have hmem196 :
                                                (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                  (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)).size =
                                                  196 := by
                                              have hsize :=
                                                twoWordHashMem_size_of_ge_64'
                                                  (clipperTakeIdWord I) (⟨12⟩ : UInt256)
                                                  (mem := clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)
                                                  (by rw [hbaseMem196]; norm_num)
                                              rw [hsize, hbaseMem196]
                                            have hread64 :
                                                (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                  (clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)).readWithPadding
                                                    64 32 =
                                                  UInt256.toByteArray ⟨128⟩ := by
                                              exact
                                                twoWordHashMem_read64_of_ge_96 (clipperTakeIdWord I)
                                                  (⟨12⟩ : UInt256)
                                                  (by rw [hbaseMem196]; norm_num) hbaseRead64
                                            exact
                                              clipperTakeOweGtTabVatFluxNoCodeRevertEquivFromPostAccounts (hperm := by assumption)
                                                (v := v) (hpatch := hpatch) hcode hwv hdispatch hdec
                                                hlockedEvm hstoppedLt husrEvm
                                                (by simpa [sliceE, lotE] using rd8686)
                                                (by simpa using hPostAccounts)
                                                (by simp [evmPriceStele])
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
                                                hdispatch hdec hlockedEvm
                                                hstoppedLt husrEvm
                                                (by simpa [sliceE, lotE] using rd8686)
                                                hout (by simpa using hPostAccounts)
                                                hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv hlenMax hoffHuge
                                                hpayloadOk hmaxLe
                                                (by simpa [sliceE, lotE] using howeMul)
                                                (by simpa [sliceE, lotE] using hgt)
                                                hstatus hdepth hperm
                                            · have htab :=
                                                clipperTakePostTabWord_eq (σ := σ')
                                                  (τ := σ') (evm := evmPriceStele)
                                                  (I := I) (by simpa using hPostAccounts)
                                                  (by simp [evmPriceStele])
                                                  (by simpa [evmPriceStele] using hlockOwner)
                                              have hlot :=
                                                clipperTakePostLotWord_eq (σ := σ')
                                                  (τ := σ') (evm := evmPriceStele)
                                                  (I := I) (by simpa using hPostAccounts)
                                                  (by simp [evmPriceStele])
                                                  (by simpa [evmPriceStele] using hlockOwner)
                                              have hbaseMem196 :
                                                  (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLock I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLock I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o).size =
                                                    196 := by
                                                exact clipperStatusPricePostCallMem_size
                                                  (clipperTakeSalesTopWord σLock I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLock I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I) hout
                                              have hbaseRead64 :
                                                  (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLock I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLock I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o).readWithPadding
                                                      64 32 = UInt256.toByteArray ⟨128⟩ := by
                                                exact clipperStatusPricePostCallMem_read64
                                                  (clipperTakeSalesTopWord σLock I)
                                                  ((UInt256.ofNat I.header.timestamp).sub
                                                    ((clipperTakeSalesTicStackWord σLock I).land
                                                      clipperSalesUint96Mask))
                                                  (clipperTakeSalesTopHashMem_size I)
                                                  (clipperTakeSalesTopHashMem_read64 I) hout
                                              have hmem196 :
                                                  (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                    (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLock I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLock I).land
                                                          clipperSalesUint96Mask))
                                                      (clipperTakeSalesTopHashMem I) o)).size =
                                                    196 := by
                                                have hmemSize := twoWordHashMem_size_of_ge_64'
                                                  (clipperTakeIdWord I) (⟨12⟩ : UInt256)
                                                  (mem := clipperStatusPricePostCallMem
                                                    (clipperTakeSalesTopWord σLock I)
                                                    ((UInt256.ofNat I.header.timestamp).sub
                                                      ((clipperTakeSalesTicStackWord σLock I).land
                                                        clipperSalesUint96Mask))
                                                    (clipperTakeSalesTopHashMem I) o)
                                                  (by rw [hbaseMem196]; norm_num)
                                                rw [hmemSize, hbaseMem196]
                                              have hread64 :
                                                  (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
                                                    (clipperStatusPricePostCallMem
                                                      (clipperTakeSalesTopWord σLock I)
                                                      ((UInt256.ofNat I.header.timestamp).sub
                                                        ((clipperTakeSalesTicStackWord σLock I).land
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
                                                hevmPriceSigma0 hevmPriceEnv
                                                (by rfl) hdataStartEq hlenMaxNat hpayloadOk
                                                (by
                                                  exact solcAddrMask_clean
                                                    (solcAddrMask_result_canonical
                                                      (clipperTakeWhoWord I)))
                                                (by rfl) (by rfl)
                                                (by
                                                  simpa [σLock,
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
                                                hlockedEvm hstoppedLt husrEvm hmaxLe
                                                hstatus hdepth hperm
                                        · have hrev :=
                                            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMulRevert
                                              (v := v) (hpatch := hpatch) rd8686
                                              (by simpa [sliceE, lotE] using Nat.le_of_not_gt howeMul)
                                              (by simp only [List.length_cons, List.length_nil]; omega)
                                          have hlot := clipperTakePostLotWord_eq (σ := σ') (τ := σ') (evm := evmPriceStele) (I := I)
                                            (by simpa using hPostAccounts) (by simp [evmPriceStele]) (by simpa [evmPriceStele] using hlockOwner)
                                          have hsrcHover : UInt256.size ≤
                                              (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
                                                (clipperTakeAmtWord I)).toNat * priceWord.toNat := by
                                            simpa [sliceE, lotE, hlot, clipperMinWord_comm, Nat.mul_comm]
                                              using Nat.le_of_not_gt howeMul
                                          have hbody := by
                                            simpa [evmStele, σLock] using
                                              (clipperTakeOwe0MulOverflowSourceReverts (fork := fork) (hperm := by assumption)
                                                (σ := σ)
                                                (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                                                hlockedEvm hstoppedLt husrEvm priceWord hmaxLe
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
                                      let evm0 := initState σ σ₀
                                        (Sat256.ofUInt256 g) A I
                                      let evmLock :=
                                        Stele.EVM.storageStore evm0
                                          evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                                      ExecStmt fork config
                                        { contract := contract,
                                          locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                        evmLock
                                        (.internalCall "status"
                                          [.var "tic",
                                            .storage (salesF (.var "id") "top")] "st")
                                        .reverted := by
                                    simpa [evmStele, evmLockStele] using
                                      clipperTakeStatusCallRevertsRdivMul v
                                        (evm := evmLockStele) (evmPrice := evmPriceStele)
                                        I priceWord (out := o) hlePriceStele hcalcCodeStele
                                        hcallPriceStele hdecPrice hleDoneStele htailStele hover
                                  have hbody :
                                      ExecTransitionBody fork config contract evmStele
                                        (clipperTakeStore I) takeTransition.body
                                        .reverted (immStore v) := by
                                    simpa [evmStele, σLock] using
                                      (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                        (g := g) v hwv hlockedEvm hstoppedLt husrEvm
                                        hstatus)
                                  exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                            · have hltDone :
                                  (UInt256.ofNat I.header.timestamp).toNat <
                                    (UInt256.land (clipperTakeSalesTicStackWord σLock I)
                                      clipperSalesUint96Mask).toNat := by
                                simpa [hticClean] using Nat.lt_of_not_ge hleDone
                              have hrev :=
                                Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForDoneRevert
                                  (v := v) (hpatch := hpatch) rd8606 hltDone
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hltDoneStele :
                                  (clipperTimestampWord evmPriceStele).toNat <
                                    (clipperTakeSalesTicEVMWord evmLockStele I).toNat := by
                                simpa [evmPriceStele, htimestampStele, hticSteleLoad,
                                  ← hticStackWord] using Nat.lt_of_not_ge hleDone
                              have hstatus :
                                  let evm0 := initState σ σ₀
                                    (Sat256.ofUInt256 g) A I
                                  let evmLock :=
                                    Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                      ⟨13⟩ ⟨1⟩
                                  ExecStmt fork config
                                    { contract := contract,
                                      locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                                    evmLock
                                    (.internalCall "status"
                                      [.var "tic", .storage (salesF (.var "id") "top")] "st")
                                    .reverted := by
                                simpa [evmStele, evmLockStele] using
                                  clipperTakeStatusCallRevertsAgeForDone v
                                    (evm := evmLockStele) (evmPrice := evmPriceStele)
                                    I priceWord (out := o) hlePriceStele hcalcCodeStele
                                    hcallPriceStele hdecPrice hltDoneStele
                              have hbody :
                                  ExecTransitionBody fork config contract evmStele
                                    (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                                simpa [evmStele, σLock] using
                                  (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g) v hwv hlockedEvm hstoppedLt husrEvm
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
                            (UInt256.land (clipperTakeSalesTicStackWord σLock I)
                              clipperSalesUint96Mask)
                        have hdepthInit : evmLockStele.executionEnv.depth = 1024 := by
                          simpa [evmLockStele, evmStele, initState,
                            storageStore_executionEnv] using hdepthEq
                        let evmPriceStele : EVM.State :=
                          { evmLockStele with
                            substate :=
                              (Ethereum.EVM.callSubstate fork
                                evmLockStele.accountMap (EVM.address (clipperStatusCalcAddress
                                evmLockStele)) evmLockStele.substate) }
                        have hcd :
                            config.externalABI.encode? "price"
                              [.int (Int.ofNat
                                (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                .int (Int.ofNat
                                  (UInt256.sub (clipperTimestampWord evmLockStele)
                                    (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)] =
                              some ((clipperStatusPriceCalldataMem
                                (clipperTakeSalesTopWord σLock I) ageForPrice
                                (clipperTakeSalesTopHashMem I)).readWithPadding 128 68) := by
                          have hcdRaw :
                              config.externalABI.encode? "price"
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopWord σLock I).toNat),
                                  .int (Int.ofNat ageForPrice.toNat)] =
                                some ((clipperStatusPriceCalldataMem
                                  (clipperTakeSalesTopWord σLock I) ageForPrice
                                  (clipperTakeSalesTopHashMem I)).readWithPadding 128 68) := by
                            simpa using
                              clipperStatusPriceEncode_eq
                                (clipperTakeSalesTopWord σLock I) ageForPrice
                                (clipperTakeSalesTopHashMem_size I)
                          have htopEvmStele :
                              clipperTakeSalesTopEVMWord evmLockStele I =
                                clipperTakeSalesTopWord σLock I := by
                            rw [htopSteleLoadLock, ← htopWord]
                          have hageForPriceStele :
                              UInt256.sub (clipperTimestampWord evmLockStele)
                                  (clipperTakeSalesTicEVMWord evmLockStele I) =
                                ageForPrice := by
                            simp [ageForPrice, htimestampStele, hticSteleLoad,
                              ← hticStackWord, hticClean]
                          rw [htopEvmStele, hageForPriceStele]
                          exact hcdRaw
                        have hcallPriceStele :
                            typedCallViaEVM fork config evmLockStele
                              (EVM.address (clipperStatusCalcAddress evmLockStele))
                              "price" 0
                              [.int (Int.ofNat
                                (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                .int (Int.ofNat
                                  (UInt256.sub (clipperTimestampWord evmLockStele)
                                    (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)]
                              (false, evmPriceStele, ByteArray.empty) false := by
                          simpa [evmPriceStele] using
                            (callNotMade_depthLimit (cfg := config) (evm := evmLockStele)
                              (tgt := EVM.address (clipperStatusCalcAddress evmLockStele))
                              (name := "price")
                              (args :=
                                [.int (Int.ofNat
                                  (clipperTakeSalesTopEVMWord evmLockStele I).toNat),
                                  .int (Int.ofNat
                                    (UInt256.sub (clipperTimestampWord evmLockStele)
                                      (clipperTakeSalesTicEVMWord evmLockStele I)).toNat)])
                              (callPerm := false)
                              (calldata :=
                                (clipperStatusPriceCalldataMem
                                  (clipperTakeSalesTopWord σLock I) ageForPrice
                                  (clipperTakeSalesTopHashMem I)).readWithPadding 128 68)
                              hcd hdepthInit)
                        have hstatus :
                            let evm0 := initState σ σ₀
                              (Sat256.ofUInt256 g) A I
                            let evmLock :=
                              Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                                ⟨13⟩ ⟨1⟩
                            ExecStmt fork config
                              { contract := contract,
                                locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                              evmLock
                              (.internalCall "status"
                                [.var "tic", .storage (salesF (.var "id") "top")] "st")
                              .reverted := by
                          simpa [evmStele, evmLockStele] using
                            clipperTakeStatusCallRevertsPriceCallFailure v
                              (evm := evmLockStele) (evmPrice := evmPriceStele)
                              I (out := ByteArray.empty) hlePriceStele hcalcCodeStele
                              hcallPriceStele
                        have hbody :
                            ExecTransitionBody fork config contract evmStele
                              (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                          simpa [evmStele, σLock] using
                            (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) v hwv hlockedEvm hstoppedLt husrEvm hstatus)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                    · have hcalcZero :
                          Reasoning.Theory.extCodeSizeWord σLock calcAddr = ⟨0⟩ :=
                        not_ne_iff.mp hcalcCode
                      have hrev :=
                        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceNoCode
                          (v := v) hpatch rd8549
                          (by simpa [calcAddr] using hcalcZero)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hcalcAddrStele :
                          clipperStatusCalcAddress evmLockStele =
                            AccountAddress.ofUInt256 calcAddr := by
                        simp [σLock, evmLockStele, evmStele, clipperStatusCalcAddress,
                          clipperStatusCalcWord, calcAddr, initState, Stele.EVM.storageLoad,
                          State.lookupAccount, Account.lookupStorage, solcSlotWord,
                          storageStore_accountMap, storageStore_executionEnv, hcalcSlotStele]
                      have hcalcZeroStele :
                          Reasoning.Theory.extCodeSizeWord σLock calcAddr = ⟨0⟩ := by
                        exact hcalcZero
                      have hnoCodeStele :
                          (UInt256.ofNat
                            ((evmLockStele.lookupAccount
                              (clipperStatusCalcAddress evmLockStele)).option 0
                              (fun acc => acc.code.size))).toNat = 0 := by
                        rw [hcalcAddrStele]
                        unfold Reasoning.Theory.extCodeSizeWord at hcalcZeroStele
                        simp [-Std.ExtTreeMap.get?_eq_getElem?, evmLockStele, evmStele, State.lookupAccount, initState,
                          storageStore_accountMap] at hcalcZeroStele ⊢
                        cases hacc : σLock.get? (AccountAddress.ofUInt256 calcAddr) with
                        | none =>
                            native_decide
                        | some acc =>
                            simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc] at hcalcZeroStele ⊢
                            exact congrArg UInt256.toNat hcalcZeroStele
                      have hstatus :
                          let evm0 := initState σ σ₀
                            (Sat256.ofUInt256 g) A I
                          let evmLock :=
                            Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                          ExecStmt fork config
                            { contract := contract,
                              locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                            evmLock
                            (.internalCall "status"
                              [.var "tic", .storage (salesF (.var "id") "top")] "st")
                            .reverted := by
                        simpa [evmStele, evmLockStele] using
                          clipperTakeStatusCallRevertsPriceNoCode v evmLockStele I
                            hlePriceStele hnoCodeStele
                      have hbody :
                          ExecTransitionBody fork config contract evmStele
                            (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                        simpa [evmStele, σLock] using
                          (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            v hwv hlockedEvm hstoppedLt husrEvm hstatus)
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
                  · have hltEvm :
                        (UInt256.ofNat I.header.timestamp).toNat <
                          (clipperTakeSalesTicStackWord σLock I).toNat := by
                      omega
                    have hltStele :
                        (UInt256.ofNat I.header.timestamp).toNat <
                          (clipperTakeSalesTicStackWord σLock I).toNat := by
                      rw [← hticStackWord]
                      exact hltEvm
                    let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                    let evmLockStele :=
                      Stele.EVM.storageStore evmStele evmStele.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                    have hltLoad :
                        (clipperTimestampWord evmLockStele).toNat <
                          (clipperTakeSalesTicEVMWord evmLockStele I).toNat := by
                      simpa [evmLockStele, evmStele, clipperTimestampWord,
                        clipperTakeSalesTicEVMWord, clipperTakeSalesTicStackWord,
                        initState, solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
                        storageStore_accountMap, storageStore_executionEnv, u256_land_comm]
                        using hltStele
                    have hstatus :
                        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
                        let evmLock :=
                          Stele.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                        ExecStmt fork config
                          { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
                          evmLock
                          (.internalCall "status"
                            [.var "tic", .storage (salesF (.var "id") "top")] "st")
                          .reverted := by
                      simpa [evmStele, evmLockStele] using
                        clipperTakeStatusCallRevertsAgeForPrice v evmLockStele I hltLoad
                    have hbody :
                        ExecTransitionBody fork config contract evmStele
                          (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                      simpa [evmStele, σLock] using
                        (clipperTakeStatusSourceRevertsOfStatus (fork := fork) (hperm := by assumption)
                          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          v hwv hlockedEvm hstoppedLt husrEvm hstatus)
                    have hrev :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPriceRevert
                        (v := v) hpatch _hreachStatus
                        (by simpa [hticClean] using hltEvm)
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
              · have hstoppedEvmGe : 3 ≤ (solcSlotWord σLock I ⟨14⟩).toNat := by
                  omega
                let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody fork config contract evmStele
                      (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
                  simpa [evmStele, σLock] using
                    (clipperTakeStoppedSourceReverts (fork := fork) (hperm := by assumption)
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                      hlockedEvm hstoppedEvmGe)
                have hrev := clipperTakeX_stoppedClosed (v := v) (σ := σLock)
                  hpatch (by simpa [σLock] using hstoppedEvmGe)
                  (by simpa [σLock] using rd3610)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
            · have hbody :
                  ExecTransitionBody fork config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (clipperTakeStore I) takeTransition.body .reverted (immStore v) :=
                clipperTakeBodyRevertsLocked
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                  hlockedEvm
              obtain ⟨_, _, rd3527⟩ := hreachDecoded
              have hrev := clipperTakeX_locked (fork := fork) (σ := σ) (I := I)
                (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (sel := clipperSelWord I) (v := v) hpatch hlockedEvm rd3527
              exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
          · have hpayloadShort :
                (((I.calldata.toList.drop 4).drop
                  ((clipperTakeDataOffsetWord I).toNat + 32)).take
                  (clipperTakeDataLenWord I).toNat).length ≠
                    (clipperTakeDataLenWord I).toNat := hpayloadOk
            have hdec := clipperDecode_take_none_payload_short (I := I)
              hcalldataSmall hsz164 hoffHuge hlenWord hlenMax hpayloadShort
            have hpayloadGt := clipperTakePayloadGt_one hsize hsz4 hoffHuge hlenWord
              hlenMax hpayloadShort
            exact (clipperTakeX_payload_short
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := clipperSelWord I) (v := v) hpatch hoffHuge hlenMax hpayloadGt hreachLenOk)
              |>.reEquivDecodingFailed hcode hdispatch hdec
      · have hlenShort : I.calldata.size <
            4 + (clipperTakeDataOffsetWord I).toNat + 32 := by
          omega
        have hdec := clipperDecode_take_none_length_short (I := I)
          hcalldataSmall hsz164 hoffHuge hlenShort
        have hgtLen := clipperTakeLenWordGt_one hsize hsz4 hoffHuge hlenShort
        exact (clipperTakeX_length_short
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := clipperSelWord I) (v := v) hpatch hgtLen hreachOffsetOk)
          |>.reEquivDecodingFailed hcode hdispatch hdec
  · have hshort : I.calldata.size < 164 := by omega
    have hdec := clipperDecode_take_none_short (I := I) hsz4 hshort
    exact (clipperTakeX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4 hsize
      hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdec

end Benchmarks.Dss.Clipper
