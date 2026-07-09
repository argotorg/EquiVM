import Benchmarks.Dss.Flopper.Dent.Part9

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let id := dentIdWord I
  let packedSlot := auctionPackedSlot id
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dentTransition :=
    flopperDispatchDent hsel
  have hreach := flopperReachDentBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := flopperDecode_dent_ok (I := I) hsz100
    have hdecoded := flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
    by_cases hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
    · by_cases hguyZero : flopperAddressReturnWord packedSlot σ_evm I = ⟨0⟩
      · exact flopperDentBodyCoreGuyNotSet hcode hsize hwv hsz100 hlive
          (by simpa [packedSlot, id] using hguyZero) hdispatch hdecode hreach hAccounts
      · have hguy :
            flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩ := by
          simpa [packedSlot, id] using hguyZero
        by_cases hticZero : flopperUint48Offset20Word packedSlot σ_evm I = ⟨0⟩
        · have hticOk :
              (UInt256.ofNat I.header.timestamp).toNat <
                  (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I))
                    σ_evm I).toNat ∨
                flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I))
                    σ_evm I = ⟨0⟩ := by
            exact Or.inr (by simpa [packedSlot, id] using hticZero)
          by_cases hendGt :
              (UInt256.ofNat I.header.timestamp).toNat <
                (flopperUint48Offset26Word packedSlot σ_evm I).toNat
          · by_cases hbid :
                dentBidWord I = flopperSlotWord (auctionBidSlot id) σ_evm I
            · by_cases hlotLt :
                  (dentLotWord I).toNat <
                    (flopperSlotWord (auctionLotSlot id) σ_evm I).toNat
              · by_cases hbegFit :
                    (flopperSlotWord ⟨4⟩ σ_evm I).toNat *
                        (dentLotWord I).toNat < UInt256.size
                · by_cases hlotOneFit :
                      (flopperSlotWord (auctionLotSlot id) σ_evm I).toNat *
                          dentOneWord.toNat < UInt256.size
                  · by_cases hsuff :
                        (dentBegLotWord
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            I).toNat ≤
                          (dentLotOneWord
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            I).toNat
                    · obtain ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, rd2322⟩ :=
                        flopperDentX_toBegLotOkFromDecoded hlive hguy hticOk
                          (by simpa [packedSlot, id] using hendGt)
                          (by simpa [id] using hbid)
                          (by simpa [id] using hlotLt)
                          (by simpa [id] using hlotOneFit) hbegFit hdecoded
                      obtain ⟨_, _, rd2405⟩ :=
                        flopperDentX_sufficientDecreaseOkFromGuard hsuff rd2322
                      by_cases hcallerEq :
                          UInt256.ofNat I.source.val =
                            flopperAddressReturnWord packedSlot σ_evm I
                      · by_cases haddFit :
                            (UInt256.land (UInt256.ofNat I.header.timestamp)
                                  flopperUint48Mask).toNat +
                                (dentRuntimeTtlWord I.codeOwner σ_evm I).toNat <
                              2 ^ 48
                        · exact flopperDentBodyCoreSuccessCallerEq hcode hperm hwv
                            hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                            (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                            hbegFit (by simpa [id] using hlotOneFit) hsuff
                            (by simpa [packedSlot, id] using hcallerEq) haddFit
                            hdispatch hdecode rd2405 hAccounts
                        · exact flopperDentBodyCoreAddOverflowCallerEq hcode hperm hwv
                            hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                            (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                            hbegFit (by simpa [id] using hlotOneFit) hsuff
                            (by simpa [packedSlot, id] using hcallerEq)
                            (Nat.le_of_not_gt haddFit) hdispatch hdecode rd2405
                            hAccounts
                      · have hcallerNe :
                            UInt256.ofNat I.source.val ≠
                              flopperAddressReturnWord
                                (auctionPackedSlot (dentIdWord I)) σ_evm I := by
                          simpa [packedSlot, id] using hcallerEq
                        by_cases hnoCode :
                            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                              (flopperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩
                        · exact flopperDentBodyCoreMoveNoCode hcode hperm hwv
                            hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                            (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                            hbegFit (by simpa [id] using hlotOneFit) hsuff
                            hcallerNe hnoCode hdispatch hdecode rd2405 hmemLotOne
                            hreadLotOne hAccounts
                        · have hcodeSize :
                              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                                (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩ := hnoCode
                          by_cases hdepthEq : I.depth = 1024
                          · exact flopperDentBodyCoreMoveCallDepthLimit hcode hwv
                              hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                              (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                              hbegFit (by simpa [id] using hlotOneFit) hsuff hcallerNe
                              hcodeSize hdepthEq hdispatch hdecode rd2405 hmemLotOne
                              hreadLotOne hAccounts
                          · have hdepthLt : I.depth.val < 1024 := by
                              have hle : I.depth.val ≤ 1024 :=
                                Nat.le_of_lt_succ I.depth.isLt
                              have hne : I.depth.val ≠ 1024 := by
                                intro hval
                                apply hdepthEq
                                exact Fin.ext hval
                              omega
                            obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
                            let memCaller := twoWordHashMem id ⟨1⟩ memLotOne
                            let memMap := twoWordHashMem id ⟨1⟩ memCaller
                            let src := UInt256.ofNat I.source.val
                            let vat := flopperAddressReturnWord ⟨2⟩ σ_evm I
                            let guy := flopperAddressReturnWord packedSlot σ_evm I
                            have hmemCaller : memCaller.size = 96 := by
                              simpa [memCaller, id] using
                                twoWordHashMem_size_96 id ⟨1⟩ hmemLotOne
                            have hread64Caller :
                                memCaller.readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ := by
                              simpa [memCaller, id] using
                                twoWordHashMem_read64 id ⟨1⟩ hmemLotOne hreadLotOne
                            have hmemMap : memMap.size = 96 := by
                              simpa [memMap, memCaller, id] using
                                twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
                            have hread64Map :
                                memMap.readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ := by
                              simpa [memMap, memCaller, id] using
                                twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
                            have hmoveMem96 :
                                96 ≤ (dentMoveCalldataMem src guy (dentBidWord I)
                                  memMap).size := by
                              rw [dentMoveCalldataMem_size src guy (dentBidWord I) hmemMap]
                              decide
                            have hmoveRead64 :
                                (dentMoveCalldataMem src guy (dentBidWord I) memMap
                                  ).readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ := by
                              exact dentMoveCalldataMem_read64 src guy (dentBidWord I)
                                hmemMap hread64Map
                            obtain ⟨_, _, rd2439⟩ :=
                              flopperDentX_callerNeToMove hcallerNe rd2435
                            obtain ⟨cA', σ', zMove, outMove, A', k2545, C2545,
                                rd2545, hcallMove, houtMoveSize⟩ :=
                              flopperDentX_moveCall
                                (g := Sat256.ofUInt256 g) hperm hcodeSize hdepthLt
                                hmemCaller hread64Caller rd2439
                            by_cases hzMove : zMove = true
                            · have rd2545True : RD flopperBytecode I
                                  (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                                    A I) ⟨2545⟩
                                  (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
                                    flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                                    dentBidWord I :: dentLotWord I :: dentIdWord I ::
                                    ⟨334⟩ :: flopperSelWord I :: [])
                                  (dentMoveCalldataMem src guy (dentBidWord I) memMap)
                                  (UInt256.ofNat 8) outMove (cA', σ') k2545 C2545 := by
                                simpa [hzMove, vat, id] using rd2545
                              have hcallMoveTrue :
                                  typedCallViaEVM config
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                                      A I)
                                    (EVM.address (AccountAddress.ofNat
                                      (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                                    "move" 0
                                    [.address (AccountAddress.ofNat
                                        (UInt256.ofNat I.source.val).toNat),
                                      .address (AccountAddress.ofNat
                                        (flopperAddressReturnWord
                                          (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
                                      .int (Int.ofNat (dentBidWord I).toNat)]
                                    (true,
                                      { initState cA gh bl σ_evm σ₀
                                          (Sat256.ofUInt256 g) A I with
                                        accountMap := σ', substate := A',
                                        createdAccounts := cA' },
                                      outMove) true := by
                                simpa [hzMove, vat, src, guy, packedSlot, id] using hcallMove
                              by_cases hticMoveZero :
                                  flopperUint48Offset20Word packedSlot σ' I = ⟨0⟩
                              · by_cases hashNoCode :
                                    Reasoning.Theory.uniswapExtCodeSizeWord σ'
                                      (flopperAddressReturnWord packedSlot σ' I) = ⟨0⟩
                                · exact flopperDentBodyCoreAshNoCodeMoveCallerNeTicZero
                                    hcode hwv hlive hguy hticOk
                                    (by simpa [packedSlot, id] using hendGt)
                                    (by simpa [id] using hbid)
                                    (by simpa [id] using hlotLt) hbegFit
                                    (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                    hcodeSize
                                    (by simpa [packedSlot, id] using hticMoveZero)
                                    (by simpa [packedSlot, id] using hashNoCode)
                                    rd2545True hmoveMem96 hmoveRead64 hcallMoveTrue
                                    hdispatch hdecode hAccounts
                                · have hashCodeSize :
                                      Reasoning.Theory.uniswapExtCodeSizeWord σ'
                                        (flopperAddressReturnWord
                                          (auctionPackedSlot (dentIdWord I)) σ' I) ≠
                                          ⟨0⟩ := by
                                    simpa [packedSlot, id] using hashNoCode
                                  obtain ⟨memAshSelector, cAAsh, σAsh, zAsh, outAsh,
                                      AinAsh, AAsh, k2690, C2690, rd2690, hashCall,
                                      houtAshSize, hmemAsh64, hreadAsh64, hmemAsh128Of,
                                      hreadAsh128Of⟩ :=
                                    flopperDentX_moveSuccessTicZeroAshCall
                                      (g := Sat256.ofUInt256 g) hperm hmoveMem96
                                      hmoveRead64
                                      (by simpa [packedSlot, id] using hticMoveZero)
                                      hashCodeSize hdepthLt rd2545True
                                  let evmAshPre : EVM.State :=
                                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                                        A I with
                                      accountMap := σ', substate := AinAsh,
                                      createdAccounts := cA' }
                                  have hdepthNeAsh :
                                      evmAshPre.executionEnv.depth ≠ 1024 := by
                                    intro hbad
                                    have hbadI : I.depth = 1024 := by
                                      simpa [evmAshPre, initState] using hbad
                                    have hval : I.depth.val = 1024 := congrArg Fin.val hbadI
                                    omega
                                  by_cases hzAsh : zAsh = true
                                  · have rd2690True : RD flopperBytecode I
                                        (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀
                                          (Sat256.ofUInt256 g) A I) ⟨2690⟩
                                        (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
                                          flopperAddressReturnWord
                                            (auctionPackedSlot (dentIdWord I)) σ' I ::
                                          ⟨0⟩ :: dentBidWord I :: dentLotWord I ::
                                          dentIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                                        (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
                                          (min dentAshOutSize
                                            (UInt256.ofNat outAsh.size)).toNat)
                                        (UInt256.ofNat 8) outAsh (cAAsh, σAsh) k2690
                                        C2690 := by
                                      simpa [hzAsh, packedSlot, id] using rd2690
                                    have hashCallTrue :
                                        typedCallViaEVM config
                                          { initState cA gh bl σ_evm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σ', substate := AinAsh,
                                            createdAccounts := cA' }
                                          (EVM.address (AccountAddress.ofNat
                                            (flopperAddressReturnWord
                                              (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
                                          "Ash" 0 []
                                          (true,
                                            { initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σAsh, substate := AAsh,
                                              createdAccounts := cAAsh },
                                            outAsh) true := by
                                      simpa [hzAsh, packedSlot, id] using hashCall
                                    obtain ⟨AAshCore, hashCallTrueCoreRaw⟩ :=
                                      dentTypedCallViaEVM_zero_setSubstate hashCallTrue
                                        (by simpa [evmAshPre] using hdepthNeAsh) A'
                                    have hashCallTrueCore :
                                        typedCallViaEVM config
                                          { initState cA gh bl σ_evm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σ', substate := A',
                                            createdAccounts := cA' }
                                          (EVM.address (AccountAddress.ofNat
                                            (flopperAddressReturnWord
                                              (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
                                          "Ash" 0 []
                                          (true,
                                            { initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σAsh, substate := AAshCore,
                                              createdAccounts := cAAsh },
                                            outAsh) true := by
                                      simpa using hashCallTrueCoreRaw
                                    by_cases houtAsh32 : 32 ≤ outAsh.size
                                    · have hmemAsh128 := hmemAsh128Of houtAsh32
                                      have hreadAsh128 := hreadAsh128Of houtAsh32
                                      by_cases hkissNoCode :
                                          Reasoning.Theory.uniswapExtCodeSizeWord σAsh
                                            (flopperAddressReturnWord packedSlot σAsh I) =
                                              ⟨0⟩
                                      · exact
                                          flopperDentBodyCoreKissNoCodeMoveCallerNeTicZero
                                            hcode hwv hlive hguy hticOk
                                            (by simpa [packedSlot, id] using hendGt)
                                            (by simpa [id] using hbid)
                                            (by simpa [id] using hlotLt) hbegFit
                                            (by simpa [id] using hlotOneFit) hsuff
                                            hcallerNe hcodeSize
                                            (by simpa [packedSlot, id] using hticMoveZero)
                                            hashCodeSize
                                            (by simpa [packedSlot, id] using hkissNoCode)
                                            hdepthLt rd2690True hcallMoveTrue hashCallTrueCore
                                            houtAsh32 houtAshSize hmemAsh64 hreadAsh64
                                            hmemAsh128 hreadAsh128 hdispatch hdecode
                                            hAccounts
                                      · have hkissCodeSize :
                                            Reasoning.Theory.uniswapExtCodeSizeWord σAsh
                                              (flopperAddressReturnWord
                                                (auctionPackedSlot (dentIdWord I))
                                                σAsh I) ≠ ⟨0⟩ := by
                                          simpa [packedSlot, id] using hkissNoCode
                                        obtain ⟨_, _, rd2731⟩ :=
                                          flopperDentX_ashCallSuccessDecodeOk
                                            houtAsh32 houtAshSize hmemAsh64 hreadAsh64
                                            hmemAsh128 hreadAsh128 rd2690True
                                        obtain ⟨_, _, rd2817⟩ :=
                                          flopperDentX_ashDecodeOkToKissExtcodesizeGuard
                                            hmemAsh128 hreadAsh64 rd2731
                                        let memAsh := outAsh.write 0 memAshSelector
                                          dentAshOutPtr.toNat
                                          (min dentAshOutSize
                                            (UInt256.ofNat outAsh.size)).toNat
                                        let memKissMap := twoWordHashMem id ⟨1⟩ memAsh
                                        let memKiss := dentKissCalldataMem
                                          (dentKissAmtWord I outAsh) memKissMap
                                        have hkissEncode :
                                            config.externalABI.encode? "kiss"
                                                [.int (Int.ofNat
                                                  (dentKissAmtWord I outAsh).toNat)] =
                                              some (memKiss.readWithPadding
                                                dentKissOutPtr.toNat
                                                dentKissInSize.toNat) := by
                                          simpa only [memKiss] using
                                            (dentKissEncode_eq
                                              (dentKissAmtWord I outAsh)
                                              (mem := memKissMap))
                                        obtain ⟨cAKiss, σKiss, zKiss, outKiss,
                                            AinKiss, AKiss, k2833, C2833, rd2833,
                                            hkissCall, houtKissSize⟩ :=
                                          flopperDentX_kissCall
                                            (g := Sat256.ofUInt256 g) hperm
                                            hkissCodeSize hdepthLt
                                            (by
                                              simpa only [memAsh, memKissMap, memKiss]
                                                using hkissEncode)
                                            (by
                                              simpa only [memAsh, memKissMap, memKiss,
                                                packedSlot, id] using rd2817)
                                        by_cases hzKiss : zKiss = true
                                        · have rd2833True : RD flopperBytecode I
                                              (Sat256.ofUInt256 g)
                                              (initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I) ⟨2833⟩
                                              (⟨1⟩ :: dentKissEndPtr ::
                                                dentKissSelectorWord ::
                                                flopperAddressReturnWord
                                                  (auctionPackedSlot (dentIdWord I))
                                                  σAsh I ::
                                                dentAshWord outAsh :: dentBidWord I ::
                                                dentLotWord I :: dentIdWord I ::
                                                ⟨334⟩ :: flopperSelWord I :: [])
                                              memKiss (UInt256.ofNat 8) outKiss
                                              (cAKiss, σKiss) k2833 C2833 := by
                                            simpa only [hzKiss, memAsh, memKissMap, memKiss,
                                              packedSlot, id] using rd2833
                                          have hkissCallTrue :
                                              typedCallViaEVM config
                                                { initState cA gh bl σ_evm σ₀
                                                    (Sat256.ofUInt256 g) A I with
                                                  accountMap := σAsh, substate := AinKiss,
                                                  createdAccounts := cAAsh }
                                                (EVM.address (AccountAddress.ofNat
                                                  (flopperAddressReturnWord
                                                    (auctionPackedSlot (dentIdWord I))
                                                    σAsh I).toNat))
                                                "kiss" 0
                                                [.int (Int.ofNat
                                                  (dentKissAmtWord I outAsh).toNat)]
                                                (true,
                                                  { initState cA gh bl σ_evm σ₀
                                                      (Sat256.ofUInt256 g) A I with
                                                    accountMap := σKiss,
                                                    substate := AKiss,
                                                    createdAccounts := cAKiss },
                                                  outKiss) true := by
                                            simpa only [hzKiss, packedSlot, id] using hkissCall
                                          by_cases haddFit :
                                              (UInt256.land
                                                    (UInt256.ofNat I.header.timestamp)
                                                    flopperUint48Mask).toNat +
                                                  (dentRuntimeTtlWord I.codeOwner
                                                    (dentRuntimeAfterGuyMap I.codeOwner
                                                      σKiss I) I).toNat <
                                                2 ^ 48
                                          · exact
                                              flopperDentBodyCoreSuccessMoveCallerNeTicZeroKissSuccess
                                                hcode hperm hwv hlive hguy hticOk
                                                (by simpa [packedSlot, id] using hendGt)
                                                (by simpa [id] using hbid)
                                                (by simpa [id] using hlotLt) hbegFit
                                                (by simpa [id] using hlotOneFit) hsuff
                                                hcallerNe hcodeSize
                                                (by simpa [packedSlot, id]
                                                  using hticMoveZero)
                                                hashCodeSize hkissCodeSize haddFit
                                                hdepthLt rd2833True hcallMoveTrue
                                                hashCallTrueCore houtAsh32 hkissCallTrue
                                                hdispatch hdecode hAccounts
                                          · exact
                                              flopperDentBodyCoreAddOverflowMoveCallerNeTicZeroKissSuccess
                                                hcode hperm hwv hlive hguy hticOk
                                                (by simpa [packedSlot, id] using hendGt)
                                                (by simpa [id] using hbid)
                                                (by simpa [id] using hlotLt) hbegFit
                                                (by simpa [id] using hlotOneFit) hsuff
                                                hcallerNe hcodeSize
                                                (by simpa [packedSlot, id]
                                                  using hticMoveZero)
                                                hashCodeSize hkissCodeSize
                                                (Nat.le_of_not_gt haddFit) hdepthLt
                                                rd2833True hcallMoveTrue hashCallTrueCore
                                                houtAsh32 hkissCallTrue hdispatch hdecode
                                                hAccounts
                                        · have hzKissFalse : zKiss = false := by
                                            cases zKiss <;> simp at hzKiss ⊢
                                          have rd2833False : RD flopperBytecode I
                                              (Sat256.ofUInt256 g)
                                              (initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I) ⟨2833⟩
                                              (⟨0⟩ :: dentKissEndPtr ::
                                                dentKissSelectorWord ::
                                                flopperAddressReturnWord
                                                  (auctionPackedSlot (dentIdWord I))
                                                  σAsh I ::
                                                dentAshWord outAsh :: dentBidWord I ::
                                                dentLotWord I :: dentIdWord I ::
                                                ⟨334⟩ :: flopperSelWord I :: [])
                                              memKiss (UInt256.ofNat 8) outKiss
                                              (cAKiss, σKiss) k2833 C2833 := by
                                            simpa only [hzKissFalse, memAsh, memKissMap,
                                              memKiss, packedSlot, id] using rd2833
                                          have hkissCallFalse :
                                              typedCallViaEVM config
                                                { initState cA gh bl σ_evm σ₀
                                                    (Sat256.ofUInt256 g) A I with
                                                  accountMap := σAsh, substate := AinKiss,
                                                  createdAccounts := cAAsh }
                                                (EVM.address (AccountAddress.ofNat
                                                  (flopperAddressReturnWord
                                                    (auctionPackedSlot (dentIdWord I))
                                                    σAsh I).toNat))
                                                "kiss" 0
                                                [.int (Int.ofNat
                                                  (dentKissAmtWord I outAsh).toNat)]
                                                (false,
                                                  { initState cA gh bl σ_evm σ₀
                                                      (Sat256.ofUInt256 g) A I with
                                                    accountMap := σKiss,
                                                    substate := AKiss,
                                                    createdAccounts := cAKiss },
                                                  outKiss) true := by
                                            simpa only [hzKissFalse, packedSlot, id]
                                              using hkissCall
                                          exact
                                            flopperDentBodyCoreKissCallFailureMoveCallerNeTicZero
                                              hcode hwv hlive hguy hticOk
                                              (by simpa [packedSlot, id] using hendGt)
                                              (by simpa [id] using hbid)
                                              (by simpa [id] using hlotLt) hbegFit
                                              (by simpa [id] using hlotOneFit) hsuff
                                              hcallerNe hcodeSize
                                              (by simpa [packedSlot, id]
                                                using hticMoveZero)
                                              hashCodeSize hkissCodeSize hdepthLt
                                              rd2833False hcallMoveTrue hashCallTrueCore
                                              houtAsh32 hkissCallFalse houtKissSize
                                              hdispatch hdecode hAccounts
                                    · have hashShort : outAsh.size < 32 := by omega
                                      exact
                                        flopperDentBodyCoreAshDecodeShortMoveCallerNeTicZero
                                          hcode hwv hlive hguy hticOk
                                          (by simpa [packedSlot, id] using hendGt)
                                          (by simpa [id] using hbid)
                                          (by simpa [id] using hlotLt) hbegFit
                                          (by simpa [id] using hlotOneFit) hsuff
                                          hcallerNe hcodeSize
                                          (by simpa [packedSlot, id] using hticMoveZero)
                                          hashCodeSize hdepthLt rd2690True hcallMoveTrue
                                          hashCallTrueCore hashShort houtAshSize hmemAsh64
                                          hreadAsh64 hdispatch hdecode hAccounts
                                  · have hzAshFalse : zAsh = false := by
                                      cases zAsh <;> simp at hzAsh ⊢
                                    have rd2690False : RD flopperBytecode I
                                        (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀
                                          (Sat256.ofUInt256 g) A I) ⟨2690⟩
                                        (⟨0⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
                                          flopperAddressReturnWord
                                            (auctionPackedSlot (dentIdWord I)) σ' I ::
                                          ⟨0⟩ :: dentBidWord I :: dentLotWord I ::
                                          dentIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                                        (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
                                          (min dentAshOutSize
                                            (UInt256.ofNat outAsh.size)).toNat)
                                        (UInt256.ofNat 8) outAsh (cAAsh, σAsh) k2690
                                        C2690 := by
                                      simpa [hzAshFalse, packedSlot, id] using rd2690
                                    have hashCallFalse :
                                        typedCallViaEVM config
                                          { initState cA gh bl σ_evm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σ', substate := AinAsh,
                                            createdAccounts := cA' }
                                          (EVM.address (AccountAddress.ofNat
                                            (flopperAddressReturnWord
                                              (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
                                          "Ash" 0 []
                                          (false,
                                            { initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σAsh, substate := AAsh,
                                              createdAccounts := cAAsh },
                                            outAsh) true := by
                                      simpa [hzAshFalse, packedSlot, id] using hashCall
                                    obtain ⟨AAshCore, hashCallFalseCoreRaw⟩ :=
                                      dentTypedCallViaEVM_zero_setSubstate hashCallFalse
                                        (by simpa [evmAshPre] using hdepthNeAsh) A'
                                    have hashCallFalseCore :
                                        typedCallViaEVM config
                                          { initState cA gh bl σ_evm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σ', substate := A',
                                            createdAccounts := cA' }
                                          (EVM.address (AccountAddress.ofNat
                                            (flopperAddressReturnWord
                                              (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
                                          "Ash" 0 []
                                          (false,
                                            { initState cA gh bl σ_evm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σAsh, substate := AAshCore,
                                              createdAccounts := cAAsh },
                                            outAsh) true := by
                                      simpa using hashCallFalseCoreRaw
                                    exact
                                      flopperDentBodyCoreAshCallFailureMoveCallerNeTicZero
                                        hcode hwv hlive hguy hticOk
                                        (by simpa [packedSlot, id] using hendGt)
                                        (by simpa [id] using hbid)
                                        (by simpa [id] using hlotLt) hbegFit
                                        (by simpa [id] using hlotOneFit) hsuff
                                        hcallerNe hcodeSize
                                        (by simpa [packedSlot, id] using hticMoveZero)
                                        hashCodeSize hdepthLt rd2690False
                                        hcallMoveTrue hashCallFalseCore houtAshSize
                                        hdispatch hdecode hAccounts
                              · have hticMoveNe :
                                    flopperUint48Offset20Word
                                      (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩ := by
                                  simpa [packedSlot, id] using hticMoveZero
                                by_cases haddFit :
                                    (UInt256.land (UInt256.ofNat I.header.timestamp)
                                          flopperUint48Mask).toNat +
                                        (dentRuntimeTtlWord I.codeOwner
                                          (dentRuntimeAfterGuyMap I.codeOwner σ' I)
                                          I).toNat <
                                      2 ^ 48
                                · exact flopperDentBodyCoreSuccessMoveCallerNeTicNonzero
                                    hcode hperm hwv hlive hguy hticOk
                                    (by simpa [packedSlot, id] using hendGt)
                                    (by simpa [id] using hbid)
                                    (by simpa [id] using hlotLt) hbegFit
                                    (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                    hcodeSize hticMoveNe haddFit rd2545True
                                    hcallMoveTrue hdispatch hdecode hAccounts
                                · exact flopperDentBodyCoreAddOverflowMoveCallerNeTicNonzero
                                    hcode hperm hwv hlive hguy hticOk
                                    (by simpa [packedSlot, id] using hendGt)
                                    (by simpa [id] using hbid)
                                    (by simpa [id] using hlotLt) hbegFit
                                    (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                    hcodeSize hticMoveNe (Nat.le_of_not_gt haddFit)
                                    rd2545True hcallMoveTrue hdispatch hdecode hAccounts
                            · have hzMoveFalse : zMove = false := by
                                cases zMove <;> simp at hzMove ⊢
                              have rd2545False : RD flopperBytecode I
                                  (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                                    A I) ⟨2545⟩
                                  (⟨0⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
                                    flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                                    dentBidWord I :: dentLotWord I :: dentIdWord I ::
                                    ⟨334⟩ :: flopperSelWord I :: [])
                                  (dentMoveCalldataMem src guy (dentBidWord I) memMap)
                                  (UInt256.ofNat 8) outMove (cA', σ') k2545 C2545 := by
                                simpa [hzMoveFalse, vat, id] using rd2545
                              have hcallMoveFalse :
                                  typedCallViaEVM config
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g)
                                      A I)
                                    (EVM.address (AccountAddress.ofNat
                                      (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                                    "move" 0
                                    [.address (AccountAddress.ofNat
                                        (UInt256.ofNat I.source.val).toNat),
                                      .address (AccountAddress.ofNat
                                        (flopperAddressReturnWord
                                          (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
                                      .int (Int.ofNat (dentBidWord I).toNat)]
                                    (false,
                                      { initState cA gh bl σ_evm σ₀
                                          (Sat256.ofUInt256 g) A I with
                                        accountMap := σ', substate := A',
                                        createdAccounts := cA' },
                                      outMove) true := by
                                simpa [hzMoveFalse, vat, src, guy, packedSlot, id]
                                  using hcallMove
                              exact flopperDentBodyCoreMoveCallFailure hcode hwv hlive
                                hguy hticOk (by simpa [packedSlot, id] using hendGt)
                                (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                                hbegFit (by simpa [id] using hlotOneFit) hsuff
                                hcallerNe hcodeSize rd2545False hcallMoveFalse
                                houtMoveSize hdispatch hdecode hAccounts
                    · exact flopperDentBodyCoreInsufficientDecrease hcode hsize hwv
                        hsz100 hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                        (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                        hbegFit (by simpa [id] using hlotOneFit) (by omega)
                        hdispatch hdecode hreach hAccounts
                  · exact flopperDentBodyCoreLotOneOverflow hcode hsize hwv hsz100
                      hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                      (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                      hbegFit (Nat.le_of_not_gt hlotOneFit) hdispatch hdecode hreach
                      hAccounts
                · exact flopperDentBodyCoreBegLotOverflow hcode hsize hwv hsz100
                    hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                    (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                    (Nat.le_of_not_gt hbegFit) hdispatch hdecode hreach hAccounts
              · exact flopperDentBodyCoreLotNotLower hcode hsize hwv hsz100 hlive
                  hguy hticOk (by simpa [packedSlot, id] using hendGt)
                  (by simpa [id] using hbid) (Nat.le_of_not_gt hlotLt)
                  hdispatch hdecode hreach hAccounts
            · exact flopperDentBodyCoreBidMismatch hcode hsize hwv hsz100 hlive
                hguy hticOk (by simpa [packedSlot, id] using hendGt)
                (by simpa [id] using hbid) hdispatch hdecode hreach hAccounts
          · exact flopperDentBodyCoreEndFinished hcode hsize hwv hsz100 hlive
              hguy hticOk (Nat.le_of_not_gt hendGt) hdispatch hdecode hreach
              hAccounts
        · by_cases hticGt :
              (UInt256.ofNat I.header.timestamp).toNat <
                (flopperUint48Offset20Word packedSlot σ_evm I).toNat
          · have hticOk :
                (UInt256.ofNat I.header.timestamp).toNat <
                    (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I))
                      σ_evm I).toNat ∨
                  flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I))
                      σ_evm I = ⟨0⟩ := by
              exact Or.inl (by simpa [packedSlot, id] using hticGt)
            by_cases hendGt :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (flopperUint48Offset26Word packedSlot σ_evm I).toNat
            · by_cases hbid :
                  dentBidWord I = flopperSlotWord (auctionBidSlot id) σ_evm I
              · by_cases hlotLt :
                    (dentLotWord I).toNat <
                      (flopperSlotWord (auctionLotSlot id) σ_evm I).toNat
                · by_cases hbegFit :
                      (flopperSlotWord ⟨4⟩ σ_evm I).toNat *
                          (dentLotWord I).toNat < UInt256.size
                  · by_cases hlotOneFit :
                        (flopperSlotWord (auctionLotSlot id) σ_evm I).toNat *
                            dentOneWord.toNat < UInt256.size
                    · by_cases hsuff :
                          (dentBegLotWord
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              I).toNat ≤
                            (dentLotOneWord
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              I).toNat
                      · obtain ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, rd2322⟩ :=
                          flopperDentX_toBegLotOkFromDecoded hlive hguy hticOk
                            (by simpa [packedSlot, id] using hendGt)
                            (by simpa [id] using hbid)
                            (by simpa [id] using hlotLt)
                            (by simpa [id] using hlotOneFit) hbegFit hdecoded
                        obtain ⟨_, _, rd2405⟩ :=
                          flopperDentX_sufficientDecreaseOkFromGuard hsuff rd2322
                        by_cases hcallerEq :
                            UInt256.ofNat I.source.val =
                              flopperAddressReturnWord packedSlot σ_evm I
                        · by_cases haddFit :
                              (UInt256.land (UInt256.ofNat I.header.timestamp)
                                    flopperUint48Mask).toNat +
                                  (dentRuntimeTtlWord I.codeOwner σ_evm I).toNat <
                                2 ^ 48
                          · exact flopperDentBodyCoreSuccessCallerEq hcode hperm hwv
                              hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                              (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                              hbegFit (by simpa [id] using hlotOneFit) hsuff
                              (by simpa [packedSlot, id] using hcallerEq) haddFit
                              hdispatch hdecode rd2405 hAccounts
                          · exact flopperDentBodyCoreAddOverflowCallerEq hcode hperm hwv
                              hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                              (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                              hbegFit (by simpa [id] using hlotOneFit) hsuff
                              (by simpa [packedSlot, id] using hcallerEq)
                              (Nat.le_of_not_gt haddFit) hdispatch hdecode rd2405
                              hAccounts
                        · have hcallerNe :
                              UInt256.ofNat I.source.val ≠
                                flopperAddressReturnWord
                                  (auctionPackedSlot (dentIdWord I)) σ_evm I := by
                            simpa [packedSlot, id] using hcallerEq
                          by_cases hnoCode :
                              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                                (flopperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩
                          · exact flopperDentBodyCoreMoveNoCode hcode hperm hwv
                              hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                              (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                              hbegFit (by simpa [id] using hlotOneFit) hsuff
                              hcallerNe hnoCode hdispatch hdecode rd2405 hmemLotOne
                              hreadLotOne hAccounts
                          · have hcodeSize :
                                Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                                  (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩ :=
                              hnoCode
                            by_cases hdepthEq : I.depth = 1024
                            · exact flopperDentBodyCoreMoveCallDepthLimit hcode hwv
                                hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                                (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                                hbegFit (by simpa [id] using hlotOneFit) hsuff
                                hcallerNe hcodeSize hdepthEq hdispatch hdecode rd2405
                                hmemLotOne hreadLotOne hAccounts
                            · have hdepthLt : I.depth.val < 1024 := by
                                have hle : I.depth.val ≤ 1024 :=
                                  Nat.le_of_lt_succ I.depth.isLt
                                have hne : I.depth.val ≠ 1024 := by
                                  intro hval
                                  apply hdepthEq
                                  exact Fin.ext hval
                                omega
                              obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
                              let memCaller := twoWordHashMem id ⟨1⟩ memLotOne
                              let memMap := twoWordHashMem id ⟨1⟩ memCaller
                              let src := UInt256.ofNat I.source.val
                              let vat := flopperAddressReturnWord ⟨2⟩ σ_evm I
                              let guy := flopperAddressReturnWord packedSlot σ_evm I
                              have hmemCaller : memCaller.size = 96 := by
                                simpa [memCaller, id] using
                                  twoWordHashMem_size_96 id ⟨1⟩ hmemLotOne
                              have hread64Caller :
                                  memCaller.readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨128⟩ := by
                                simpa [memCaller, id] using
                                  twoWordHashMem_read64 id ⟨1⟩ hmemLotOne hreadLotOne
                              obtain ⟨_, _, rd2439⟩ :=
                                flopperDentX_callerNeToMove hcallerNe rd2435
                              obtain ⟨cA', σ', zMove, outMove, A', k2545, C2545,
                                  rd2545, hcallMove, houtMoveSize⟩ :=
                                flopperDentX_moveCall
                                  (g := Sat256.ofUInt256 g) hperm hcodeSize hdepthLt
                                  hmemCaller hread64Caller rd2439
                              have hmemMap : memMap.size = 96 := by
                                simpa [memMap, memCaller, id] using
                                  twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
                              have hread64Map :
                                  memMap.readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨128⟩ := by
                                simpa [memMap, memCaller, id] using
                                  twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
                              have hmoveMem96 :
                                  96 ≤ (dentMoveCalldataMem src guy (dentBidWord I)
                                    memMap).size := by
                                rw [dentMoveCalldataMem_size src guy (dentBidWord I)
                                  hmemMap]
                                decide
                              have hmoveRead64 :
                                  (dentMoveCalldataMem src guy (dentBidWord I) memMap
                                    ).readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨128⟩ := by
                                exact dentMoveCalldataMem_read64 src guy (dentBidWord I)
                                  hmemMap hread64Map
                              by_cases hzMove : zMove = true
                              · have rd2545True : RD flopperBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀
                                      (Sat256.ofUInt256 g) A I) ⟨2545⟩
                                    (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
                                      flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                                      dentBidWord I :: dentLotWord I :: dentIdWord I ::
                                      ⟨334⟩ :: flopperSelWord I :: [])
                                    (dentMoveCalldataMem src guy (dentBidWord I) memMap)
                                    (UInt256.ofNat 8) outMove (cA', σ') k2545 C2545 := by
                                  simpa [hzMove, vat, id] using rd2545
                                have hcallMoveTrue :
                                    typedCallViaEVM config
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (EVM.address (AccountAddress.ofNat
                                        (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                                      "move" 0
                                      [.address (AccountAddress.ofNat
                                          (UInt256.ofNat I.source.val).toNat),
                                        .address (AccountAddress.ofNat
                                          (flopperAddressReturnWord
                                            (auctionPackedSlot (dentIdWord I))
                                            σ_evm I).toNat),
                                        .int (Int.ofNat (dentBidWord I).toNat)]
                                      (true,
                                        { initState cA gh bl σ_evm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σ', substate := A',
                                          createdAccounts := cA' },
                                        outMove) true := by
                                  simpa [hzMove, vat, src, guy, packedSlot, id] using hcallMove
                                by_cases hticMoveZero :
                                    flopperUint48Offset20Word packedSlot σ' I = ⟨0⟩
                                · exact flopperDentBodyCoreMoveSuccessTicZero
                                    hcode hperm hwv hlive hguy hticOk
                                    (by simpa [packedSlot, id] using hendGt)
                                    (by simpa [id] using hbid)
                                    (by simpa [id] using hlotLt) hbegFit
                                    (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                    hcodeSize
                                    (by simpa [packedSlot, id] using hticMoveZero)
                                    hdepthLt rd2545True hmoveMem96 hmoveRead64
                                    hcallMoveTrue hdispatch hdecode hAccounts
                                · have hticMoveNe :
                                      flopperUint48Offset20Word
                                        (auctionPackedSlot (dentIdWord I)) σ' I ≠
                                        ⟨0⟩ := by
                                    simpa [packedSlot, id] using hticMoveZero
                                  by_cases haddFit :
                                      (UInt256.land (UInt256.ofNat I.header.timestamp)
                                            flopperUint48Mask).toNat +
                                          (dentRuntimeTtlWord I.codeOwner
                                            (dentRuntimeAfterGuyMap I.codeOwner σ' I)
                                            I).toNat <
                                        2 ^ 48
                                  · exact flopperDentBodyCoreSuccessMoveCallerNeTicNonzero
                                      hcode hperm hwv hlive hguy hticOk
                                      (by simpa [packedSlot, id] using hendGt)
                                      (by simpa [id] using hbid)
                                      (by simpa [id] using hlotLt) hbegFit
                                      (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                      hcodeSize hticMoveNe haddFit rd2545True
                                      hcallMoveTrue hdispatch hdecode hAccounts
                                  · exact flopperDentBodyCoreAddOverflowMoveCallerNeTicNonzero
                                      hcode hperm hwv hlive hguy hticOk
                                      (by simpa [packedSlot, id] using hendGt)
                                      (by simpa [id] using hbid)
                                      (by simpa [id] using hlotLt) hbegFit
                                      (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                      hcodeSize hticMoveNe (Nat.le_of_not_gt haddFit)
                                      rd2545True hcallMoveTrue hdispatch hdecode hAccounts
                              · have hzMoveFalse : zMove = false := by
                                  cases zMove <;> simp at hzMove ⊢
                                have rd2545False : RD flopperBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀
                                      (Sat256.ofUInt256 g) A I) ⟨2545⟩
                                    (⟨0⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
                                      flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                                      dentBidWord I :: dentLotWord I :: dentIdWord I ::
                                      ⟨334⟩ :: flopperSelWord I :: [])
                                    (dentMoveCalldataMem src guy (dentBidWord I) memMap)
                                    (UInt256.ofNat 8) outMove (cA', σ') k2545 C2545 := by
                                  simpa [hzMoveFalse, vat, id] using rd2545
                                have hcallMoveFalse :
                                    typedCallViaEVM config
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (EVM.address (AccountAddress.ofNat
                                        (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                                      "move" 0
                                      [.address (AccountAddress.ofNat
                                          (UInt256.ofNat I.source.val).toNat),
                                        .address (AccountAddress.ofNat
                                          (flopperAddressReturnWord
                                            (auctionPackedSlot (dentIdWord I))
                                            σ_evm I).toNat),
                                        .int (Int.ofNat (dentBidWord I).toNat)]
                                      (false,
                                        { initState cA gh bl σ_evm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σ', substate := A',
                                          createdAccounts := cA' },
                                        outMove) true := by
                                  simpa [hzMoveFalse, vat, src, guy, packedSlot, id]
                                    using hcallMove
                                exact flopperDentBodyCoreMoveCallFailure hcode hwv
                                  hlive hguy hticOk
                                  (by simpa [packedSlot, id] using hendGt)
                                  (by simpa [id] using hbid)
                                  (by simpa [id] using hlotLt) hbegFit
                                  (by simpa [id] using hlotOneFit) hsuff hcallerNe
                                  hcodeSize rd2545False hcallMoveFalse houtMoveSize
                                  hdispatch hdecode hAccounts
                      · exact flopperDentBodyCoreInsufficientDecrease hcode hsize hwv
                          hsz100 hlive hguy hticOk
                          (by simpa [packedSlot, id] using hendGt)
                          (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                          hbegFit (by simpa [id] using hlotOneFit) (by omega)
                          hdispatch hdecode hreach hAccounts
                    · exact flopperDentBodyCoreLotOneOverflow hcode hsize hwv hsz100
                        hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                        (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                        hbegFit (Nat.le_of_not_gt hlotOneFit) hdispatch hdecode hreach
                        hAccounts
                  · exact flopperDentBodyCoreBegLotOverflow hcode hsize hwv hsz100
                      hlive hguy hticOk (by simpa [packedSlot, id] using hendGt)
                      (by simpa [id] using hbid) (by simpa [id] using hlotLt)
                      (Nat.le_of_not_gt hbegFit) hdispatch hdecode hreach hAccounts
                · exact flopperDentBodyCoreLotNotLower hcode hsize hwv hsz100 hlive
                    hguy hticOk (by simpa [packedSlot, id] using hendGt)
                    (by simpa [id] using hbid) (Nat.le_of_not_gt hlotLt)
                    hdispatch hdecode hreach hAccounts
              · exact flopperDentBodyCoreBidMismatch hcode hsize hwv hsz100 hlive
                  hguy hticOk (by simpa [packedSlot, id] using hendGt)
                  (by simpa [id] using hbid) hdispatch hdecode hreach hAccounts
            · exact flopperDentBodyCoreEndFinished hcode hsize hwv hsz100 hlive
                hguy hticOk (Nat.le_of_not_gt hendGt) hdispatch hdecode hreach
                hAccounts
          · exact flopperDentBodyCoreTicFinished hcode hsize hwv hsz100 hlive
              hguy (by simpa [packedSlot, id] using hticZero)
              (Nat.le_of_not_gt hticGt) hdispatch hdecode hreach hAccounts
    · exact flopperDentBodyCoreNotLive hcode hsize hwv hsz100 hlive hdispatch
        hdecode hreach hAccounts
  · exact flopperDentBodyCoreDecodeFailed_short hcode hsize hsz4
      (Nat.lt_of_not_ge hsz100) hdispatch hreach

end Benchmarks.Dss.Flopper
