import Benchmarks.Dss.Flipper.YankCalls

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

theorem flipperYankBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 18)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 18) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
      flipperDispatchYank hsel
    have hdecode := flipperDecode_yank_ok (I := I) hsz36
    have hreach := flipperReachYankBody (fork := fork)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    obtain ⟨_, _, hdecoded⟩ := flipperYankX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    let callerSlot := flipperCallerWardsSlot I
    have hcallerWord : solcSlotWordAt callerSlot σ I =
        solcSlotWordAt callerSlot σ I :=
      rfl
    have hpacked :
        solcSlotWordAt (bidPackedSlotOfWord (yankId I)) σ I =
          solcSlotWordAt (bidPackedSlotOfWord (yankId I)) σ I :=
      rfl
    have hguyEq :
        bidGuyWord (yankId I) σ I = bidGuyWord (yankId I) σ I := by
      simp [bidGuyWord, solcAddressSlotWord, hpacked]
    have hbidEq :
        bidBidWord (yankId I) σ I = bidBidWord (yankId I) σ I :=
      rfl
    have htabEq :
        bidTabWord (yankId I) σ I = bidTabWord (yankId I) σ I :=
      rfl
    by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
    · obtain ⟨_, _, hafterAuth⟩ := flipperYankX_authOk (I := I) hauthEvm hdecoded
      by_cases hguyEvm : bidGuyWord (yankId I) σ I = ⟨0⟩
      · have hguyStele : bidGuyWord (yankId I) σ I = ⟨0⟩ := by
          simpa [← hguyEq] using hguyEvm
        have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
          rw [← hcallerWord]
          exact hauthEvm
        have hbody :
            ExecTransitionBody fork config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (yankLocals I) yankTransition.body .reverted := by
          simpa using
            (flipperYankSourceBodyGuyZero
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthStele hguyStele)
        exact (flipperYankX_guyZero (I := I) hguyEvm hafterAuth)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · obtain ⟨_, _, hafterGuy⟩ := flipperYankX_guyNonzero (I := I) hguyEvm hafterAuth
        by_cases hbidLtEvm :
            (bidBidWord (yankId I) σ I).toNat <
              (bidTabWord (yankId I) σ I).toNat
        · obtain ⟨_, _, hafterBidLt⟩ := flipperYankX_bidLt (I := I) hbidLtEvm hafterGuy
          by_cases hcatZero :
              Reasoning.Theory.extCodeSizeWord σ
                (flipperCatTargetWord σ I) = ⟨0⟩
          · have hcatZeroStele :
                Reasoning.Theory.extCodeSizeWord σ
                    (flipperCatTargetWord σ I) = ⟨0⟩ :=
              hcatZero
            have hnoCode :
                (UInt256.ofNat
                  (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                    (flipperCatAddress σ I)).option 0
                    (fun acc => acc.code.size))).toNat = 0 :=
              flipperCatCode_zero_of_codeSize_zero
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZeroStele
            have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
              rw [← hcallerWord]
              exact hauthEvm
            have hguyStele : bidGuyWord (yankId I) σ I ≠ ⟨0⟩ := by
              intro hzero
              exact hguyEvm (by simpa [hguyEq] using hzero)
            have hbidLtStele :
                (bidBidWord (yankId I) σ I).toNat <
                  (bidTabWord (yankId I) σ I).toNat := by
              simpa [← hbidEq, ← htabEq] using hbidLtEvm
            have hbody :
                ExecTransitionBody fork config contract
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (yankLocals I) yankTransition.body .reverted := by
              simpa using
                (flipperYankSourceBodyCatNoCode
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthStele hguyStele hbidLtStele hnoCode)
            exact (flipperYankX_catNoCode (I := I) hcatZero hafterBidLt)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hcatNeStele :
                Reasoning.Theory.extCodeSizeWord σ
                    (flipperCatTargetWord σ I) ≠ ⟨0⟩ :=
              hcatZero
            have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNeStele
            have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
              rw [← hcallerWord]
              exact hauthEvm
            have hguyStele : bidGuyWord (yankId I) σ I ≠ ⟨0⟩ := by
              intro hzero
              exact hguyEvm (by simpa [hguyEq] using hzero)
            have hbidLtStele :
                (bidBidWord (yankId I) σ I).toNat <
                  (bidTabWord (yankId I) σ I).toNat := by
              simpa [← hbidEq, ← htabEq] using hbidLtEvm
            by_cases hdepthEq : I.depth = 1024
            · have hcatEncode :
                  config.externalABI.encode? "claw"
                    (yankClawArgVals
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I)) =
                      some ((yankCatCallMem σ I).readWithPadding 128 36) := by
                simpa [yankClawArgVals, yankClawArgValsOf, initState, solcSlotWordAt,
                  solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
                  Account.lookupStorage, bidTabWord, bidSlotOfWord, bidBaseOfWord] using
                  yankCatCallMem_encode σ I
              have hcallCat :=
                Reasoning.Theory.callNotMade_depthLimit (fork := fork) (cfg := config)
                  (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (tgt := EVM.address (flipperCatAddress σ I)) (name := "claw")
                  (args :=
                    yankClawArgVals
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
                  (calldata := (yankCatCallMem σ I).readWithPadding 128 36)
                  (callPerm := true) hcatEncode (by simpa [initState] using hdepthEq)
              have hbody :
                  ExecTransitionBody fork config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (yankLocals I) yankTransition.body .reverted := by
                simpa using
                  (flipperYankSourceBodyCatCallFailure
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthStele hguyStele hbidLtStele hcatCode hcallCat)
              exact (flipperYankX_catCallDepthLimit hcatZero hdepthEq hafterBidLt)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hdepthLt : I.depth.val < 1024 := by
                by_contra hnot
                have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
                have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
                have hval : I.depth.val = 1024 := by omega
                exact hdepthEq (Fin.ext hval)
              obtain ⟨σ_cat, zCat, outCat, A_cat, k1346, C1346, rd1346,
                  hcallCatEvmRaw, houtCat⟩ :=
                flipperYankX_catPostCall hcatZero hdepthLt hafterBidLt
              let evm0Evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
              let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
              let evmCatEvm :=
                { evm0Evm with
                  accountMap := σ_cat
                  substate := A_cat
                  }
              have hcallCatEvm :
                  typedCallViaEVM fork config evm0Evm
                    (EVM.address (flipperCatAddress σ I)) "claw" 0
                    [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)]
                    (zCat, evmCatEvm, outCat) true := by
                simpa [evm0Evm, evmCatEvm] using hcallCatEvmRaw
              obtain ⟨σ_cat_stele, A_cat_stele, hcallCatSteleRaw, hCatStateEquiv⟩ :=
                typedCallViaEVM_sameInputs_stateEquiv
                  (evm_stele := evm0Stele) hcallCatEvm
                  rfl
                  (by simp [evm0Evm, evm0Stele, initState])
                  (by simp [evm0Evm, evm0Stele, initState])
              let evmCatStele : EVM.State :=
                { evm0Stele with
                  accountMap := σ_cat_stele
                  substate := A_cat_stele
                  }
              have hcatTargetEq :
                  EVM.address (flipperCatAddress σ I) =
                    EVM.address (flipperCatAddress σ I) := rfl
              have hcatArgsEq :
                  [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)] =
                    yankClawArgVals evm0Stele := by
                simp [yankClawArgVals, yankClawArgValsOf, evm0Stele, initState,
                  Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                  bidTabWord, solcSlotWordAt, solcSlotWord]
              have hcallCatStele :
                  typedCallViaEVM fork config evm0Stele
                    (EVM.address (flipperCatAddress σ I)) "claw" 0
                    (yankClawArgVals evm0Stele) (zCat, evmCatStele, outCat) true := by
                have hcallCatSteleRaw' :
                    typedCallViaEVM fork config evm0Stele
                      (EVM.address (flipperCatAddress σ I)) "claw" 0
                      [Value.int (Int.ofNat (bidTabWord (yankId I) σ I).toNat)]
                      (zCat, evmCatStele, outCat) true := by
                  simpa [evmCatStele, evmCatEvm, hcatTargetEq] using hcallCatSteleRaw
                rw [← hcatArgsEq]
                exact hcallCatSteleRaw'
              cases zCat
              · have hcallCatSteleFalse :
                    typedCallViaEVM fork config evm0Stele
                      (EVM.address (flipperCatAddress σ I)) "claw" 0
                      (yankClawArgVals evm0Stele) (false, evmCatStele, outCat) true := by
                  simpa using hcallCatStele
                have hbody :
                    ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                      yankTransition.body .reverted := by
                  simpa [evm0Stele] using
                    (flipperYankSourceBodyCatCallFailure
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      hwv hauthStele hguyStele hbidLtStele hcatCode hcallCatSteleFalse)
                exact (flipperYankX_catCallFailure (by simpa using rd1346) houtCat)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have rd1346True : RD fork flipperBytecode I (Sat256.ofUInt256 g)
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1346⟩
                    (⟨1⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
                      flipperCatTargetWord σ I :: yankId I :: ⟨323⟩ ::
                      flipperSelWord I :: [])
                    (yankCatCallMem σ I) (UInt256.ofNat 6) outCat σ_cat
                    k1346 C1346 := by
                  simpa using rd1346
                obtain ⟨_, _, rd1365⟩ := flipperYankX_catCallSuccessToVatStart rd1346True
                have hcallCatSteleTrue :
                    typedCallViaEVM fork config evm0Stele
                      (EVM.address (flipperCatAddress σ I)) "claw" 0
                      (yankClawArgVals evm0Stele) (true, evmCatStele, outCat) true := by
                  simpa using hcallCatStele
                have hCatStateEquiv' : EVMStateEquiv evmCatEvm evmCatStele := by
                  simpa [evmCatStele, evmCatEvm] using hCatStateEquiv
                have hAccountsCat : Eq σ_cat σ_cat_stele := by
                  simpa [evmCatEvm, evmCatStele] using hCatStateEquiv'.accountMap
                by_cases hvatZero :
                    Reasoning.Theory.extCodeSizeWord σ_cat
                      (flipperVatTargetWord σ_cat I) = ⟨0⟩
                · have hvatZeroStele :
                      Reasoning.Theory.extCodeSizeWord σ_cat_stele
                          (flipperVatTargetWord σ_cat_stele I) = ⟨0⟩ :=
                    by rw [← hAccountsCat]; exact hvatZero
                  have hvatNoCode :
                      (UInt256.ofNat
                        ((evmCatStele.lookupAccount
                          (flipperVatAddress evmCatStele.accountMap
                            evmCatStele.executionEnv)).option
                          0 (fun acc => acc.code.size))).toNat = 0 := by
                    simpa [evmCatStele, evm0Stele, initState, State.lookupAccount] using
                      extCodeSizeWord_zero_lookup_code_zero
                        (σ := σ_cat_stele) (target := flipperVatTargetWord σ_cat_stele I)
                        (addr := flipperVatAddress σ_cat_stele I)
                        (flipperVatAddress_eq_target σ_cat_stele I) hvatZeroStele
                  have hbody :
                      ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                        yankTransition.body .reverted := by
                    simpa [evm0Stele] using
                      (flipperYankSourceBodyVatNoCode
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmCat := evmCatStele) (outCat := outCat)
                        hwv hauthStele hguyStele hbidLtStele hcatCode hcallCatSteleTrue
                        hvatNoCode)
                  exact (flipperYankX_vatNoCode hvatZero rd1365)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hvatNeStele :
                      Reasoning.Theory.extCodeSizeWord σ_cat_stele
                          (flipperVatTargetWord σ_cat_stele I) ≠ ⟨0⟩ :=
                    by rw [← hAccountsCat]; exact hvatZero
                  have hvatCodeStele :
                      0 <
                        (UInt256.ofNat
                          ((evmCatStele.lookupAccount
                            (flipperVatAddress evmCatStele.accountMap
                              evmCatStele.executionEnv)).option
                            0 (fun acc => acc.code.size))).toNat := by
                    simpa [evmCatStele, evm0Stele, initState, State.lookupAccount] using
                      extCodeSizeWord_ne_zero_lookup_code_pos
                        (σ := σ_cat_stele) (target := flipperVatTargetWord σ_cat_stele I)
                        (addr := flipperVatAddress σ_cat_stele I)
                        (flipperVatAddress_eq_target σ_cat_stele I) hvatNeStele
                  obtain ⟨σ_vat, zVat, outVat, A_vat, k1482, C1482, rd1482,
                      hcallVatEvmRaw, houtVat⟩ :=
                    flipperYankX_vatPostCall (Acur := A_cat) hvatZero hdepthLt rd1365
                  let evmVatEvm : EVM.State :=
                    { evmCatEvm with
                      accountMap := σ_vat
                      substate := A_vat
                      }
                  have hcallVatEvm :
                      typedCallViaEVM fork config evmCatEvm
                        (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
                        (yankFluxArgValsOf evmCatEvm (yankId I))
                        (zVat, evmVatEvm, outVat) true := by
                    simpa [evmCatEvm, evmVatEvm] using hcallVatEvmRaw
                  obtain ⟨σ_vat_stele, A_vat_stele, hcallVatSteleRaw, hVatStateEquiv⟩ :=
                    typedCallViaEVM_sameInputs_stateEquiv
                      (evm_stele := evmCatStele) hcallVatEvm hCatStateEquiv'.accountMap
                      (by simp [evmCatEvm, evmCatStele, evm0Evm, evm0Stele, initState])
                      hCatStateEquiv'.executionEnv
                  let evmVatStele : EVM.State :=
                    { evmCatStele with
                      accountMap := σ_vat_stele
                      substate := A_vat_stele
                      }
                  have hvatTargetEq :
                      EVM.address (flipperVatAddress σ_cat I) =
                        EVM.address
                          (flipperVatAddress evmCatStele.accountMap
                            evmCatStele.executionEnv) := by
                    have haddr : flipperVatAddress σ_cat I =
                        flipperVatAddress σ_cat_stele I := by rw [← hAccountsCat]
                    rw [haddr]
                    simp [evmCatStele, evm0Stele, initState]
                  have hfluxArgsEq :
                      yankFluxArgValsOf evmCatEvm (yankId I) =
                        yankFluxArgValsOf evmCatStele (yankId I) := by
                    simp [yankFluxArgValsOf, Stele.EVM.storageLoad, State.lookupAccount,
                      Account.lookupStorage, hCatStateEquiv'.executionEnv,
                      hCatStateEquiv'.accountMap]
                  have hcallVatStele :
                      typedCallViaEVM fork config evmCatStele
                        (EVM.address
                          (flipperVatAddress evmCatStele.accountMap
                            evmCatStele.executionEnv)) "flux" 0
                        (yankFluxArgValsOf evmCatStele (yankId I))
                        (zVat, evmVatStele, outVat) true := by
                    have hcallVatSteleRaw' :
                        typedCallViaEVM fork config evmCatStele
                          (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
                          (yankFluxArgValsOf evmCatEvm (yankId I))
                          (zVat, evmVatStele, outVat) true := by
                      simpa [evmVatStele, evmVatEvm] using hcallVatSteleRaw
                    rw [hvatTargetEq, hfluxArgsEq] at hcallVatSteleRaw'
                    exact hcallVatSteleRaw'
                  cases zVat
                  · have rd1482False : RD fork flipperBytecode I (Sat256.ofUInt256 g)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
                        (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                          flipperVatTargetWord σ_cat I :: yankId I :: ⟨323⟩ ::
                          flipperSelWord I :: [])
                        (yankVatFluxCallMem σ σ_cat I) (UInt256.ofNat 9) outVat
                        σ_vat k1482 C1482 := by
                      simpa using rd1482
                    have hcallVatSteleFalse :
                        typedCallViaEVM fork config evmCatStele
                          (EVM.address
                            (flipperVatAddress evmCatStele.accountMap
                              evmCatStele.executionEnv)) "flux" 0
                          (yankFluxArgValsOf evmCatStele (yankId I))
                          (false, evmVatStele, outVat) true := by
                      simpa using hcallVatStele
                    have hbody :
                        ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                          yankTransition.body .reverted := by
                      simpa [evm0Stele] using
                        (flipperYankSourceBodyVatCallFailure
                          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmCat := evmCatStele) (evmVat := evmVatStele)
                          (outCat := outCat) (outVat := outVat)
                          hwv hauthStele hguyStele hbidLtStele hcatCode
                          hcallCatSteleTrue hvatCodeStele hcallVatSteleFalse)
                    exact (flipperYankX_vatCallFailure rd1482False houtVat)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have rd1482True : RD fork flipperBytecode I (Sat256.ofUInt256 g)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
                        (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                          flipperVatTargetWord σ_cat I :: yankId I :: ⟨323⟩ ::
                          flipperSelWord I :: [])
                        (yankVatFluxCallMem σ σ_cat I) (UInt256.ofNat 9) outVat
                        σ_vat k1482 C1482 := by
                      simpa using rd1482
                    obtain ⟨_, _, rd1501⟩ :=
                      flipperYankX_vatCallSuccessToMoveStart rd1482True
                    have hcallVatSteleTrue :
                        typedCallViaEVM fork config evmCatStele
                          (EVM.address
                            (flipperVatAddress evmCatStele.accountMap
                              evmCatStele.executionEnv)) "flux" 0
                          (yankFluxArgValsOf evmCatStele (yankId I))
                          (true, evmVatStele, outVat) true := by
                      simpa using hcallVatStele
                    have hVatStateEquiv' : EVMStateEquiv evmVatEvm evmVatStele := by
                      simpa [evmVatEvm, evmVatStele] using hVatStateEquiv
                    have hAccountsVat : Eq σ_vat σ_vat_stele := by
                      simpa [evmVatEvm, evmVatStele] using hVatStateEquiv'.accountMap
                    by_cases hmoveZero :
                        Reasoning.Theory.extCodeSizeWord σ_vat
                          (flipperVatTargetWord σ_vat I) = ⟨0⟩
                    · have hmoveZeroStele :
                          Reasoning.Theory.extCodeSizeWord σ_vat_stele
                              (flipperVatTargetWord σ_vat_stele I) = ⟨0⟩ :=
                        by rw [← hAccountsVat]; exact hmoveZero
                      have hmoveNoCode :
                          (UInt256.ofNat
                            ((evmVatStele.lookupAccount
                              (flipperVatAddress evmVatStele.accountMap
                                evmVatStele.executionEnv)).option
                              0 (fun acc => acc.code.size))).toNat = 0 := by
                        simpa [evmVatStele, evmCatStele, evm0Stele, initState,
                          State.lookupAccount] using
                          extCodeSizeWord_zero_lookup_code_zero
                            (σ := σ_vat_stele)
                            (target := flipperVatTargetWord σ_vat_stele I)
                            (addr := flipperVatAddress σ_vat_stele I)
                            (flipperVatAddress_eq_target σ_vat_stele I) hmoveZeroStele
                      have hbody :
                          ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                            yankTransition.body .reverted := by
                        simpa [evm0Stele] using
                          (flipperYankSourceBodyMoveNoCode
                            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmCat := evmCatStele) (evmVat := evmVatStele)
                            (outCat := outCat) (outVat := outVat)
                            hwv hauthStele hguyStele hbidLtStele hcatCode
                            hcallCatSteleTrue hvatCodeStele hcallVatSteleTrue hmoveNoCode)
                      exact (flipperYankX_moveNoCode hmoveZero rd1501)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hmoveNeStele :
                          Reasoning.Theory.extCodeSizeWord σ_vat_stele
                              (flipperVatTargetWord σ_vat_stele I) ≠ ⟨0⟩ :=
                        by rw [← hAccountsVat]; exact hmoveZero
                      have hmoveCodeStele :
                          0 <
                            (UInt256.ofNat
                              ((evmVatStele.lookupAccount
                                (flipperVatAddress evmVatStele.accountMap
                                  evmVatStele.executionEnv)).option
                                0 (fun acc => acc.code.size))).toNat := by
                        simpa [evmVatStele, evmCatStele, evm0Stele, initState,
                          State.lookupAccount] using
                          extCodeSizeWord_ne_zero_lookup_code_pos
                            (σ := σ_vat_stele)
                            (target := flipperVatTargetWord σ_vat_stele I)
                            (addr := flipperVatAddress σ_vat_stele I)
                            (flipperVatAddress_eq_target σ_vat_stele I) hmoveNeStele
                      obtain ⟨σ_move, zMove, outMove, A_move, k1615,
                          C1615, rd1615, hcallMoveEvmRaw, houtMove⟩ :=
                        flipperYankX_movePostCall (Acur := A_vat)
                          hmoveZero hdepthLt rd1501
                      let evmMoveEvm : EVM.State :=
                        { evmVatEvm with
                          accountMap := σ_move
                          substate := A_move
                          }
                      have hcallMoveEvm :
                          typedCallViaEVM fork config evmVatEvm
                            (EVM.address (flipperVatAddress σ_vat I)) "move" 0
                            (yankMoveArgValsOf evmVatEvm (yankId I))
                            (zMove, evmMoveEvm, outMove) true := by
                        simpa [evmVatEvm, evmMoveEvm] using hcallMoveEvmRaw
                      obtain ⟨σ_move_stele, A_move_stele, hcallMoveSteleRaw,
                          hMoveStateEquiv⟩ :=
                        typedCallViaEVM_sameInputs_stateEquiv
                          (evm_stele := evmVatStele) hcallMoveEvm hVatStateEquiv'.accountMap
                          (by
                            simp [evmVatEvm, evmVatStele, evmCatEvm, evmCatStele,
                              evm0Evm, evm0Stele, initState])
                          hVatStateEquiv'.executionEnv
                      let evmMoveStele : EVM.State :=
                        { evmVatStele with
                          accountMap := σ_move_stele
                          substate := A_move_stele
                          }
                      have hmoveTargetEq :
                          EVM.address (flipperVatAddress σ_vat I) =
                            EVM.address
                              (flipperVatAddress evmVatStele.accountMap
                                evmVatStele.executionEnv) := by
                        have haddr : flipperVatAddress σ_vat I =
                            flipperVatAddress σ_vat_stele I :=
                          by rw [← hAccountsVat]
                        rw [haddr]
                        simp [evmVatStele, evmCatStele, evm0Stele, initState]
                      have hmoveArgsEq :
                          yankMoveArgValsOf evmVatEvm (yankId I) =
                            yankMoveArgValsOf evmVatStele (yankId I) := by
                        simp [yankMoveArgValsOf, Stele.EVM.storageLoad, State.lookupAccount,
                          Account.lookupStorage, hVatStateEquiv'.executionEnv,
                          hVatStateEquiv'.accountMap]
                      have hcallMoveStele :
                          typedCallViaEVM fork config evmVatStele
                            (EVM.address
                              (flipperVatAddress evmVatStele.accountMap
                                evmVatStele.executionEnv)) "move" 0
                            (yankMoveArgValsOf evmVatStele (yankId I))
                            (zMove, evmMoveStele, outMove) true := by
                        have hcallMoveSteleRaw' :
                            typedCallViaEVM fork config evmVatStele
                              (EVM.address (flipperVatAddress σ_vat I)) "move" 0
                              (yankMoveArgValsOf evmVatEvm (yankId I))
                              (zMove, evmMoveStele, outMove) true := by
                          simpa [evmMoveStele, evmMoveEvm] using hcallMoveSteleRaw
                        rw [hmoveTargetEq, hmoveArgsEq] at hcallMoveSteleRaw'
                        exact hcallMoveSteleRaw'
                      cases zMove
                      · have rd1615False : RD fork flipperBytecode I (Sat256.ofUInt256 g)
                            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨1615⟩
                            (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
                              flipperVatTargetWord σ_vat I :: yankId I :: ⟨323⟩ ::
                              flipperSelWord I :: [])
                            (yankVatMoveCallMem σ σ_cat σ_vat I) (UInt256.ofNat 9)
                            outMove σ_move k1615 C1615 := by
                          simpa using rd1615
                        have hcallMoveSteleFalse :
                            typedCallViaEVM fork config evmVatStele
                              (EVM.address
                                (flipperVatAddress evmVatStele.accountMap
                                  evmVatStele.executionEnv)) "move" 0
                              (yankMoveArgValsOf evmVatStele (yankId I))
                              (false, evmMoveStele, outMove) true := by
                          simpa using hcallMoveStele
                        have hbody :
                            ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                              yankTransition.body .reverted := by
                          simpa [evm0Stele] using
                            (flipperYankSourceBodyMoveCallFailure
                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmCat := evmCatStele) (evmVat := evmVatStele)
                              (evmMove := evmMoveStele)
                              (outCat := outCat) (outVat := outVat) (outMove := outMove)
                              hwv hauthStele hguyStele hbidLtStele hcatCode
                              hcallCatSteleTrue hvatCodeStele hcallVatSteleTrue
                              hmoveCodeStele hcallMoveSteleFalse)
                        exact (flipperYankX_moveCallFailure rd1615False houtMove)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have rd1615True : RD fork flipperBytecode I (Sat256.ofUInt256 g)
                            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨1615⟩
                            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
                              flipperVatTargetWord σ_vat I :: yankId I :: ⟨323⟩ ::
                              flipperSelWord I :: [])
                            (yankVatMoveCallMem σ σ_cat σ_vat I) (UInt256.ofNat 9)
                            outMove σ_move k1615 C1615 := by
                          simpa using rd1615
                        obtain ⟨k1635, C1635, rd1635⟩ :=
                          flipperYankX_moveCallSuccessToDeleteStart rd1615True
                        have hretSplit :=
                          flipperYankX_deleteReturnFromPostCallSplit
                            (σmem := σ)
                            (σflux := σ_cat) (σcall := σ_vat) (σ := σ_move)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (k := k1635) (C := C1635)
                            (out := outMove) rd1635
                        have hcallMoveSteleTrue :
                            typedCallViaEVM fork config evmVatStele
                              (EVM.address
                                (flipperVatAddress evmVatStele.accountMap
                                  evmVatStele.executionEnv)) "move" 0
                              (yankMoveArgValsOf evmVatStele (yankId I))
                              (true, evmMoveStele, outMove) true := by
                          simpa using hcallMoveStele
                        let locals3 : Store :=
                          (((yankLocals I).insert "_clawRet" (collapseReturns [])).insert
                            "_fluxRet" (collapseReturns [])).insert "_moveRet"
                            (collapseReturns [])
                        have hbodySplit :
                            (I.perm = true → ExecTransitionBody fork config contract evm0Stele (yankLocals I)
                              yankTransition.body
                              (.returned { contract := contract, locals := locals3 }
                                (bidDeletedEVM evmMoveStele (yankId I)) none)) ∧
                            (I.perm = false → ExecTransitionBody fork config contract evm0Stele
                              (yankLocals I) yankTransition.body .staticViolation) := by
                          simpa [evm0Stele, locals3] using
                            (flipperYankSourceBodySuccessSplit
                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmCat := evmCatStele) (evmVat := evmVatStele)
                              (evmMove := evmMoveStele)
                              (outCat := outCat) (outVat := outVat) (outMove := outMove)
                              hwv hauthStele hguyStele hbidLtStele hcatCode
                              hcallCatSteleTrue hvatCodeStele hcallVatSteleTrue
                              hmoveCodeStele hcallMoveSteleTrue)
                        rcases hretSplit with ⟨hperm, hret⟩ | ⟨hperm, hstatic⟩
                        swap
                        · exact hstatic.reEquivStaticHalt
                            hcode hdispatch hdecode (hbodySplit.2 hperm)
                        have hMoveStateEquiv' : EVMStateEquiv evmMoveEvm evmMoveStele := by
                          simpa [evmMoveEvm, evmMoveStele] using hMoveStateEquiv
                        have hMoveAccounts : Eq σ_move σ_move_stele := by
                          simpa [evmMoveEvm, evmMoveStele] using hMoveStateEquiv'.accountMap
                        have hcollapsed :
                            Eq (yankBidDeleteAccountMap I σ_move (yankId I))
                              (bidDeleteCollapsedAccountMap I.codeOwner σ_move_stele
                                (yankId I)) := by
                          simpa [yankBidDeleteAccountMap] using
                            congrArg (fun m => bidDeleteCollapsedAccountMap I.codeOwner m
                              (yankId I)) hMoveAccounts
                        have hdeleted :
                            Eq
                              (bidDeleteCollapsedAccountMap I.codeOwner σ_move_stele
                                (yankId I))
                              (bidDeletedEVM evmMoveStele (yankId I)).accountMap := by
                          exact bidDeleteCollapsedAccountMap_eq_bidDeletedEVM
                            evmMoveStele (yankId I)
                        have haccounts :
                            Eq (yankBidDeleteAccountMap I σ_move (yankId I))
                              (bidDeletedEVM evmMoveStele (yankId I)).accountMap :=
                          Eq.trans hcollapsed hdeleted
                        exact hret.reEquivExecutionGen hcode hdispatch hdecode
                          (hbodySplit.1 hperm)
                          haccounts
                          (by
                            rw [show yankTransition.returnType = [] by rfl]
                            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))
        · have hgeEvm :
              (bidTabWord (yankId I) σ I).toNat ≤
                (bidBidWord (yankId I) σ I).toNat := by
            omega
          have hgeStele :
              (bidTabWord (yankId I) σ I).toNat ≤
                (bidBidWord (yankId I) σ I).toNat := by
            simpa [← hbidEq, ← htabEq] using hgeEvm
          have hguyStele : bidGuyWord (yankId I) σ I ≠ ⟨0⟩ := by
            intro hzero
            exact hguyEvm (by simpa [hguyEq] using hzero)
          have hauthStele : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
            rw [← hcallerWord]
            exact hauthEvm
          have hbody :
              ExecTransitionBody fork config contract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (yankLocals I) yankTransition.body .reverted := by
            simpa using
              (flipperYankSourceBodyNotDent
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthStele hguyStele hgeStele)
          exact (flipperYankX_bidNotLt (I := I) hgeEvm hafterGuy)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthStele : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
        intro hstele
        exact hauthEvm (by rw [hcallerWord, hstele])
      let locals : Store := yankLocals I
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody fork config contract evm0 locals yankTransition.body .reverted := by
        have hguard := flipperAuthGuardEval_false
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (locals := locals) (by simp [locals, yankLocals]) hauthStele
        have hblock := nonpayableSecondRequireReverts (fork := fork)
          (cfg := config) (stele := { contract := contract, locals := locals })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest :=
            [.require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr),
             .require (.binary .lt (.storage (bidsF (.var "id") "bid"))
                (.storage (bidsF (.var "id") "tab")))] ++
            checkedExternalCallStmts (.storage catRef) "claw" (.intLit 0)
              [.storage (bidsF (.var "id") "tab")] "_clawRet" ++
            checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
              [.storage ilkRef, thisAddr, sender, .storage (bidsF (.var "id") "lot")]
              "_fluxRet" ++
            checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_moveRet" ++
            [ .delete (bidRef (.var "id")) ])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, yankTransition, nonpayable, auth, evm0, locals,
          yankLocals] using ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, flipperCallerWardsSlot, solcSlotWordAt] using hauthEvm
      have hrev := RD.flipperAuthCheckRevert
        (pc := ⟨967⟩) (okPc := ⟨1049⟩) (key := yankId I) (ret := ⟨323⟩)
        (R := [flipperSelWord I])
        hdecoded
        (by
          unfold flipperAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold flipperAuthCodecopyRevertTailWf flipperAuthTailPc
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 18) rfl hsel
    have hshort : I.calldata.size < 36 := by omega
    have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
      flipperDispatchYank hsel
    have hreach := flipperReachYankBody (fork := fork)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperYankX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_yank_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper
