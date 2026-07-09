import Benchmarks.Dss.Flipper.YankCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

theorem flipperYankBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 18))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 18) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
      flipperDispatchYank hsel
    have hdecode := flipperDecode_yank_ok (I := I) hsz36
    have hreach := flipperReachYankBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    obtain ⟨_, _, hdecoded⟩ := flipperYankX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    let callerSlot := flipperCallerWardsSlot I
    have hcallerWord : flipperSlotWord callerSlot σ_evm I =
        flipperSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hpacked :
        flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ_evm I =
          flipperSlotWord (bidPackedSlotOfWord (yankId I)) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidPackedSlotOfWord (yankId I)) ⟨0⟩
    have hguyEq :
        bidGuyWord (yankId I) σ_evm I = bidGuyWord (yankId I) σ_solm I := by
      simp [bidGuyWord, flipperAddressReturnWord, hpacked]
    have hbidEq :
        bidBidWord (yankId I) σ_evm I = bidBidWord (yankId I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (bidBaseOfWord (yankId I)) ⟨0⟩
    have htabEq :
        bidTabWord (yankId I) σ_evm I = bidTabWord (yankId I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidSlotOfWord (yankId I) ⟨5⟩) ⟨0⟩
    by_cases hauthEvm : flipperSlotWord callerSlot σ_evm I = ⟨1⟩
    · obtain ⟨_, _, hafterAuth⟩ := flipperYankX_authOk (I := I) hauthEvm hdecoded
      by_cases hguyEvm : bidGuyWord (yankId I) σ_evm I = ⟨0⟩
      · have hguySolm : bidGuyWord (yankId I) σ_solm I = ⟨0⟩ := by
          simpa [← hguyEq] using hguyEvm
        have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
          rw [← hcallerWord]
          exact hauthEvm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (yankLocals I) yankTransition.body .reverted := by
          simpa using
            (flipperYankSourceBodyGuyZero (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hguySolm)
        exact (flipperYankX_guyZero (I := I) hguyEvm hafterAuth)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · obtain ⟨_, _, hafterGuy⟩ := flipperYankX_guyNonzero (I := I) hguyEvm hafterAuth
        by_cases hbidLtEvm :
            (bidBidWord (yankId I) σ_evm I).toNat <
              (bidTabWord (yankId I) σ_evm I).toNat
        · obtain ⟨_, _, hafterBidLt⟩ := flipperYankX_bidLt (I := I) hbidLtEvm hafterGuy
          by_cases hcatZero :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                (flipperCatTargetWord σ_evm I) = ⟨0⟩
          · have hcatZeroSolm :
                Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                    (flipperCatTargetWord σ_solm I) = ⟨0⟩ :=
              flipperCatCodeSize_zero_accountMapEquiv hAccounts hcatZero
            have hnoCode :
                (UInt256.ofNat
                  (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                    (flipperCatAddress σ_solm I)).option 0
                    (fun acc => acc.code.size))).toNat = 0 :=
              flipperCatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZeroSolm
            have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
              rw [← hcallerWord]
              exact hauthEvm
            have hguySolm : bidGuyWord (yankId I) σ_solm I ≠ ⟨0⟩ := by
              intro hzero
              exact hguyEvm (by simpa [hguyEq] using hzero)
            have hbidLtSolm :
                (bidBidWord (yankId I) σ_solm I).toNat <
                  (bidTabWord (yankId I) σ_solm I).toNat := by
              simpa [← hbidEq, ← htabEq] using hbidLtEvm
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (yankLocals I) yankTransition.body .reverted := by
              simpa using
                (flipperYankSourceBodyCatNoCode (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthSolm hguySolm hbidLtSolm hnoCode)
            exact (flipperYankX_catNoCode (I := I) hcatZero hafterBidLt)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hcatNeSolm :
                Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                    (flipperCatTargetWord σ_solm I) ≠ ⟨0⟩ :=
              flipperCatCodeSize_ne_zero_accountMapEquiv hAccounts hcatZero
            have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero
              (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNeSolm
            have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
              rw [← hcallerWord]
              exact hauthEvm
            have hguySolm : bidGuyWord (yankId I) σ_solm I ≠ ⟨0⟩ := by
              intro hzero
              exact hguyEvm (by simpa [hguyEq] using hzero)
            have hbidLtSolm :
                (bidBidWord (yankId I) σ_solm I).toNat <
                  (bidTabWord (yankId I) σ_solm I).toNat := by
              simpa [← hbidEq, ← htabEq] using hbidLtEvm
            by_cases hdepthEq : I.depth = 1024
            · have hcatEncode :
                  config.externalABI.encode? "claw"
                    (yankClawArgVals
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
                      some ((yankCatCallMem σ_solm I).readWithPadding 128 36) := by
                simpa [yankClawArgVals, yankClawArgValsOf, initState, flipperSlotWord,
                  solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                  Account.lookupStorage, bidTabWord, bidSlotOfWord, bidBaseOfWord] using
                  yankCatCallMem_encode σ_solm I
              have hcallCat :=
                Reasoning.Theory.callNotMade_depthLimit (cfg := config)
                  (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (tgt := EVM.address (flipperCatAddress σ_solm I)) (name := "claw")
                  (args :=
                    yankClawArgVals
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
                  (calldata := (yankCatCallMem σ_solm I).readWithPadding 128 36)
                  (callPerm := true) hcatEncode (by simpa [initState] using hdepthEq)
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (yankLocals I) yankTransition.body .reverted := by
                simpa using
                  (flipperYankSourceBodyCatCallFailure (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hguySolm hbidLtSolm hcatCode hcallCat)
              exact (flipperYankX_catCallDepthLimit hcatZero hdepthEq hafterBidLt)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hdepthLt : I.depth.val < 1024 := by
                by_contra hnot
                have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
                have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
                have hval : I.depth.val = 1024 := by omega
                exact hdepthEq (Fin.ext hval)
              obtain ⟨cA_cat, σ_cat, zCat, outCat, A_cat, k1346, C1346, rd1346,
                  hcallCatEvmRaw, houtCat⟩ :=
                flipperYankX_catPostCall hcatZero hperm hdepthLt hafterBidLt
              let evm0Evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
              let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evmCatEvm :=
                { evm0Evm with
                  accountMap := σ_cat
                  substate := A_cat
                  createdAccounts := cA_cat }
              have hcallCatEvm :
                  typedCallViaEVM config evm0Evm
                    (EVM.address (flipperCatAddress σ_evm I)) "claw" 0
                    [Value.int (Int.ofNat (bidTabWord (yankId I) σ_evm I).toNat)]
                    (zCat, evmCatEvm, outCat) true := by
                simpa [evm0Evm, evmCatEvm] using hcallCatEvmRaw
              obtain ⟨σ_cat_solm, A_cat_solm, hcallCatSolmRaw, hCatStateEquiv⟩ :=
                flipper_typedCallViaEVM_accountMapEquiv_noSubstate
                  (evm_solm := evm0Solm) hcallCatEvm
                  (by simpa [evm0Evm, evm0Solm] using hAccounts)
                  (by simp [evm0Evm, evm0Solm, initState])
                  (by simp [evm0Evm, evm0Solm, initState])
                  (by simp [evm0Evm, evm0Solm, initState])
                  (by simp [evm0Evm, evm0Solm, initState])
                  (by simp [evm0Evm, evm0Solm, initState])
              let evmCatSolm : EVM.State :=
                { evm0Solm with
                  accountMap := σ_cat_solm
                  substate := A_cat_solm
                  createdAccounts := cA_cat }
              have hcatTargetEq :
                  EVM.address (flipperCatAddress σ_evm I) =
                    EVM.address (flipperCatAddress σ_solm I) := by
                rw [flipperCatAddress_accountMapEquiv hAccounts]
              have hcatArgsEqRaw :
                  [Value.int (Int.ofNat (bidTabWord (yankId I) σ_evm I).toNat)] =
                    [Value.int (Int.ofNat (bidTabWord (yankId I) σ_solm I).toNat)] := by
                rw [htabEq]
              have hcatArgsEq :
                  [Value.int (Int.ofNat (bidTabWord (yankId I) σ_evm I).toNat)] =
                    yankClawArgVals evm0Solm := by
                simpa [yankClawArgVals, yankClawArgValsOf, evm0Solm, initState,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                  bidTabWord] using hcatArgsEqRaw
              have hcallCatSolm :
                  typedCallViaEVM config evm0Solm
                    (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
                    (yankClawArgVals evm0Solm) (zCat, evmCatSolm, outCat) true := by
                have hcallCatSolmRaw' :
                    typedCallViaEVM config evm0Solm
                      (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
                      [Value.int (Int.ofNat (bidTabWord (yankId I) σ_evm I).toNat)]
                      (zCat, evmCatSolm, outCat) true := by
                  simpa [evmCatSolm, evmCatEvm, hcatTargetEq] using hcallCatSolmRaw
                rw [← hcatArgsEq]
                exact hcallCatSolmRaw'
              cases zCat
              · have hcallCatSolmFalse :
                    typedCallViaEVM config evm0Solm
                      (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
                      (yankClawArgVals evm0Solm) (false, evmCatSolm, outCat) true := by
                  simpa using hcallCatSolm
                have hbody :
                    ExecTransitionBody config contract evm0Solm (yankLocals I)
                      yankTransition.body .reverted := by
                  simpa [evm0Solm] using
                    (flipperYankSourceBodyCatCallFailure
                      (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      hwv hauthSolm hguySolm hbidLtSolm hcatCode hcallCatSolmFalse)
                exact (flipperYankX_catCallFailure (by simpa using rd1346) houtCat)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have rd1346True : RD flipperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1346⟩
                    (⟨1⟩ :: ⟨164⟩ :: ⟨3865913243⟩ ::
                      flipperCatTargetWord σ_evm I :: yankId I :: ⟨323⟩ ::
                      flipperSelWord I :: [])
                    (yankCatCallMem σ_evm I) (UInt256.ofNat 6) outCat (cA_cat, σ_cat)
                    k1346 C1346 := by
                  simpa using rd1346
                obtain ⟨_, _, rd1365⟩ := flipperYankX_catCallSuccessToVatStart rd1346True
                have hcallCatSolmTrue :
                    typedCallViaEVM config evm0Solm
                      (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
                      (yankClawArgVals evm0Solm) (true, evmCatSolm, outCat) true := by
                  simpa using hcallCatSolm
                have hCatStateEquiv' : EVMStateEquiv evmCatEvm evmCatSolm := by
                  simpa [evmCatSolm, evmCatEvm] using hCatStateEquiv
                have hAccountsCat : accountMapEquiv σ_cat σ_cat_solm := by
                  simpa [evmCatEvm, evmCatSolm] using hCatStateEquiv'.accountMap
                by_cases hvatZero :
                    Reasoning.Theory.uniswapExtCodeSizeWord σ_cat
                      (flipperVatTargetWord σ_cat I) = ⟨0⟩
                · have hvatZeroSolm :
                      Reasoning.Theory.uniswapExtCodeSizeWord σ_cat_solm
                          (flipperVatTargetWord σ_cat_solm I) = ⟨0⟩ :=
                    flipperVatCodeSize_zero_accountMapEquiv hAccountsCat hvatZero
                  have hvatNoCode :
                      (UInt256.ofNat
                        ((evmCatSolm.lookupAccount
                          (flipperVatAddress evmCatSolm.accountMap
                            evmCatSolm.executionEnv)).option
                          0 (fun acc => acc.code.size))).toNat = 0 := by
                    simpa [evmCatSolm, evm0Solm, initState, State.lookupAccount] using
                      flipper_uniswapExtCodeSizeWord_zero_lookup_code_zero
                        (σ := σ_cat_solm) (target := flipperVatTargetWord σ_cat_solm I)
                        (addr := flipperVatAddress σ_cat_solm I)
                        (flipperVatAddress_eq_target σ_cat_solm I) hvatZeroSolm
                  have hbody :
                      ExecTransitionBody config contract evm0Solm (yankLocals I)
                        yankTransition.body .reverted := by
                    simpa [evm0Solm] using
                      (flipperYankSourceBodyVatNoCode (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmCat := evmCatSolm) (outCat := outCat)
                        hwv hauthSolm hguySolm hbidLtSolm hcatCode hcallCatSolmTrue
                        hvatNoCode)
                  exact (flipperYankX_vatNoCode hvatZero rd1365)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hvatNeSolm :
                      Reasoning.Theory.uniswapExtCodeSizeWord σ_cat_solm
                          (flipperVatTargetWord σ_cat_solm I) ≠ ⟨0⟩ :=
                    flipperVatCodeSize_ne_zero_accountMapEquiv hAccountsCat hvatZero
                  have hvatCodeSolm :
                      0 <
                        (UInt256.ofNat
                          ((evmCatSolm.lookupAccount
                            (flipperVatAddress evmCatSolm.accountMap
                              evmCatSolm.executionEnv)).option
                            0 (fun acc => acc.code.size))).toNat := by
                    simpa [evmCatSolm, evm0Solm, initState, State.lookupAccount] using
                      flipper_uniswapExtCodeSizeWord_pos_lookup_code_pos
                        (σ := σ_cat_solm) (target := flipperVatTargetWord σ_cat_solm I)
                        (addr := flipperVatAddress σ_cat_solm I)
                        (flipperVatAddress_eq_target σ_cat_solm I) hvatNeSolm
                  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k1482, C1482, rd1482,
                      hcallVatEvmRaw, houtVat⟩ :=
                    flipperYankX_vatPostCall (Acur := A_cat) hvatZero hperm hdepthLt rd1365
                  let evmVatEvm : EVM.State :=
                    { evmCatEvm with
                      accountMap := σ_vat
                      substate := A_vat
                      createdAccounts := cA_vat }
                  have hcallVatEvm :
                      typedCallViaEVM config evmCatEvm
                        (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
                        (yankFluxArgValsOf evmCatEvm (yankId I))
                        (zVat, evmVatEvm, outVat) true := by
                    simpa [evmCatEvm, evmVatEvm] using hcallVatEvmRaw
                  obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hVatStateEquiv⟩ :=
                    flipper_typedCallViaEVM_accountMapEquiv_noSubstate
                      (evm_solm := evmCatSolm) hcallVatEvm hCatStateEquiv'.accountMap
                      (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
                      (by simp [evmCatEvm, evmCatSolm])
                      (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
                      (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
                      (by simpa using hCatStateEquiv'.executionEnv.symm)
                  let evmVatSolm : EVM.State :=
                    { evmCatSolm with
                      accountMap := σ_vat_solm
                      substate := A_vat_solm
                      createdAccounts := cA_vat }
                  have hvatTargetEq :
                      EVM.address (flipperVatAddress σ_cat I) =
                        EVM.address
                          (flipperVatAddress evmCatSolm.accountMap
                            evmCatSolm.executionEnv) := by
                    have haddr : flipperVatAddress σ_cat I =
                        flipperVatAddress σ_cat_solm I :=
                      flipperVatAddress_accountMapEquiv hAccountsCat
                    rw [haddr]
                    simp [evmCatSolm, evm0Solm, initState]
                  have hfluxArgsEq :
                      yankFluxArgValsOf evmCatEvm (yankId I) =
                        yankFluxArgValsOf evmCatSolm (yankId I) := by
                    have hloadIlk :
                        Solm.EVM.storageLoad evmCatEvm
                            evmCatSolm.executionEnv.codeOwner ⟨3⟩ =
                          Solm.EVM.storageLoad evmCatSolm
                            evmCatSolm.executionEnv.codeOwner ⟨3⟩ :=
                      storageLoad_accountMapEquiv hCatStateEquiv'.accountMap
                        evmCatSolm.executionEnv.codeOwner ⟨3⟩
                    have hloadLot :
                        Solm.EVM.storageLoad evmCatEvm
                            evmCatSolm.executionEnv.codeOwner
                            (bidSlotOfWord (yankId I) ⟨1⟩) =
                          Solm.EVM.storageLoad evmCatSolm
                            evmCatSolm.executionEnv.codeOwner
                            (bidSlotOfWord (yankId I) ⟨1⟩) :=
                      storageLoad_accountMapEquiv hCatStateEquiv'.accountMap
                        evmCatSolm.executionEnv.codeOwner (bidSlotOfWord (yankId I) ⟨1⟩)
                    simp [yankFluxArgValsOf, hCatStateEquiv'.executionEnv, hloadIlk,
                      hloadLot]
                  have hcallVatSolm :
                      typedCallViaEVM config evmCatSolm
                        (EVM.address
                          (flipperVatAddress evmCatSolm.accountMap
                            evmCatSolm.executionEnv)) "flux" 0
                        (yankFluxArgValsOf evmCatSolm (yankId I))
                        (zVat, evmVatSolm, outVat) true := by
                    have hcallVatSolmRaw' :
                        typedCallViaEVM config evmCatSolm
                          (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
                          (yankFluxArgValsOf evmCatEvm (yankId I))
                          (zVat, evmVatSolm, outVat) true := by
                      simpa [evmVatSolm, evmVatEvm] using hcallVatSolmRaw
                    rw [hvatTargetEq, hfluxArgsEq] at hcallVatSolmRaw'
                    exact hcallVatSolmRaw'
                  cases zVat
                  · have rd1482False : RD flipperBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
                        (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                          flipperVatTargetWord σ_cat I :: yankId I :: ⟨323⟩ ::
                          flipperSelWord I :: [])
                        (yankVatFluxCallMem σ_evm σ_cat I) (UInt256.ofNat 9) outVat
                        (cA_vat, σ_vat) k1482 C1482 := by
                      simpa using rd1482
                    have hcallVatSolmFalse :
                        typedCallViaEVM config evmCatSolm
                          (EVM.address
                            (flipperVatAddress evmCatSolm.accountMap
                              evmCatSolm.executionEnv)) "flux" 0
                          (yankFluxArgValsOf evmCatSolm (yankId I))
                          (false, evmVatSolm, outVat) true := by
                      simpa using hcallVatSolm
                    have hbody :
                        ExecTransitionBody config contract evm0Solm (yankLocals I)
                          yankTransition.body .reverted := by
                      simpa [evm0Solm] using
                        (flipperYankSourceBodyVatCallFailure
                          (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmCat := evmCatSolm) (evmVat := evmVatSolm)
                          (outCat := outCat) (outVat := outVat)
                          hwv hauthSolm hguySolm hbidLtSolm hcatCode
                          hcallCatSolmTrue hvatCodeSolm hcallVatSolmFalse)
                    exact (flipperYankX_vatCallFailure rd1482False houtVat)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have rd1482True : RD flipperBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
                        (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                          flipperVatTargetWord σ_cat I :: yankId I :: ⟨323⟩ ::
                          flipperSelWord I :: [])
                        (yankVatFluxCallMem σ_evm σ_cat I) (UInt256.ofNat 9) outVat
                        (cA_vat, σ_vat) k1482 C1482 := by
                      simpa using rd1482
                    obtain ⟨_, _, rd1501⟩ :=
                      flipperYankX_vatCallSuccessToMoveStart rd1482True
                    have hcallVatSolmTrue :
                        typedCallViaEVM config evmCatSolm
                          (EVM.address
                            (flipperVatAddress evmCatSolm.accountMap
                              evmCatSolm.executionEnv)) "flux" 0
                          (yankFluxArgValsOf evmCatSolm (yankId I))
                          (true, evmVatSolm, outVat) true := by
                      simpa using hcallVatSolm
                    have hVatStateEquiv' : EVMStateEquiv evmVatEvm evmVatSolm := by
                      simpa [evmVatEvm, evmVatSolm] using hVatStateEquiv
                    have hAccountsVat : accountMapEquiv σ_vat σ_vat_solm := by
                      simpa [evmVatEvm, evmVatSolm] using hVatStateEquiv'.accountMap
                    by_cases hmoveZero :
                        Reasoning.Theory.uniswapExtCodeSizeWord σ_vat
                          (flipperVatTargetWord σ_vat I) = ⟨0⟩
                    · have hmoveZeroSolm :
                          Reasoning.Theory.uniswapExtCodeSizeWord σ_vat_solm
                              (flipperVatTargetWord σ_vat_solm I) = ⟨0⟩ :=
                        flipperVatCodeSize_zero_accountMapEquiv hAccountsVat hmoveZero
                      have hmoveNoCode :
                          (UInt256.ofNat
                            ((evmVatSolm.lookupAccount
                              (flipperVatAddress evmVatSolm.accountMap
                                evmVatSolm.executionEnv)).option
                              0 (fun acc => acc.code.size))).toNat = 0 := by
                        simpa [evmVatSolm, evmCatSolm, evm0Solm, initState,
                          State.lookupAccount] using
                          flipper_uniswapExtCodeSizeWord_zero_lookup_code_zero
                            (σ := σ_vat_solm)
                            (target := flipperVatTargetWord σ_vat_solm I)
                            (addr := flipperVatAddress σ_vat_solm I)
                            (flipperVatAddress_eq_target σ_vat_solm I) hmoveZeroSolm
                      have hbody :
                          ExecTransitionBody config contract evm0Solm (yankLocals I)
                            yankTransition.body .reverted := by
                        simpa [evm0Solm] using
                          (flipperYankSourceBodyMoveNoCode
                            (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmCat := evmCatSolm) (evmVat := evmVatSolm)
                            (outCat := outCat) (outVat := outVat)
                            hwv hauthSolm hguySolm hbidLtSolm hcatCode
                            hcallCatSolmTrue hvatCodeSolm hcallVatSolmTrue hmoveNoCode)
                      exact (flipperYankX_moveNoCode hmoveZero rd1501)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hmoveNeSolm :
                          Reasoning.Theory.uniswapExtCodeSizeWord σ_vat_solm
                              (flipperVatTargetWord σ_vat_solm I) ≠ ⟨0⟩ :=
                        flipperVatCodeSize_ne_zero_accountMapEquiv hAccountsVat hmoveZero
                      have hmoveCodeSolm :
                          0 <
                            (UInt256.ofNat
                              ((evmVatSolm.lookupAccount
                                (flipperVatAddress evmVatSolm.accountMap
                                  evmVatSolm.executionEnv)).option
                                0 (fun acc => acc.code.size))).toNat := by
                        simpa [evmVatSolm, evmCatSolm, evm0Solm, initState,
                          State.lookupAccount] using
                          flipper_uniswapExtCodeSizeWord_pos_lookup_code_pos
                            (σ := σ_vat_solm)
                            (target := flipperVatTargetWord σ_vat_solm I)
                            (addr := flipperVatAddress σ_vat_solm I)
                            (flipperVatAddress_eq_target σ_vat_solm I) hmoveNeSolm
                      obtain ⟨cA_move, σ_move, zMove, outMove, A_move, k1615,
                          C1615, rd1615, hcallMoveEvmRaw, houtMove⟩ :=
                        flipperYankX_movePostCall (Acur := A_vat)
                          hmoveZero hperm hdepthLt rd1501
                      let evmMoveEvm : EVM.State :=
                        { evmVatEvm with
                          accountMap := σ_move
                          substate := A_move
                          createdAccounts := cA_move }
                      have hcallMoveEvm :
                          typedCallViaEVM config evmVatEvm
                            (EVM.address (flipperVatAddress σ_vat I)) "move" 0
                            (yankMoveArgValsOf evmVatEvm (yankId I))
                            (zMove, evmMoveEvm, outMove) true := by
                        simpa [evmVatEvm, evmMoveEvm] using hcallMoveEvmRaw
                      obtain ⟨σ_move_solm, A_move_solm, hcallMoveSolmRaw,
                          hMoveStateEquiv⟩ :=
                        flipper_typedCallViaEVM_accountMapEquiv_noSubstate
                          (evm_solm := evmVatSolm) hcallMoveEvm hVatStateEquiv'.accountMap
                          (by
                            simp [evmVatEvm, evmVatSolm, evmCatEvm, evmCatSolm,
                              evm0Evm, evm0Solm, initState])
                          (by simp [evmVatEvm, evmVatSolm])
                          (by
                            simp [evmVatEvm, evmVatSolm, evmCatEvm, evmCatSolm,
                              evm0Evm, evm0Solm, initState])
                          (by
                            simp [evmVatEvm, evmVatSolm, evmCatEvm, evmCatSolm,
                              evm0Evm, evm0Solm, initState])
                          (by simpa using hVatStateEquiv'.executionEnv.symm)
                      let evmMoveSolm : EVM.State :=
                        { evmVatSolm with
                          accountMap := σ_move_solm
                          substate := A_move_solm
                          createdAccounts := cA_move }
                      have hmoveTargetEq :
                          EVM.address (flipperVatAddress σ_vat I) =
                            EVM.address
                              (flipperVatAddress evmVatSolm.accountMap
                                evmVatSolm.executionEnv) := by
                        have haddr : flipperVatAddress σ_vat I =
                            flipperVatAddress σ_vat_solm I :=
                          flipperVatAddress_accountMapEquiv hAccountsVat
                        rw [haddr]
                        simp [evmVatSolm, evmCatSolm, evm0Solm, initState]
                      have hmoveArgsEq :
                          yankMoveArgValsOf evmVatEvm (yankId I) =
                            yankMoveArgValsOf evmVatSolm (yankId I) := by
                        have hloadPacked :
                            Solm.EVM.storageLoad evmVatEvm
                                evmVatSolm.executionEnv.codeOwner
                                (bidPackedSlotOfWord (yankId I)) =
                              Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner
                                (bidPackedSlotOfWord (yankId I)) :=
                          storageLoad_accountMapEquiv hVatStateEquiv'.accountMap
                            evmVatSolm.executionEnv.codeOwner
                            (bidPackedSlotOfWord (yankId I))
                        have hloadBid :
                            Solm.EVM.storageLoad evmVatEvm
                                evmVatSolm.executionEnv.codeOwner
                                (bidBaseOfWord (yankId I)) =
                              Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner
                                (bidBaseOfWord (yankId I)) :=
                          storageLoad_accountMapEquiv hVatStateEquiv'.accountMap
                            evmVatSolm.executionEnv.codeOwner (bidBaseOfWord (yankId I))
                        simp [yankMoveArgValsOf, hVatStateEquiv'.executionEnv,
                          hloadPacked, hloadBid]
                      have hcallMoveSolm :
                          typedCallViaEVM config evmVatSolm
                            (EVM.address
                              (flipperVatAddress evmVatSolm.accountMap
                                evmVatSolm.executionEnv)) "move" 0
                            (yankMoveArgValsOf evmVatSolm (yankId I))
                            (zMove, evmMoveSolm, outMove) true := by
                        have hcallMoveSolmRaw' :
                            typedCallViaEVM config evmVatSolm
                              (EVM.address (flipperVatAddress σ_vat I)) "move" 0
                              (yankMoveArgValsOf evmVatEvm (yankId I))
                              (zMove, evmMoveSolm, outMove) true := by
                          simpa [evmMoveSolm, evmMoveEvm] using hcallMoveSolmRaw
                        rw [hmoveTargetEq, hmoveArgsEq] at hcallMoveSolmRaw'
                        exact hcallMoveSolmRaw'
                      cases zMove
                      · have rd1615False : RD flipperBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨1615⟩
                            (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
                              flipperVatTargetWord σ_vat I :: yankId I :: ⟨323⟩ ::
                              flipperSelWord I :: [])
                            (yankVatMoveCallMem σ_evm σ_cat σ_vat I) (UInt256.ofNat 9)
                            outMove (cA_move, σ_move) k1615 C1615 := by
                          simpa using rd1615
                        have hcallMoveSolmFalse :
                            typedCallViaEVM config evmVatSolm
                              (EVM.address
                                (flipperVatAddress evmVatSolm.accountMap
                                  evmVatSolm.executionEnv)) "move" 0
                              (yankMoveArgValsOf evmVatSolm (yankId I))
                              (false, evmMoveSolm, outMove) true := by
                          simpa using hcallMoveSolm
                        have hbody :
                            ExecTransitionBody config contract evm0Solm (yankLocals I)
                              yankTransition.body .reverted := by
                          simpa [evm0Solm] using
                            (flipperYankSourceBodyMoveCallFailure
                              (cA := cA) (gh := gh) (bl := bl)
                              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmCat := evmCatSolm) (evmVat := evmVatSolm)
                              (evmMove := evmMoveSolm)
                              (outCat := outCat) (outVat := outVat) (outMove := outMove)
                              hwv hauthSolm hguySolm hbidLtSolm hcatCode
                              hcallCatSolmTrue hvatCodeSolm hcallVatSolmTrue
                              hmoveCodeSolm hcallMoveSolmFalse)
                        exact (flipperYankX_moveCallFailure rd1615False houtMove)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have rd1615True : RD flipperBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨1615⟩
                            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
                              flipperVatTargetWord σ_vat I :: yankId I :: ⟨323⟩ ::
                              flipperSelWord I :: [])
                            (yankVatMoveCallMem σ_evm σ_cat σ_vat I) (UInt256.ofNat 9)
                            outMove (cA_move, σ_move) k1615 C1615 := by
                          simpa using rd1615
                        obtain ⟨k1635, C1635, rd1635⟩ :=
                          flipperYankX_moveCallSuccessToDeleteStart rd1615True
                        have hret :=
                          flipperYankX_deleteReturnFromPostCall
                            (cA := cA) (gh := gh) (bl := bl) (σmem := σ_evm)
                            (σflux := σ_cat) (σcall := σ_vat) (σ := σ_move)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (cA' := cA_move) (k := k1635) (C := C1635)
                            (out := outMove) hperm rd1635
                        have hcallMoveSolmTrue :
                            typedCallViaEVM config evmVatSolm
                              (EVM.address
                                (flipperVatAddress evmVatSolm.accountMap
                                  evmVatSolm.executionEnv)) "move" 0
                              (yankMoveArgValsOf evmVatSolm (yankId I))
                              (true, evmMoveSolm, outMove) true := by
                          simpa using hcallMoveSolm
                        let locals3 : Store :=
                          (((yankLocals I).insert "_clawRet" (collapseReturns [])).insert
                            "_fluxRet" (collapseReturns [])).insert "_moveRet"
                            (collapseReturns [])
                        have hbody :
                            ExecTransitionBody config contract evm0Solm (yankLocals I)
                              yankTransition.body
                              (.returned { contract := contract, locals := locals3 }
                                (bidDeletedEVM evmMoveSolm (yankId I)) none) := by
                          simpa [evm0Solm, locals3] using
                            (flipperYankSourceBodySuccess
                              (cA := cA) (gh := gh) (bl := bl)
                              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmCat := evmCatSolm) (evmVat := evmVatSolm)
                              (evmMove := evmMoveSolm)
                              (outCat := outCat) (outVat := outVat) (outMove := outMove)
                              hwv hauthSolm hguySolm hbidLtSolm hcatCode
                              hcallCatSolmTrue hvatCodeSolm hcallVatSolmTrue
                              hmoveCodeSolm hcallMoveSolmTrue)
                        have hMoveStateEquiv' : EVMStateEquiv evmMoveEvm evmMoveSolm := by
                          simpa [evmMoveEvm, evmMoveSolm] using hMoveStateEquiv
                        have hMoveAccounts : accountMapEquiv σ_move σ_move_solm := by
                          simpa [evmMoveEvm, evmMoveSolm] using hMoveStateEquiv'.accountMap
                        have hcollapsed :
                            accountMapEquiv (yankBidDeleteAccountMap I σ_move (yankId I))
                              (bidDeleteCollapsedAccountMap I.codeOwner σ_move_solm
                                (yankId I)) := by
                          simpa [yankBidDeleteAccountMap] using
                            (bidDeleteCollapsedAccountMap_accountMapEquiv
                              (owner := I.codeOwner) (id := yankId I) hMoveAccounts)
                        have hdeleted :
                            accountMapEquiv
                              (bidDeleteCollapsedAccountMap I.codeOwner σ_move_solm
                                (yankId I))
                              (bidDeletedEVM evmMoveSolm (yankId I)).accountMap := by
                          have h := bidDeleteCollapsedAccountMap_accountMapEquiv_bidDeletedEVM
                            evmMoveSolm (yankId I)
                          simpa [evmMoveSolm, evmVatSolm, evmCatSolm, evm0Solm, initState]
                            using h
                        have haccounts :
                            accountMapEquiv (yankBidDeleteAccountMap I σ_move (yankId I))
                              (bidDeletedEVM evmMoveSolm (yankId I)).accountMap :=
                          accountMapEquiv.trans hcollapsed hdeleted
                        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
                          hbody
                          (by simp [evmMoveSolm, bidDeletedEVM, storageStore_createdAccounts])
                          haccounts
                          (by
                            rw [show yankTransition.returnType = [] by rfl]
                            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))
        · have hgeEvm :
              (bidTabWord (yankId I) σ_evm I).toNat ≤
                (bidBidWord (yankId I) σ_evm I).toNat := by
            omega
          have hgeSolm :
              (bidTabWord (yankId I) σ_solm I).toNat ≤
                (bidBidWord (yankId I) σ_solm I).toNat := by
            simpa [← hbidEq, ← htabEq] using hgeEvm
          have hguySolm : bidGuyWord (yankId I) σ_solm I ≠ ⟨0⟩ := by
            intro hzero
            exact hguyEvm (by simpa [hguyEq] using hzero)
          have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
            rw [← hcallerWord]
            exact hauthEvm
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (yankLocals I) yankTransition.body .reverted := by
            simpa using
              (flipperYankSourceBodyNotDent (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hguySolm hgeSolm)
          exact (flipperYankX_bidNotLt (I := I) hgeEvm hafterGuy)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : flipperSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let locals : Store := yankLocals I
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals yankTransition.body .reverted := by
        have hguard := flipperAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (locals := locals) (by simp [locals, yankLocals]) hauthSolm
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := locals })
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
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, flipperCallerWardsSlot, flipperSlotWord] using hauthEvm
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
    have hreach := flipperReachYankBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperYankX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_yank_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper
