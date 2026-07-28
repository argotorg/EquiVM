import Benchmarks.Dss.Vow.HealFinal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

set_option maxHeartbeats 0 in
theorem vowHealBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 36
  · exact vowHealShort hcode hsize hperm hwv hsz4 hshort hsel hAccounts
  have hsz36 : 36 ≤ I.calldata.size := by omega
  have hdispatch : dispatchMsg contract I.calldata = some healTransition :=
    vowDispatch_heal hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I) := by
    simpa [healLocals] using vowDecode_heal_ok (I := I) hsz36
  have hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨818⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C :=
    vowReachHealBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  by_cases hcodeSizeDai :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩
  · exact vowHealDaiNoCodeBodyCore hcode hwv hsz36 hsize hdispatch hdecode hreach
      hAccounts hcodeSizeDai
  have hcodeSizeDaiNE :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) ≠ ⟨0⟩ :=
    hcodeSizeDai
  have hVatOrig : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTargetOrig : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVatOrig]
  have hVatAddrOrig : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    simp [kissVatAddress, vowAddressReturnWord, hVatOrig]
  have hcodeSizeSolmNE :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeDaiNE
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    rw [hsame, hTargetOrig]
    exact hzero
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := kissDaiTargetWord σ_solm I)
        (addr := kissVatAddress σ_solm I)
        (kissVatAddress_eq_daiTarget_account σ_solm I) hcodeSizeSolmNE
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨cA_dai, σ_dai, zDai, oDai, A_dai, k4719, C4719,
        rd4719, hcallDai, hoszDai⟩ :=
      RD.vowHealDaiPostCall hreach hsz36 hsize hcodeSizeDaiNE hdepthLt
    cases zDai
    · exact vowHealDaiCallFailureBodyCore (cA' := cA_dai) (σ'_evm := σ_dai)
        (A'_evm := A_dai) hcode hwv hdispatch hdecode (by simpa using rd4719)
        (by simpa using hcallDai) hoszDai hvatCodeSolm hAccounts
    · have rd4719True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4719⟩
          (⟨1⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
            kissDaiTargetWord σ_evm I :: healRad I :: ⟨412⟩ :: vowSelWord I :: [])
          (oDai.write 0 (kissDaiCalldataMem I) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat oDai.size)).toNat)
          (UInt256.ofNat 6) oDai (cA_dai, σ_dai) k4719 C4719 := by
        simpa using rd4719
      have hcallDaiTrue :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
            (true,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_dai
                  substate := A_dai
                  createdAccounts := cA_dai },
              oDai) false := by
        simpa using hcallDai
      by_cases ho32 : 32 ≤ oDai.size
      · let vatDai : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (oDai.extract 0 32))
        by_cases hinsuff : vatDai.toNat < (healRad I).toNat
        · exact vowHealDaiSuccessInsufficientSurplusBodyCore
            (cA' := cA_dai) (σ'_evm := σ_dai) (A'_evm := A_dai)
            hcode hwv hdispatch hdecode rd4719True hcallDaiTrue hoszDai ho32
            hvatCodeSolm hAccounts (by simpa [vatDai] using hinsuff)
        have hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat := by omega
        have hminDai : (min (⟨32⟩ : UInt256) (UInt256.ofNat oDai.size)).toNat = 32 :=
          kissDaiMin32_toNat_of_ge ho32 hoszDai
        have rd4719Write := rd4719True
        rw [hminDai] at rd4719Write
        obtain ⟨_, _, rd4737⟩ :=
          RD.vowHealDaiCallSuccessToDecode rd4719Write (by simp)
        have hmemDai : (oDai.write 0 (kissDaiCalldataMem I) 128 32).size = 164 :=
          kissDaiWrite_size I oDai 32 (by omega) ho32
        have hread64Dai :
            (oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          kissDaiWrite_read64 I oDai 32 (by omega) ho32
        have hmload64Dai :
            (if (⟨64⟩ : UInt256).toNat ≥
                  (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemDai]; decide) (by decide) hread64Dai
        have hmload128Dai :
            (if (⟨128⟩ : UInt256).toNat ≥
                  (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
                  (⟨128⟩ : UInt256).toNat 32))) =
              vatDai := by
          have hnot :
              ¬ ((⟨128⟩ : UInt256).toNat ≥
                    (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                  ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
            rw [hmemDai]
            native_decide
          rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            kissDaiWrite_read128_32 I oDai ho32]
        obtain ⟨_, _, rd4760⟩ :=
          RD.vowHealDaiReturnDecodeOk (retWord := vatDai) rd4737 ho32 hoszDai
            hmload64Dai hmload128Dai
        obtain ⟨_, _, rd4838⟩ := RD.vowHealDaiEnough rd4760 hvatDaiEnough
        have hVatDaiEvm : vowSlotWord ⟨1⟩ σ_dai I = vowSlotWord ⟨1⟩ σ_evm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_evm)
            (slot := ⟨1⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_evm)
            hcallDaiTrue
          simpa [initState, vowSlotWord, solcSlotWord] using h
        have hTargetDaiEvm : kissDaiTargetWord σ_dai I = kissDaiTargetWord σ_evm I := by
          simp [kissDaiTargetWord, hVatDaiEvm]
        have hVatAddrSin : kissVatAddress σ_dai I = kissVatAddress σ_solm I := by
          apply Fin.ext
          simp [kissVatAddress, vowAddressReturnWord, hVatDaiEvm, hVatOrig]
        obtain ⟨σ_dai_solm, A_dai_solm, hcallDaiSolmRaw, hStateDaiRaw⟩ :=
          typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDaiTrue)
            (by simp [initState]) hAccounts
        let evmDaiEvm :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai
              substate := A_dai
              createdAccounts := cA_dai }
        let evmDaiSolm :=
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai_solm
              substate := A_dai_solm
              createdAccounts := cA_dai }
        have hcallDaiSolm :
            typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
              (true, evmDaiSolm, oDai) false := by
          simpa [evmDaiSolm, hVatAddrOrig] using hcallDaiSolmRaw
        have hStateDai : EVMStateEquiv evmDaiEvm evmDaiSolm := by
          simpa [evmDaiEvm, evmDaiSolm] using hStateDaiRaw
        have hAccountsDai : accountMapEquiv σ_dai evmDaiSolm.accountMap := by
          simpa [evmDaiEvm, evmDaiSolm] using hStateDai.accountMap
        have hdecDai :
            config.externalABI.decode? "dai" oDai =
              some [.int (Int.ofNat vatDai.toNat)] := by
          simpa [vatDai] using kissDaiDecode_ok (o := oDai) ho32
        have hvatLoadDai :
            Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨1⟩ =
              vowSlotWord ⟨1⟩ σ_solm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_solm)
            (slot := ⟨1⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_solm)
            hcallDaiSolm
          simpa [evmDaiSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, vowSlotWord, solcSlotWord] using h
        have hVatDaiSolmOrig :
            vowSlotWord ⟨1⟩ evmDaiSolm.accountMap I = vowSlotWord ⟨1⟩ σ_solm I := by
          simpa [evmDaiSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, vowSlotWord, solcSlotWord] using hvatLoadDai
        have hTargetDaiEq :
            kissDaiTargetWord σ_dai I = kissDaiTargetWord evmDaiSolm.accountMap I := by
          have hslot := accountMapEquiv_storage_findD hAccountsDai I.codeOwner ⟨1⟩ ⟨0⟩
          simp [kissDaiTargetWord, vowSlotWord, hslot]
        have hTargetDaiSolmOrig :
            kissDaiTargetWord evmDaiSolm.accountMap I = kissDaiTargetWord σ_solm I := by
          simp [kissDaiTargetWord, hVatDaiSolmOrig]
        by_cases hcodeSizeSin :
            Reasoning.Theory.extCodeSizeWord σ_dai (kissDaiTargetWord σ_dai I) = ⟨0⟩
        · have hcodeSizeSinSolm :
              Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
                (kissDaiTargetWord evmDaiSolm.accountMap I) = ⟨0⟩ := by
            have hsame :=
              Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsDai
                (kissDaiTargetWord σ_dai I)
            have hzeroAtEvmTarget :
                Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
                  (kissDaiTargetWord σ_dai I) = ⟨0⟩ := by
              rw [← hsame]
              exact hcodeSizeSin
            simpa [hTargetDaiEq] using hzeroAtEvmTarget
          have haddrSin :
              kissVatAddress σ_solm I =
                AccountAddress.ofUInt256 (kissDaiTargetWord evmDaiSolm.accountMap I) := by
            rw [hTargetDaiSolmOrig]
            exact kissVatAddress_eq_daiTarget_account σ_solm I
          have hvatNoCodeSin :
              (UInt256.ofNat
                ((evmDaiSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                  (fun acc => acc.code.size))).toNat = 0 := by
            simpa [evmDaiSolm, State.lookupAccount] using
              extCodeSizeWord_zero_lookup_code_zero
                (σ := evmDaiSolm.accountMap)
                (target := kissDaiTargetWord evmDaiSolm.accountMap I)
                (addr := kissVatAddress σ_solm I) haddrSin hcodeSizeSinSolm
          exact vowHealSinNoCodeBodyCore
            (cA' := cA_dai) (σ'_evm := σ_dai) (evmDai := evmDaiSolm)
            hcode hwv hdispatch hdecode rd4838 hmemDai hread64Dai hcodeSizeSin
            hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai hvatNoCodeSin
        have hcodeSizeSinNE :
            Reasoning.Theory.extCodeSizeWord σ_dai (kissDaiTargetWord σ_dai I) ≠ ⟨0⟩ :=
          hcodeSizeSin
        have hcodeSizeSinSolmNE :
            Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
              (kissDaiTargetWord evmDaiSolm.accountMap I) ≠ ⟨0⟩ := by
          intro hzero
          apply hcodeSizeSinNE
          have hsame :=
            Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsDai
              (kissDaiTargetWord σ_dai I)
          have hzeroAtEvmTarget :
              Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
                (kissDaiTargetWord σ_dai I) = ⟨0⟩ := by
            simpa [hTargetDaiEq] using hzero
          rw [hsame]
          exact hzeroAtEvmTarget
        have haddrSin :
            kissVatAddress σ_solm I =
              AccountAddress.ofUInt256 (kissDaiTargetWord evmDaiSolm.accountMap I) := by
          rw [hTargetDaiSolmOrig]
          exact kissVatAddress_eq_daiTarget_account σ_solm I
        have hvatCodeSinSolm :
            0 < (UInt256.ofNat
              ((evmDaiSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                (fun acc => acc.code.size))).toNat := by
          simpa [evmDaiSolm, State.lookupAccount] using
            extCodeSizeWord_ne_zero_lookup_code_pos
              (σ := evmDaiSolm.accountMap)
              (target := kissDaiTargetWord evmDaiSolm.accountMap I)
              (addr := kissVatAddress σ_solm I) haddrSin hcodeSizeSinSolmNE
        obtain ⟨cA_sin, σ_sin, zSin, outSin, A_sin, k1277, C1277,
            rd1277, hcallSinRaw, houtSinSize⟩ :=
          RD.vowHealSinPostCall rd4838 hmemDai hread64Dai hcodeSizeSinNE hdepthLt
        let evmSinEvmIn :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai
              createdAccounts := cA_dai }
        let evmSinEvmOut :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_sin
              substate := A_sin
              createdAccounts := cA_sin }
        have hcallSinEvm :
            typedCallViaEVM config evmSinEvmIn
              (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
              (zSin, evmSinEvmOut, outSin) false := by
          simpa [evmSinEvmIn, evmSinEvmOut, hVatAddrSin] using hcallSinRaw
        let evmSinSolmBase := { evmDaiSolm with substate := evmSinEvmIn.substate }
        have hcallSinCreated : evmSinSolmBase.createdAccounts = evmSinEvmIn.createdAccounts := by
          simp [evmSinSolmBase, evmSinEvmIn, evmDaiSolm]
        have hcallSinEnv : evmSinSolmBase.executionEnv = evmSinEvmIn.executionEnv := by
          simp [evmSinSolmBase, evmSinEvmIn, evmDaiSolm, initState]
        obtain ⟨σ_sin_solm, A_sin_solm0, hcallSinSolmBase, hAccountsSin⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evmSinSolmBase)
            hcallSinEvm hAccountsDai
            (by simp [evmSinEvmIn, evmSinSolmBase, evmDaiSolm, initState])
            hcallSinCreated
            (by simp [evmSinEvmIn, evmSinSolmBase, evmDaiSolm, initState])
            (by simp [evmSinEvmIn, evmSinSolmBase, evmDaiSolm, initState])
            (by simp [evmSinSolmBase])
            hcallSinEnv
        have hdepthNeI : I.depth ≠ 1024 := by
          intro hdepthEq
          rw [hdepthEq] at hdepthLt
          norm_num at hdepthLt
        have hdepthNeSinBase : evmSinSolmBase.executionEnv.depth ≠ 1024 := by
          simpa [evmSinSolmBase, evmDaiSolm, initState] using hdepthNeI
        obtain ⟨A_sin_solm, hcallSinSolmRaw⟩ :=
          typedCallViaEVM_zero_setSubstate hcallSinSolmBase hdepthNeSinBase evmDaiSolm.substate
        let evmSinSolm :=
          { evmDaiSolm with
              accountMap := σ_sin_solm
              substate := A_sin_solm
              createdAccounts := cA_sin }
        have hcallSinSolm :
            typedCallViaEVM config evmDaiSolm
              (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
              (zSin, evmSinSolm, outSin) false := by
          simpa [evmSinSolm, evmSinSolmBase] using hcallSinSolmRaw
        cases zSin
        · exact vowHealSinCallFailureBodyCore
            (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
            hcode hwv hdispatch hdecode (by simpa using rd1277) houtSinSize
            hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai hvatCodeSinSolm
            (by simpa using hcallSinSolm)
        have rd1277True : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
            (⟨1⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord σ_dai I ::
              ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: vowSelWord I :: [])
            (outSin.write 0 (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
              128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
            (UInt256.ofNat 6) outSin (cA_sin, σ_sin) k1277 C1277 := by
          simpa using rd1277
        have hcallSinTrue :
            typedCallViaEVM config evmDaiSolm
              (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
              (true, evmSinSolm, outSin) false := by
          simpa using hcallSinSolm
        by_cases hoSin32 : 32 ≤ outSin.size
        · let vatSin : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
          have hminSin :
              (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
            kissDaiMin32_toNat_of_ge hoSin32 houtSinSize
          have rd1277Write := rd1277True
          rw [hminSin] at rd1277Write
          obtain ⟨_, _, rd1295⟩ := RD.vowHealSinCallSuccessToDecode rd1277Write (by simp)
          have hmemSin :
              (outSin.write 0
                (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                128 32).size = 164 :=
            healSinWrite_size I (oDai.write 0 (kissDaiCalldataMem I) 128 32) outSin 32
              hmemDai (by omega) hoSin32
          have hread64Sin :
              (outSin.write 0
                (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                128 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
            healSinWrite_read64 I (oDai.write 0 (kissDaiCalldataMem I) 128 32)
              outSin 32 hmemDai hread64Dai (by omega) hoSin32
          have hmload64Sin :
              (if (⟨64⟩ : UInt256).toNat ≥
                    (outSin.write 0
                      (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                      128 32).size
                  ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
               else UInt256.ofNat
                 (fromByteArrayBigEndian
                  ((outSin.write 0
                    (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                    128 32).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
                ⟨128⟩ :=
            mloadFreePtrValue (by rw [hmemSin]; decide) (by decide) hread64Sin
          have hmload128Sin :
              (if (⟨128⟩ : UInt256).toNat ≥
                    (outSin.write 0
                      (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                      128 32).size
                  ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
               else UInt256.ofNat
                 (fromByteArrayBigEndian
                  ((outSin.write 0
                    (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                    128 32).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
                vatSin := by
            have hnot :
                ¬ ((⟨128⟩ : UInt256).toNat ≥
                      (outSin.write 0
                        (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                        128 32).size
                    ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
              rw [hmemSin]
              native_decide
            rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
              healSinWrite_read128_32 I (oDai.write 0 (kissDaiCalldataMem I) 128 32)
                outSin hmemDai hoSin32]
          obtain ⟨_, _, rd1318⟩ :=
            RD.vowHealSinReturnDecodeOk (retWord := vatSin) rd1295 hoSin32 houtSinSize
              hmload64Sin hmload128Sin
          have hdecSin :
              config.externalABI.decode? "sin" outSin =
                some [.int (Int.ofNat vatSin.toNat)] := by
            simpa [vatSin] using vatSinDecode_ok (o := outSin) hoSin32
          have hSinLoad :
              Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨5⟩ =
                vowSlotWord ⟨5⟩ σ_sin I := by
            have hslot := accountMapEquiv_storage_findD hAccountsSin I.codeOwner ⟨5⟩ ⟨0⟩
            simpa [evmSinEvmOut, evmSinSolm, initState, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage, vowSlotWord, solcSlotWord] using
              hslot.symm
          have hAshLoad :
              Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨6⟩ =
                vowSlotWord ⟨6⟩ σ_sin I := by
            have hslot := accountMapEquiv_storage_findD hAccountsSin I.codeOwner ⟨6⟩ ⟨0⟩
            simpa [evmSinEvmOut, evmSinSolm, initState, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage, vowSlotWord, solcSlotWord] using
              hslot.symm
          have hvatLoadSin :
              Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
                vowSlotWord ⟨1⟩ σ_solm I := by
            have hstatic := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
              (cfg := config) (σ := evmDaiSolm.accountMap)
              (slot := ⟨1⟩) (default := ⟨0⟩)
              (hAccounts := accountMapEquiv_refl evmDaiSolm.accountMap)
              hcallSinTrue
            have hpre : ((evmDaiSolm.accountMap.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
                vowSlotWord ⟨1⟩ σ_solm I := by
              simpa [evmDaiSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, vowSlotWord, solcSlotWord] using hvatLoadDai
            simpa [evmSinSolm, Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, vowSlotWord, solcSlotWord] using hstatic.trans hpre
          by_cases hfreeUnder :
              vatSin.toNat < (vowSlotWord ⟨5⟩ σ_sin I).toNat
          · exact vowHealFreeSinUnderflowBodyCore
              (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
              hcode hwv hdispatch hdecode rd1318 hfreeUnder
              hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
              hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad
          have hfreeOk : (vowSlotWord ⟨5⟩ σ_sin I).toNat ≤ vatSin.toNat := by omega
          let freeSin : UInt256 := UInt256.sub vatSin (vowSlotWord ⟨5⟩ σ_sin I)
          have hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ σ_sin I) := rfl
          obtain ⟨_, _, rd1325⟩ := RD.vowHealFreeSinSubSuccess rd1318 hfreeOk
          by_cases hdebtUnder :
              freeSin.toNat < (vowSlotWord ⟨6⟩ σ_sin I).toNat
          · exact vowHealDebtUnderflowBodyCore
              (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
              hcode hwv hdispatch hdecode rd1325 hdebtUnder
              hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
              hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad hfree hfreeOk hAshLoad
          have hdebtOk : (vowSlotWord ⟨6⟩ σ_sin I).toNat ≤ freeSin.toNat := by omega
          let healDebt : UInt256 := UInt256.sub freeSin (vowSlotWord ⟨6⟩ σ_sin I)
          have hdebt : healDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ σ_sin I) := rfl
          obtain ⟨_, _, rd4921⟩ := RD.vowHealDebtSubSuccess rd1325 hdebtOk
          by_cases hinsuffDebt : healDebt.toNat < (healRad I).toNat
          · exact vowHealInsufficientDebtBodyCore
              (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
              hcode hwv hdispatch hdecode rd4921 hinsuffDebt hmemSin hread64Sin
              hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
              hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad hfree hfreeOk hAshLoad
              hdebt hdebtOk
          have hdebtEnough : (healRad I).toNat ≤ healDebt.toNat := by omega
          obtain ⟨_, _, rd4997⟩ := RD.vowHealDebtEnough rd4921 hdebtEnough
          have hSlotSinOrig :
              vowSlotWord ⟨1⟩ σ_sin I = vowSlotWord ⟨1⟩ σ_solm I := by
            have hslot := accountMapEquiv_storage_findD hAccountsSin I.codeOwner ⟨1⟩ ⟨0⟩
            have hpost :
                vowSlotWord ⟨1⟩ evmSinSolm.accountMap I =
                  vowSlotWord ⟨1⟩ σ_solm I := by
              simpa [evmSinSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, vowSlotWord, solcSlotWord] using hvatLoadSin
            exact hslot.trans hpost
          have hTargetSinEq :
              kissDaiTargetWord σ_sin I = kissDaiTargetWord evmSinSolm.accountMap I := by
            have hslot := accountMapEquiv_storage_findD hAccountsSin I.codeOwner ⟨1⟩ ⟨0⟩
            have hslotWord :
                vowSlotWord ⟨1⟩ σ_sin I = vowSlotWord ⟨1⟩ evmSinSolm.accountMap I := by
              simpa [evmSinEvmOut, evmSinSolm, initState, vowSlotWord, solcSlotWord] using
                hslot
            simp [kissDaiTargetWord, hslotWord]
          have hTargetSinSolmOrig :
              kissDaiTargetWord evmSinSolm.accountMap I = kissDaiTargetWord σ_solm I := by
            have hpost :
                vowSlotWord ⟨1⟩ evmSinSolm.accountMap I =
                  vowSlotWord ⟨1⟩ σ_solm I := by
              simpa [evmSinSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, vowSlotWord, solcSlotWord] using hvatLoadSin
            simp [kissDaiTargetWord, hpost]
          have hVatAddrHeal : kissVatAddress σ_sin I = kissVatAddress σ_solm I := by
            apply Fin.ext
            simp [kissVatAddress, vowAddressReturnWord, hSlotSinOrig]
          by_cases hcodeSizeHeal :
              Reasoning.Theory.extCodeSizeWord σ_sin
                (kissDaiTargetWord σ_sin I) = ⟨0⟩
          · have hcodeSizeHealSolm :
                Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                  (kissDaiTargetWord evmSinSolm.accountMap I) = ⟨0⟩ := by
              have hsame :=
                Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsSin
                  (kissDaiTargetWord σ_sin I)
              have hzeroAtEvmTarget :
                  Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                    (kissDaiTargetWord σ_sin I) = ⟨0⟩ := by
                rw [← hsame]
                exact hcodeSizeHeal
              simpa [hTargetSinEq] using hzeroAtEvmTarget
            have haddrHeal :
                kissVatAddress σ_solm I =
                  AccountAddress.ofUInt256 (kissDaiTargetWord evmSinSolm.accountMap I) := by
              rw [hTargetSinSolmOrig]
              exact kissVatAddress_eq_daiTarget_account σ_solm I
            have hvatNoCodeHeal :
                (UInt256.ofNat
                  ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                    (fun acc => acc.code.size))).toNat = 0 := by
              simpa [evmSinSolm, State.lookupAccount] using
                extCodeSizeWord_zero_lookup_code_zero
                  (σ := evmSinSolm.accountMap)
                  (target := kissDaiTargetWord evmSinSolm.accountMap I)
                  (addr := kissVatAddress σ_solm I) haddrHeal hcodeSizeHealSolm
            exact vowHealHealNoCodeBodyCore
              (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
              hcode hwv hdispatch hdecode rd4997 hmemSin hread64Sin hcodeSizeHeal
              hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
              hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad hfree hfreeOk hAshLoad
              hdebt hdebtOk hdebtEnough hvatLoadSin hvatNoCodeHeal
          have hcodeSizeHealNE :
              Reasoning.Theory.extCodeSizeWord σ_sin
                (kissDaiTargetWord σ_sin I) ≠ ⟨0⟩ :=
            hcodeSizeHeal
          have hcodeSizeHealSolmNE :
              Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                (kissDaiTargetWord evmSinSolm.accountMap I) ≠ ⟨0⟩ := by
            intro hzero
            apply hcodeSizeHealNE
            have hsame :=
              Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsSin
                (kissDaiTargetWord σ_sin I)
            have hzeroAtEvmTarget :
                Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                  (kissDaiTargetWord σ_sin I) = ⟨0⟩ := by
              simpa [hTargetSinEq] using hzero
            rw [hsame]
            exact hzeroAtEvmTarget
          have haddrHeal :
              kissVatAddress σ_solm I =
                AccountAddress.ofUInt256 (kissDaiTargetWord evmSinSolm.accountMap I) := by
            rw [hTargetSinSolmOrig]
            exact kissVatAddress_eq_daiTarget_account σ_solm I
          have hvatCodeHealSolm :
              0 < (UInt256.ofNat
                ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                  (fun acc => acc.code.size))).toNat := by
            simpa [evmSinSolm, State.lookupAccount] using
              extCodeSizeWord_ne_zero_lookup_code_pos
                (σ := evmSinSolm.accountMap)
                (target := kissDaiTargetWord evmSinSolm.accountMap I)
                (addr := kissVatAddress σ_solm I) haddrHeal hcodeSizeHealSolmNE
          obtain ⟨cA_heal, σ_heal, zHeal, outHeal, A_heal, k1919, C1919,
              rd1919, hcallHealRaw, houtHealSize⟩ :=
            RD.vowHealHealPostCall rd4997 hmemSin hread64Sin hcodeSizeHealNE hdepthLt hperm
          let evmHealEvmIn :=
            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σ_sin
                createdAccounts := cA_sin }
          let evmHealEvmOut :=
            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σ_heal
                substate := A_heal
                createdAccounts := cA_heal }
          have hcallHealEvm :
              typedCallViaEVM config evmHealEvmIn
                (EVM.address (kissVatAddress σ_solm I)) "heal" 0
                [.int (Int.ofNat (healRad I).toNat)]
                (zHeal, evmHealEvmOut, outHeal) true := by
            simpa [evmHealEvmIn, evmHealEvmOut, hVatAddrHeal] using hcallHealRaw
          let evmHealSolmBase := { evmSinSolm with substate := evmHealEvmIn.substate }
          have hcallHealCreated :
              evmHealSolmBase.createdAccounts = evmHealEvmIn.createdAccounts := by
            simp [evmHealSolmBase, evmHealEvmIn, evmSinSolm]
          have hcallHealEnv : evmHealSolmBase.executionEnv = evmHealEvmIn.executionEnv := by
            simp [evmHealSolmBase, evmHealEvmIn, evmSinSolm, evmDaiSolm, initState]
          obtain ⟨σ_heal_solm, A_heal_solm0, hcallHealSolmBase, hAccountsHeal⟩ :=
            typedCallViaEVM_accountMapEquiv (evm_solm := evmHealSolmBase)
              hcallHealEvm hAccountsSin
              (by simp [evmHealEvmIn, evmHealSolmBase, evmSinSolm, evmDaiSolm, initState])
              hcallHealCreated
              (by simp [evmHealEvmIn, evmHealSolmBase, evmSinSolm, evmDaiSolm, initState])
              (by simp [evmHealEvmIn, evmHealSolmBase, evmSinSolm, evmDaiSolm, initState])
              (by simp [evmHealSolmBase])
              hcallHealEnv
          have hdepthNeHealBase : evmHealSolmBase.executionEnv.depth ≠ 1024 := by
            simpa [evmHealSolmBase, evmSinSolm, evmDaiSolm, initState] using hdepthNeI
          obtain ⟨A_heal_solm, hcallHealSolmRaw⟩ :=
            typedCallViaEVM_zero_setSubstate hcallHealSolmBase hdepthNeHealBase
              evmSinSolm.substate
          let evmHealSolm :=
            { evmSinSolm with
                accountMap := σ_heal_solm
                substate := A_heal_solm
                createdAccounts := cA_heal }
          have hcallHealSolm :
              typedCallViaEVM config evmSinSolm
                (EVM.address (kissVatAddress σ_solm I)) "heal" 0
                [.int (Int.ofNat (healRad I).toNat)]
                (zHeal, evmHealSolm, outHeal) true := by
            simpa [evmHealSolm, evmHealSolmBase] using hcallHealSolmRaw
          cases zHeal
          · exact vowHealHealCallFailureBodyCore
              (preAcc := (cA_sin, σ_sin)) (acc := (cA_heal, σ_heal))
              (evmDai := evmDaiSolm)
              (evmSin := evmSinSolm) (evmHeal := evmHealSolm)
              hcode hwv hdispatch hdecode (by simpa using rd1919) houtHealSize
              hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
              hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad hfree hfreeOk hAshLoad
              hdebt hdebtOk hdebtEnough hvatLoadSin hvatCodeHealSolm
              (by simpa using hcallHealSolm)
          have hdecHeal : config.externalABI.decode? "heal" outHeal = some [] := by
            simp [config, vowExternalABI, decodeVoid?]
          have hcreated : (cA_heal, σ_heal).1 = evmHealSolm.createdAccounts := by
            rfl
          have hAccountsFinal : accountMapEquiv (cA_heal, σ_heal).2 evmHealSolm.accountMap := by
            simpa [evmHealEvmOut, evmHealSolm] using hAccountsHeal
          exact vowHealHealSuccessBodyCore
            (preAcc := (cA_sin, σ_sin)) (acc := (cA_heal, σ_heal))
            (evmDai := evmDaiSolm)
            (evmSin := evmSinSolm) (evmHeal := evmHealSolm)
            hcode hwv hdispatch hdecode (by simpa using rd1919)
            hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough hvatLoadDai
            hvatCodeSinSolm hcallSinTrue hdecSin hSinLoad hfree hfreeOk hAshLoad
            hdebt hdebtOk hdebtEnough hvatLoadSin hvatCodeHealSolm
            (by simpa using hcallHealSolm) hdecHeal hcreated hAccountsFinal
        · have hshortSin : outSin.size < 32 := Nat.lt_of_not_ge hoSin32
          have hminSin :
              (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = outSin.size :=
            kissDaiMin32_toNat_of_lt hshortSin
          have rd1277Short := rd1277True
          rw [hminSin] at rd1277Short
          have hmemSinShort :
              (outSin.write 0
                (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                128 outSin.size).size = 164 :=
            healSinWrite_size I (oDai.write 0 (kissDaiCalldataMem I) 128 32) outSin
              outSin.size hmemDai (by omega) (by omega)
          have hread64SinShort :
              (outSin.write 0
                (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                128 outSin.size).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
            healSinWrite_read64 I (oDai.write 0 (kissDaiCalldataMem I) 128 32)
              outSin outSin.size hmemDai hread64Dai (by omega) (by omega)
          have hmload64SinShort :
              (if (⟨64⟩ : UInt256).toNat ≥
                    (outSin.write 0
                      (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                      128 outSin.size).size
                  ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
               else UInt256.ofNat
                 (fromByteArrayBigEndian
                  ((outSin.write 0
                    (healSinCalldataMem I (oDai.write 0 (kissDaiCalldataMem I) 128 32))
                    128 outSin.size).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
                ⟨128⟩ :=
            mloadFreePtrValue (by rw [hmemSinShort]; decide) (by decide) hread64SinShort
          exact vowHealSinDecodeShortBodyCore
            (acc := (cA_sin, σ_sin)) (evmDai := evmDaiSolm) (evmSin := evmSinSolm)
            hcode hwv hdispatch hdecode rd1277Short hshortSin houtSinSize
            hmload64SinShort hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough
            hvatLoadDai hvatCodeSinSolm hcallSinTrue
      · have hshortDai : oDai.size < 32 := Nat.lt_of_not_ge ho32
        have hminDai : (min (⟨32⟩ : UInt256) (UInt256.ofNat oDai.size)).toNat = oDai.size :=
          kissDaiMin32_toNat_of_lt hshortDai
        have rd4719Short := rd4719True
        rw [hminDai] at rd4719Short
        obtain ⟨_, _, rd4737⟩ :=
          RD.vowHealDaiCallSuccessToDecode rd4719Short (by simp)
        have hmemDaiShort :
            (oDai.write 0 (kissDaiCalldataMem I) 128 oDai.size).size = 164 :=
          kissDaiWrite_size I oDai oDai.size (by omega) (by omega)
        have hread64DaiShort :
            (oDai.write 0 (kissDaiCalldataMem I) 128 oDai.size).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          kissDaiWrite_read64 I oDai oDai.size (by omega) (by omega)
        have hmload64DaiShort :
            (if (⟨64⟩ : UInt256).toNat ≥
                  (oDai.write 0 (kissDaiCalldataMem I) 128 oDai.size).size
                ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((oDai.write 0 (kissDaiCalldataMem I) 128 oDai.size).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemDaiShort]; decide) (by decide) hread64DaiShort
        exact vowHealDaiDecodeShortBodyCore (cA' := cA_dai) (σ'_evm := σ_dai)
          (A'_evm := A_dai) hcode hwv hdispatch hdecode rd4737 hcallDaiTrue
          hshortDai hoszDai hmload64DaiShort hvatCodeSolm hAccounts
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    obtain ⟨k4719, C4719, rd4719⟩ :=
      RD.vowHealDaiCallDepthLimit hreach hsz36 hsize hcodeSizeDaiNE hdepthEq
    let evm0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let A_dai := (evm0.addAccessedAccount (EVM.address (kissVatAddress σ_evm I))).substate
    have hcallDaiDepth :
        typedCallViaEVM config evm0
          (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
          (false, { evm0 with accountMap := σ_evm, substate := A_dai, createdAccounts := cA },
            ByteArray.empty) false := by
      simpa [evm0, A_dai, initState] using
        (callNotMade_depthLimit (cfg := config) (evm := evm0)
          (tgt := EVM.address (kissVatAddress σ_evm I)) (name := "dai")
          (args := [.address I.codeOwner]) (callPerm := false)
          (kissDaiEncode_eq I) (by simpa [evm0, initState] using hdepthEq))
    exact vowHealDaiCallFailureBodyCore (cA' := cA) (σ'_evm := σ_evm)
      (A'_evm := A_dai) hcode hwv hdispatch hdecode rd4719 hcallDaiDepth
      (by native_decide) hvatCodeSolm hAccounts

end Benchmarks.Dss.Vow
