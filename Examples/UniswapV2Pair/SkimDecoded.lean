import Examples.UniswapV2Pair.SkimCoupling

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapSkimBodyDecoded
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdecode : decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hlocked :
    (σ_evm.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
    have hRuntime :
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      have hdecoded :=
        uniswapSkimX_decoded_masked
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hsz36 hsize
          (uniswapReachSkimBody
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
      exact uniswapSkimX_locked (g := Sat256.ofUInt256 g)
        (toWord := skimToMaskedWord I) hlocked hdecoded
    exact uniswapSkimBodyRevert_locked
      (fun w : UInt256 => UInt256.land solcAddrMask w) hcode hwv hlocked hdispatch
      hdecode hRuntime hAccounts
  · have hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩ := by
      exact not_not.mp hlocked
    by_cases htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩
            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩
    · have hRuntime :
          RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
        have hsz4 : 4 ≤ I.calldata.size :=
          calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
        have hdecoded :=
          uniswapSkimX_decoded_masked
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hsz36 hsize
            (uniswapReachSkimBody
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
              (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
        have hLock :=
          uniswapSkimRuntimeLockEntered
            (g := g) (toWord := skimToMaskedWord I) hperm hunlocked hdecoded
        obtain ⟨_, _, rd5257⟩ :=
          uniswapSkimRuntimeFirstBalanceOfExtcodesize
            (g := g) (toWord := skimToMaskedWord I) hLock
        exact uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts
          rd5257 htoken0NoCode
          (by simp only [List.length_cons, List.length_nil]; omega)
      exact uniswapSkimBodyRevert_firstNoCode
        (fun w : UInt256 => UInt256.land solcAddrMask w) hcode hwv
        hunlocked htoken0NoCode hdispatch
        hdecode hRuntime hAccounts
    · by_cases hdepth : I.depth.val < 1024
      · have hsz4 : 4 ≤ I.calldata.size :=
          calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
        have hdecoded :=
          uniswapSkimX_decoded_masked
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            hsz36 hsize
            (uniswapReachSkimBody
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              hcode hwv hsz4 hsize hsel)
        have hLock :=
          uniswapSkimRuntimeLockEntered
            (g := g) (toWord := skimToMaskedWord I) hperm hunlocked hdecoded
        obtain ⟨_, _, rd5257⟩ :=
          uniswapSkimRuntimeFirstBalanceOfExtcodesize
            (g := g) (toWord := skimToMaskedWord I) hLock
        obtain ⟨_, _, _, rd5272⟩ :=
          uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
            (g := g) (toWord := skimToMaskedWord I) rd5257 htoken0NoCode
        obtain ⟨cA_made, σ_made, z_made, o_made, A_in_made, callGas_made,
            _kMade, _CMade, hΘMade, rd5273, hoSizeMade⟩ :=
          uniswapSkimRuntimeFirstBalanceOfStaticcallMade
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (toWord := skimToMaskedWord I)
            rd5272 hdepth
        obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, hrevLong,
            hoSize⟩ :=
            uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard
              (cA' := cA_made) (σ' := σ_made) (z := z_made) (o := o_made)
              (A_in := A_in_made) (callGas := callGas_made)
              hΘMade rd5273 hoSizeMade
              (by simp only [List.length_cons, List.length_nil]; omega)
        obtain ⟨evm0S, hcallAll, hPostAccounts0, hcreated0, hσ0, hgenesis0,
            hblocks0, henv0⟩ :=
          uniswapSkimFirstBalanceTypedCall_source
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (cA' := cA') (σ' := σ') (z := z) (o := o)
            (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hunlockedSolm :
            Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
          have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
          simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage] using (hword ▸ hunlocked)
        have hguard0 : skimToken0GuardTrue evmS I :=
          skimToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
        by_cases hz : z = false
        · exact (hrev hz).reEquivExecutionRevert hcode hdispatch
            hdecode (by
              have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                  (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                  "balanceOf" 0
                  [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                  (false, evm0S, o) false := by
                simpa [evmS, hz] using hcallAll
              exact uniswapSkimBodyReverts_firstCallFailure evmS evm0S I
                (by simp only [evmS, initState]; exact hwv)
                hunlockedSolm hguard0 hcall0)
        · by_cases hshort : o.size < 32
          · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
            have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                "balanceOf" 0 [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                (true, evm0S, o) false := by
              simpa [evmS, hzTrue] using hcallAll
            have hdec0 : config.externalABI.decode? "balanceOf" o = none := by
              change uniswapExternalABI.decode? "balanceOf" o = none
              simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o)
                  hshort)
            have hbody :
                ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                  .reverted := by
              exact uniswapSkimBodyReverts_firstCallDecode evmS evm0S I
                (by simp only [evmS, initState]; exact hwv)
                hunlockedSolm hguard0 hcall0 hdec0
            exact (hrevShort hzTrue hshort).reEquivExecutionRevert hcode hdispatch
              hdecode hbody
          · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
            have ho32 : 32 ≤ o.size := not_lt.mp hshort
            let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
            have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                "balanceOf" 0
                [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                (true, evm0S, o) false := by
              simpa [evmS, hzTrue] using hcallAll
            have hdec0 :
                config.externalABI.decode? "balanceOf" o =
                  some [skimBalanceValue balance0] := by
              simpa [balance0] using uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
            let reserve0E := UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩
                (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
            have hsourceReserve : uniswapReserve0Word evm0S = reserve0E := by
              have h := uniswapSkimFirstBalanceStaticReserve0 hAccounts hcall0
              simpa [reserve0E, reserve112Mask, u256_land_comm] using h
            by_cases hlt0 : balance0.toNat < reserve0E.toNat
            · obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
              have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                  (balance0 :: reserve0E :: ⟨5325⟩ :: skimToMaskedWord I ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    ⟨5330⟩ ::
                    UInt256.land
                      (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                      solcAddrMask ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                  balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                simpa [balance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
              obtain ⟨k6879, C6879, rd6879⟩ :=
                RD.uniswapSkimFirstExcessToSub rd5314'
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                  (reserve0E :: balance0 :: ⟨5325⟩ :: skimToMaskedWord I ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    ⟨5330⟩ ::
                    UInt256.land
                      (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                      solcAddrMask ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                  balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                simpa [balanceOfThisStaticcallActiveWords] using rd6879
              have hmem :
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).size =
                    164 :=
                balanceOfThisStaticcallMem_size_of_size_ge
                  (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
              have hread64 :
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding
                      64 32 =
                    UInt256.toByteArray ⟨128⟩ :=
                balanceOfThisStaticcallMem_read64_of_size_ge
                  (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
              have rdRev :=
                RD.uniswapSafeMathSubUnderflow_aw6_size164 rd6879' hlt0 hmem hread64
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hltSource : balance0.toNat < (uniswapReserve0Word evm0S).toNat := by
                rw [hsourceReserve]
                exact hlt0
              have hbody :
                  ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                    .reverted := by
                exact uniswapSkimBodyReverts_firstExcessUnderflow evmS evm0S I
                  (by simp only [evmS, initState]; exact hwv)
                  hunlockedSolm hguard0 hcall0 hdec0 hltSource
              exact rdRev.reEquivExecutionRevert hcode hdispatch
                hdecode hbody
            · have hle0 : reserve0E.toNat ≤ balance0.toNat := not_lt.mp hlt0
              obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
              have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                  (balance0 :: reserve0E :: ⟨5325⟩ :: skimToMaskedWord I ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    ⟨5330⟩ ::
                    UInt256.land
                      (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                      solcAddrMask ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                  balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                simpa [balance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
              obtain ⟨k6879, C6879, rd6879⟩ :=
                RD.uniswapSkimFirstExcessToSub rd5314'
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                  (reserve0E :: balance0 :: ⟨5325⟩ :: skimToMaskedWord I ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    ⟨5330⟩ ::
                    UInt256.land
                      (uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                      solcAddrMask ::
                    UInt256.land solcAddrMask
                      (uniswapSlotWord ⟨6⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                    skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                  (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                  balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                simpa [balanceOfThisStaticcallActiveWords] using rd6879
              obtain ⟨k6370, C6370, rd6370⟩ :=
                RD.uniswapSkimFirstExcessSuccessToSafeTransferEntry rd6879' hle0
              obtain ⟨cA1, σ1, z1, out1, A_in1, callGas1, _gasArg1,
                  k6595, C6595, hΘsafe0, rd6595, hout1Size⟩ :=
                UniswapV2Pair.RD.uniswapSkimSafeTransferEntryToCallMade
                  rd6370 ho32 hoSize hdepth
              let token0WordE :=
                uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
              let token0CleanE := UInt256.land solcAddrMask token0WordE
              let safeValue0 := UInt256.sub balance0 reserve0E
              let safeData0 :=
                (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                  (skimToMaskedWord I) safeValue0).readWithPadding 292 68
              have hdata0 :
                  transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
                    some safeData0 := by
                have hencoded :=
                  skimFirstSafeTransferCalldata (evm0S := evm0S) (I := I)
                    (balance0 := balance0) (reserve0 := reserve0E)
                    (toWord := skimToMaskedWord I) (skimToAddress_word_eq_masked I)
                    hsourceReserve hle0
                have hread :=
                  skimSafeTransferCallMem2_read292_68
                    (UInt256.ofNat I.codeOwner.val) (o := o) (skimToMaskedWord I) safeValue0
                    ho32 hoSize
                simpa [safeData0, safeValue0, hread] using hencoded
              let evm0E : EVM.State :=
                { evm0S with
                  accountMap := σ'
                  createdAccounts := cA'
                  σ₀ := σ₀
                  genesisBlockHeader := gh
                  blocks := bl
                  executionEnv := I }
              obtain ⟨g1Ret, A1E, hΘsafeEq⟩ := hΘsafe0
              have hcallE : callViaEVM evm0E
                  (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                  0 safeData0
                  (z1,
                    { evm0E with
                      accountMap := σ1
                      substate := A1E
                      createdAccounts := cA1 },
                    out1) := by
                refine callViaEVM.callMade (perm := true) (g' := g1Ret)
                  wordOfInt_zero.symm ?_ rfl ?_ ?_
                · refine ⟨callGas1, A_in1, ?_⟩
                  simpa [evm0E, token0CleanE, token0WordE, safeData0, safeValue0, hperm,
                    accountAddress_roundtrip] using hΘsafeEq
                · show (⟨0⟩ : UInt256) ≤ _
                  exact Fin.zero_le _
                · intro hdepthEq
                  have hdepthLt : I.depth.val < 1024 := hdepth
                  rw [show evm0E.executionEnv.depth = I.depth by simp [evm0E]] at hdepthEq
                  rw [hdepthEq] at hdepthLt
                  exact absurd hdepthLt (by decide)
              obtain ⟨σ1S, A1S, htransfer0Raw, hPostTransferAccounts0⟩ :=
                callViaEVM_accountMapEquiv (storage := config.storage)
                  (evm_evm := evm0E) (evm_solm := evm0S) hcallE hPostAccounts0
                  (by simp [evm0E, hσ0])
                  (by simp [evm0E, hcreated0])
                  (by simp [evm0E, hgenesis0])
                  (by simp [evm0E, hblocks0])
                  (by simp [evm0E])
                  (by
                    simp [evm0E, henv0, uniswapLockEnteredState,
                      uniswapUnlockedState, initState, storageStore_executionEnv])
              let evm1S : EVM.State :=
                { evm0S with
                  accountMap := σ1S
                  substate := A1S
                  createdAccounts := cA1 }
              have htransfer0Raw' : callViaEVM evm0S
                  (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                  0 safeData0 (z1, evm1S, out1) := by
                simpa [evm1S] using htransfer0Raw
              have htarget0 :
                  AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask) =
                    EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩) := by
                let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
                have hLockAccounts : accountMapEquiv σLockE σLockS := by
                  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                have hslot : token0WordE = token0WordS := by
                  simpa [σLockE, σLockS, token0WordE, token0WordS] using
                    accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
                have hcanonClean : token0CleanE.toNat < EVM.addressModulus := by
                  simpa [token0CleanE, token0WordE, u256_land_comm] using
                    solcAddrMask_result_canonical token0WordE
                have hclean : UInt256.land token0CleanE solcAddrMask = token0CleanE :=
                  solcAddrMask_clean hcanonClean
                have haddr :
                    AccountAddress.ofUInt256 token0CleanE =
                      uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩ := by
                  simpa [token0CleanE, token0WordE, token0WordS, σLockS, evmS,
                    uniswapLockEnteredState, uniswapUnlockedState, initState,
                    storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                    Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                    uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                    u256_land_comm]
                rw [hclean, haddr]
                exact (uniswapAddress_self (uniswapAddressAtSlot
                  (uniswapLockEnteredState evmS) ⟨6⟩)).symm
              have htransfer0 : callViaEVM evm0S
                  (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                  0 safeData0 (z1, evm1S, out1) := by
                simpa [htarget0] using htransfer0Raw'
              by_cases hz1False : z1 = false
              · have htransferFalse : callViaEVM evm0S
                    (EVM.address
                      (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    0 safeData0 (false, evm1S, out1) := by
                  simpa [hz1False] using htransfer0
                have henoughSource :
                    (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                  rw [hsourceReserve]
                  exact hle0
                have hbody :
                    ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                      .reverted := by
                  exact uniswapSkimBodyReverts_firstSafeTransferFailure
                    evmS evm0S evm1S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                    htransferFalse
                have rd6595False : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                    (⟨0⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                      ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToMaskedWord I :: token0CleanE ::
                      ⟨5330⟩ ::
                      UInt256.land
                        (uniswapSlotWord ⟨7⟩
                          (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                        solcAddrMask ::
                      token0CleanE :: skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                    (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                      (skimToMaskedWord I) safeValue0)
                    (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                  simpa [hz1False, token0CleanE, token0WordE, safeValue0] using rd6595
                by_cases hout1Empty : out1.size = 0
                · have rdRev :=
                    RD.uniswapSkimSafeTransferEmptyFailureReverts
                      rd6595False hout1Empty ho32 hoSize
                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                    hdecode hbody
                · by_cases hout1Sign : out1.size < 2 ^ 255
                  · have rdRev :=
                      RD.uniswapSkimSafeTransferNonemptyFailureReverts
                        rd6595False hout1Empty hout1Sign ho32 hoSize
                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                      hdecode hbody
                  · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                    have rdRev :=
                      RD.uniswapSkimSafeTransferNonemptyHugeReverts
                        rd6595False hout1Empty hhi hout1Size ho32 hoSize
                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                      hdecode hbody
              · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1False
                have htransferTrue : callViaEVM evm0S
                    (EVM.address
                      (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    0 safeData0 (true, evm1S, out1) := by
                  simpa [hz1True] using htransfer0
                have henoughSource :
                    (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                  rw [hsourceReserve]
                  exact hle0
                let token1WordE :=
                  uniswapSlotWord ⟨7⟩
                    (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                let token1CleanE := UInt256.land token1WordE solcAddrMask
                have htarget1 :
                    AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                      uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                  let token1WordS := uniswapSlotWord ⟨7⟩ σLockS I
                  have hLockAccounts : accountMapEquiv σLockE σLockS := by
                    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                  have hslot : token1WordE = token1WordS := by
                    simpa [σLockE, σLockS, token1WordE, token1WordS] using
                      accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨7⟩ ⟨0⟩
                  have hcanonClean : token1CleanE.toNat < EVM.addressModulus := by
                    simpa [token1CleanE, token1WordE, u256_land_comm] using
                      solcAddrMask_result_canonical token1WordE
                  have hclean : UInt256.land token1CleanE solcAddrMask = token1CleanE :=
                    solcAddrMask_clean hcanonClean
                  have haddr :
                      AccountAddress.ofUInt256 token1CleanE =
                        uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                    simpa [token1CleanE, token1WordE, token1WordS, σLockS, evmS,
                      uniswapLockEnteredState, uniswapUnlockedState, initState,
                      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                      Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                      uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                      u256_land_comm]
                  rw [hclean, haddr]
                have rd6595True : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                    (⟨1⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                      ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToMaskedWord I :: token0CleanE ::
                      ⟨5330⟩ :: token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                      ⟨570⟩ :: uniswapSelWord I :: [])
                    (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                      (skimToMaskedWord I) safeValue0)
                    (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                  simpa [hz1True, token0CleanE, token0WordE, token1CleanE, token1WordE,
                    safeValue0] using rd6595
                by_cases hout1Empty : out1.size = 0
                · have hsafe0 :
                      ExecStmt config
                        { contract := contract,
                          locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                        (.internalCall "_safeTransfer"
                          [.var "_token0", .var "to", .var "excess0"] "ok0")
                        (.ok
                          { contract := contract,
                            locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                          evm1S) := by
                    have hs := safeTransferInternalCallReturns_empty
                      (caller :=
                        { contract := contract,
                          locals := skimFirstExcessStore evmS evm0S I balance0 })
                      (evm := evm0S) (evm' := evm1S)
                      (tokenExpr := .var "_token0") (toExpr := .var "to")
                      (valueExpr := .var "excess0") (retVar := "ok0")
                      (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                      (recipient := skimToAddress I)
                      (value := skimExcess0Word evm0S balance0)
                      (calldata := safeData0) (out := out1)
                      rfl
                      (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                      hdata0 htransferTrue hout1Empty
                    simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                  obtain ⟨k5330, C5330, rd5330⟩ :=
                    RD.uniswapSkimSafeTransferEmptyReturnTo5330
                      rd6595True hout1Empty ho32 hoSize
                  have hPostTransferAccounts1 : accountMapEquiv σ1 evm1S.accountMap := by
                    simpa [evm1S] using hPostTransferAccounts0
                  by_cases htoken1NoCode :
                      extCodeSizeWord σ1
                        (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                  · have hguard1 :=
                      skimToken1GuardAfterFirstTransfer_false
                        (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                        (I := I) (balance0 := balance0) (token1 := token1CleanE)
                        hPostTransferAccounts1 htarget1 htoken1NoCode
                    have hbody :
                        ExecTransitionBody config contract evmS (skimStore I)
                          skimTransition.body .reverted := by
                      exact uniswapSkimBodyReverts_secondNoCode
                        evmS evm0S evm1S I
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                    have rdRev :=
                      RD.uniswapSkimSecondBalanceOfNoCodeReverts
                        (value := safeValue0) (toWord := skimToMaskedWord I)
                        (token0 := token0CleanE) (token1 := token1CleanE)
                        (sel := uniswapSelWord I) rd5330 ho32 hoSize htoken1NoCode
                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                      hdecode hbody
                  · have htoken1Code :
                        extCodeSizeWord σ1
                          (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                      htoken1NoCode
                    have hguard1 :=
                      skimToken1GuardAfterFirstTransfer_true
                        (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                        (I := I) (balance0 := balance0) (token1 := token1CleanE)
                        hPostTransferAccounts1 htarget1 htoken1Code
                    obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                        hΘ2, rd5273, hout2Size⟩ :=
                      RD.uniswapSkimSecondBalanceOfStaticcallMade
                        (value := safeValue0) (toWord := skimToMaskedWord I)
                        (token0 := token0CleanE) (token1 := token1CleanE)
                        (sel := uniswapSelWord I) rd5330 ho32 hoSize hdepth htoken1Code
                    have henv1 : evm1S.executionEnv = I := by
                      simpa [evm1S, evmS, uniswapLockEnteredState, uniswapUnlockedState,
                        initState, storageStore_executionEnv] using henv0
                    obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                        hblocks2, henv2⟩ :=
                      uniswapSkimSecondBalanceTypedCall_source
                        (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                        (I := I) (evm1S := evm1S)
                        (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                        (A_in2 := A_in2) (callGas2 := callGas2)
                        (o := o) (toWord := skimToMaskedWord I) (value := safeValue0)
                        (token1 := token1CleanE)
                        hPostTransferAccounts1
                        (by simp [evm1S])
                        (by simp [evm1S, hσ0])
                        (by simp [evm1S, hgenesis0])
                        (by simp [evm1S, hblocks0])
                        henv1 hdepth ho32 hoSize hΘ2
                    have htarget1E :
                        AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                          EVM.address
                            (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩) := by
                      change
                        AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                          EVM.address
                            (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                      rw [htarget1]
                      exact
                        (uniswapAddress_self
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                    have hcall1 : typedCallViaEVM config evm1S
                        (EVM.address
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                        (z2, evm2S, out2) false := by
                      simpa [htarget1E] using hcall1Raw
                    by_cases hz2False : z2 = false
                    · have hcall1False : typedCallViaEVM config evm1S
                          (EVM.address
                            (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                          "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                          (false, evm2S, out2) false := by
                        simpa [hz2False] using hcall1
                      have hbody :
                          ExecTransitionBody config contract evmS (skimStore I)
                            skimTransition.body .reverted := by
                        exact uniswapSkimBodyReverts_secondCallFailure
                          evmS evm0S evm1S evm2S I
                          (by simp only [evmS, initState]; exact hwv)
                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                          hguard1 hcall1False
                      have hstatus :
                          (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                        simp [hz2False]
                      have rdRev :=
                        RD.uniswapSkimSecondBalanceCallFailureReverts
                          rd5273 hstatus hout2Size
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                        hdecode hbody
                    · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                      have hcall1True : typedCallViaEVM config evm1S
                          (EVM.address
                            (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                          "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                          (true, evm2S, out2) false := by
                        simpa [hz2True] using hcall1
                      have hstatus :
                          (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                        rw [hz2True]
                        decide
                      obtain ⟨k5291, C5291, rd5291⟩ :=
                        RD.uniswapSkimSecondBalanceCallSuccessToDecode
                          rd5273 hstatus
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      by_cases hshort2 : out2.size < 32
                      · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                          change uniswapExternalABI.decode? "balanceOf" out2 = none
                          simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                            (decodeReturnValueWithMode_legacy_uint256_none_short
                              (returndata := out2) hshort2)
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_secondCallDecode
                            evmS evm0S evm1S evm2S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                            hguard1 hcall1True hdec1
                        have rdRev :=
                          RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts
                            rd5291 ho32 hoSize hshort2 hout2Size
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          hdecode hbody
                      · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                        let balance1 :=
                          UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                        have hdec1 :
                            config.externalABI.decode? "balanceOf" out2 =
                              some [skimBalanceValue balance1] := by
                          simpa [balance1] using
                            uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                        let reserve1E :=
                          UInt256.land reserve112Mask
                            (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                        have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                          have h :=
                            uniswapSkimSecondBalanceStaticReserve1
                              hPostTransferAccounts1 henv1 hcall1True
                          simpa [reserve1E, u256_land_comm] using h
                        obtain ⟨k5314, C5314, rd5314⟩ :=
                          RD.uniswapSkimSecondBalanceReturnWordDecodeOk
                            rd5291 ho32 hoSize ho32_2 hout2Size
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨5314⟩
                            (balance1 :: reserve1E :: ⟨5325⟩ :: skimToMaskedWord I ::
                              token1CleanE :: ⟨5433⟩ ::
                              token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                              ⟨570⟩ :: uniswapSelWord I :: [])
                            (skimSecondBalanceStaticcallMem
                              (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                              safeValue0 out2)
                            (UInt256.ofNat 13) out2 (cA2, σ2) k5314 C5314 := by
                          simpa [balance1, reserve1E, u256_land_comm] using rd5314
                        by_cases hlt1 : balance1.toNat < reserve1E.toNat
                        · obtain ⟨k6879, C6879, rd6879⟩ :=
                            RD.uniswapSkimFirstExcessToSub rd5314'
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              ⟨6879⟩
                              (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                token1CleanE :: ⟨5433⟩ ::
                                token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                ⟨570⟩ :: uniswapSelWord I :: [])
                              (skimSecondBalanceStaticcallMem
                                (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                safeValue0 out2)
                              (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                            simpa using rd6879
                          have hmem :
                              (skimSecondBalanceStaticcallMem
                                (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                safeValue0 out2).size = 388 :=
                            skimSecondBalanceStaticcallMem_size_of_size_ge
                              (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) safeValue0
                              out2 ho32 hoSize ho32_2 hout2Size
                          have hread64 :
                              (skimSecondBalanceStaticcallMem
                                (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                safeValue0 out2).readWithPadding 64 32 =
                                UInt256.toByteArray ⟨292⟩ :=
                            skimSecondBalanceStaticcallMem_read64_of_size_ge
                              (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) safeValue0
                              out2 ho32 hoSize ho32_2 hout2Size
                          have rdRev :=
                            RD.uniswapSafeMathSubUnderflow_aw13_free292
                              rd6879' hlt1 hmem hread64
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have hltSource :
                              balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                            rw [hsourceReserve1]
                            exact hlt1
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_secondExcessUnderflow
                              evmS evm0S evm1S evm2S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                              hguard1 hcall1True hdec1 hltSource
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            hdecode hbody
                        · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                          obtain ⟨k6879, C6879, rd6879⟩ :=
                            RD.uniswapSkimFirstExcessToSub rd5314'
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              ⟨6879⟩
                              (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                token1CleanE :: ⟨5433⟩ ::
                                token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                ⟨570⟩ :: uniswapSelWord I :: [])
                              (skimSecondBalanceStaticcallMem
                                (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                safeValue0 out2)
                              (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                            simpa using rd6879
                          obtain ⟨k6370, C6370, rd6370⟩ :=
                            RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          let safeValue1 := UInt256.sub balance1 reserve1E
                          let safeData1 :=
                            (skimSecondSafeTransferCallMem2
                              (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                              safeValue0 out2 safeValue1).readWithPadding 456 68
                          have hdata1 :
                              transferCalldata? (skimToAddress I)
                                  (skimExcess1Word evm2S balance1) =
                                some safeData1 := by
                            have hencoded :=
                              skimSecondSafeTransferCalldata
                                (evm2S := evm2S) (I := I) (o := o) (out2 := out2)
                                (balance1 := balance1) (reserve1 := reserve1E)
                                (prevValue := safeValue0) (toWord := skimToMaskedWord I)
                                (skimToAddress_word_eq_masked I) hsourceReserve1 hle1
                                ho32 hoSize ho32_2 hout2Size
                            simpa [safeData1, safeValue1] using hencoded
                          have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              ⟨6370⟩
                              (safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                ⟨570⟩ :: uniswapSelWord I :: [])
                              (skimSecondBalanceStaticcallMem
                                (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                safeValue0 out2)
                              (UInt256.ofNat 13) out2 (cA2, σ2) k6370 C6370 := by
                            simpa [safeValue1] using rd6370
                          obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                              k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                            RD.uniswapSkimSecondSafeTransferEntryToCallMade
                              rd6370' ho32 hoSize ho32_2 hout2Size hdepth
                          let evm2E : EVM.State :=
                            { evm2S with
                              accountMap := σ2
                              createdAccounts := cA2
                              σ₀ := σ₀
                              genesisBlockHeader := gh
                              blocks := bl
                              executionEnv := I }
                          obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                          have hcallE1 : callViaEVM evm2E
                              (AccountAddress.ofUInt256
                                (UInt256.land token1CleanE solcAddrMask))
                              0 safeData1
                              (z3,
                                { evm2E with
                                  accountMap := σ3
                                  substate := A3E
                                  createdAccounts := cA3 },
                                out3) := by
                            refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                              wordOfInt_zero.symm ?_ rfl ?_ ?_
                            · refine ⟨callGas3, A_in3, ?_⟩
                              simpa [evm2E, safeData1, safeValue1, hperm,
                                accountAddress_roundtrip] using hΘsafeEq1
                            · show (⟨0⟩ : UInt256) ≤ _
                              exact Fin.zero_le _
                            · intro hdepthEq
                              have hdepthLt : I.depth.val < 1024 := hdepth
                              rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                at hdepthEq
                              rw [hdepthEq] at hdepthLt
                              exact absurd hdepthLt (by decide)
                          obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                            callViaEVM_accountMapEquiv (storage := config.storage)
                              (evm_evm := evm2E) (evm_solm := evm2S)
                              hcallE1 hPost2
                              (by simp [evm2E, hσ2])
                              (by simp [evm2E, hcreated2])
                              (by simp [evm2E, hgenesis2])
                              (by simp [evm2E, hblocks2])
                              (by simp [evm2E])
                              (by simp [evm2E, henv2, henv1])
                          let evm3S : EVM.State :=
                            { evm2S with
                              accountMap := σ3S
                              substate := A3S
                              createdAccounts := cA3 }
                          have htransfer1Raw' : callViaEVM evm2S
                              (AccountAddress.ofUInt256
                                (UInt256.land token1CleanE solcAddrMask))
                              0 safeData1 (z3, evm3S, out3) := by
                            simpa [evm3S] using htransfer1Raw
                          have htransfer1Target :
                              AccountAddress.ofUInt256
                                  (UInt256.land token1CleanE solcAddrMask) =
                                EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩) := by
                            rw [htarget1]
                            exact (uniswapAddress_self
                              (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                          have htransfer1 : callViaEVM evm2S
                              (EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                              0 safeData1 (z3, evm3S, out3) := by
                            simpa [htransfer1Target] using htransfer1Raw'
                          have hPostTransferAccounts3 :
                              accountMapEquiv σ3 evm3S.accountMap := by
                            simpa [evm3S] using hPostTransferAccounts2
                          have henv3 : evm3S.executionEnv = I := by
                            simpa [evm3S] using henv2.trans henv1
                          have henough1Source :
                              (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                            rw [hsourceReserve1]
                            exact hle1
                          have hfinish :
                              ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨5433⟩
                                  (token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  mem aw outRet (cA3, σ3) kR CR →
                                ExecStmt config
                                  { contract := contract,
                                    locals :=
                                      skimSecondExcessStore evmS evm0S evm2S I
                                        balance0 balance1 } evm2S
                                  (.internalCall "_safeTransfer"
                                    [.var "_token1", .var "to", .var "excess1"] "ok1")
                                  (.ok
                                    { contract := contract,
                                      locals :=
                                        skimSecondSafeTransferStore evmS evm0S evm2S I
                                          balance0 balance1 }
                                    evm3S) →
                                runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
                                  g A I := by
                            intro mem outRet aw kR CR rd5433 hsafe1
                            have rdRet :=
                              RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body
                                  (.returned
                                    { contract := contract,
                                      locals :=
                                        skimSecondSafeTransferStore evmS evm0S evm2S I
                                          balance0 balance1 }
                                    (uniswapLockExitedState evm3S) none) := by
                              exact uniswapSkimBodyReturns
                                evmS evm0S evm1S evm2S evm3S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                hguard1 hcall1True hdec1 henough1Source hsafe1
                            have hCreatedRet :
                                cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                              simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                storageStore_createdAccounts]
                            have hAccountsRet :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                  (uniswapLockExitedState evm3S).accountMap := by
                              have hs :=
                                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                  hPostTransferAccounts3
                              simpa [uniswapLockExitedState, uniswapUnlockedState,
                                storageStore_accountMap, henv3] using hs
                            exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                              hdecode hbody hCreatedRet
                              hAccountsRet (returnEquiv.fallthrough rfl rfl (by native_decide))
                          by_cases hz3False : z3 = false
                          · have htransfer1False : callViaEVM evm2S
                                (EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩))
                                0 safeData1 (false, evm3S, out3) := by
                              simpa [hz3False] using htransfer1
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                evmS evm0S evm1S evm2S evm3S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                hguard1 hcall1True hdec1 henough1Source hdata1
                                htransfer1False
                            have rd6595False : RD uniswapV2PairBytecode I
                                (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨6595⟩
                                (⟨0⟩ :: ⟨524⟩ ::
                                  UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                  safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                  token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                  ⟨570⟩ :: uniswapSelWord I :: [])
                                (skimSecondSafeTransferCallMem2
                                  (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                  safeValue0 out2 safeValue1)
                                (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                              simpa [hz3False, safeValue1] using rd6595b
                            by_cases hout3Empty : out3.size = 0
                            · have rdRev :=
                                RD.uniswapSkimSecondSafeTransferEmptyFailureReverts
                                  rd6595False hout3Empty ho32 hoSize ho32_2 hout2Size
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                hdecode hbody
                            · by_cases hout3Sign : out3.size < 2 ^ 255
                              · have rdRev :=
                                  RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts
                                    rd6595False hout3Empty hout3Sign ho32 hoSize
                                    ho32_2 hout2Size
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  hdecode hbody
                              · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                have rdRev :=
                                  RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                    rd6595False hout3Empty hhi hout3Size ho32 hoSize
                                    ho32_2 hout2Size
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  hdecode hbody
                          · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                            have htransfer1True : callViaEVM evm2S
                                (EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩))
                                0 safeData1 (true, evm3S, out3) := by
                              simpa [hz3True] using htransfer1
                            have rd6595True : RD uniswapV2PairBytecode I
                                (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨6595⟩
                                (⟨1⟩ :: ⟨524⟩ ::
                                  UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                  safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                  token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                  ⟨570⟩ :: uniswapSelWord I :: [])
                                (skimSecondSafeTransferCallMem2
                                  (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                  safeValue0 out2 safeValue1)
                                (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                              simpa [hz3True, safeValue1] using rd6595b
                            by_cases hout3Empty : out3.size = 0
                            · have hsafe1 :
                                  ExecStmt config
                                    { contract := contract,
                                      locals :=
                                        skimSecondExcessStore evmS evm0S evm2S I
                                          balance0 balance1 } evm2S
                                    (.internalCall "_safeTransfer"
                                      [.var "_token1", .var "to", .var "excess1"] "ok1")
                                    (.ok
                                      { contract := contract,
                                        locals :=
                                          skimSecondSafeTransferStore evmS evm0S evm2S I
                                            balance0 balance1 }
                                      evm3S) := by
                                have hs := safeTransferInternalCallReturns_empty
                                  (caller :=
                                    { contract := contract,
                                      locals :=
                                        skimSecondExcessStore evmS evm0S evm2S I
                                          balance0 balance1 })
                                  (evm := evm2S) (evm' := evm3S)
                                  (tokenExpr := .var "_token1") (toExpr := .var "to")
                                  (valueExpr := .var "excess1") (retVar := "ok1")
                                  (token :=
                                    uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                                  (recipient := skimToAddress I)
                                  (value := skimExcess1Word evm2S balance1)
                                  (calldata := safeData1) (out := out3)
                                  rfl
                                  (evalExprs_skim_safeTransfer1_args
                                    evmS evm0S evm2S I balance0 balance1)
                                  hdata1 htransfer1True hout3Empty
                                simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                  using hs
                              obtain ⟨k5433, C5433, rd5433⟩ :=
                                RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433
                                  rd6595True hout3Empty ho32 hoSize ho32_2 hout2Size
                              exact hfinish rd5433 hsafe1
                            · by_cases hout3Sign : out3.size < 2 ^ 255
                              · by_cases hshort3 : out3.size < 32
                                · have hdecSafe1 :
                                      ABI.decodeReturnValueWithMode?
                                          config.abiDecodeMode boolTy out3 =
                                        none := by
                                    change
                                      ABI.decodeReturnValueWithMode?
                                          DecodeMode.legacySolc05 boolTy out3 =
                                        none
                                    exact decodeReturnValueWithMode_legacy_bool_none_short
                                      (returndata := out3) hshort3
                                  have hbody :
                                      ExecTransitionBody config contract evmS (skimStore I)
                                        skimTransition.body .reverted := by
                                    exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                      evmS evm0S evm1S evm2S evm3S I
                                      (by simp only [evmS, initState]; exact hwv)
                                      hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                      hguard1 hcall1True hdec1 henough1Source hdata1
                                      htransfer1True hout3Empty hdecSafe1
                                  have rdRev :=
                                    RD.uniswapSkimSecondSafeTransferNonemptyShortReverts
                                      rd6595True hout3Empty hshort3 hout3Sign ho32 hoSize
                                      ho32_2 hout2Size
                                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    hdecode hbody
                                · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                  let safeWord1 :=
                                    UInt256.ofNat
                                      (fromByteArrayBigEndian (out3.extract 0 32))
                                  by_cases hword1 : safeWord1 = ⟨0⟩
                                  · have hdecSafe1 :
                                        ABI.decodeReturnValueWithMode?
                                            config.abiDecodeMode boolTy out3 =
                                          some (.bool false) := by
                                      change
                                        ABI.decodeReturnValueWithMode?
                                            DecodeMode.legacySolc05 boolTy out3 =
                                          some (.bool false)
                                      exact decodeReturnValueWithMode_legacy_bool_false
                                        (returndata := out3) hout332 hout3Sign hword1
                                    have hbody :
                                        ExecTransitionBody config contract evmS (skimStore I)
                                          skimTransition.body .reverted := by
                                      exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                        evmS evm0S evm1S evm2S evm3S I
                                        (by simp only [evmS, initState]; exact hwv)
                                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                        hguard1 hcall1True hdec1 henough1Source hdata1
                                        htransfer1True hout3Empty hdecSafe1
                                    have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts
                                        rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                        hoSize ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      hdecode hbody
                                  · have hdecSafe1 :
                                        ABI.decodeReturnValueWithMode?
                                            config.abiDecodeMode boolTy out3 =
                                          some (.bool true) := by
                                      change
                                        ABI.decodeReturnValueWithMode?
                                            DecodeMode.legacySolc05 boolTy out3 =
                                          some (.bool true)
                                      exact decodeReturnValueWithMode_legacy_bool_true
                                        (returndata := out3) hout332 hout3Sign hword1
                                    have hsafe1 :
                                        ExecStmt config
                                          { contract := contract,
                                            locals :=
                                              skimSecondExcessStore evmS evm0S evm2S I
                                                balance0 balance1 } evm2S
                                          (.internalCall "_safeTransfer"
                                            [.var "_token1", .var "to", .var "excess1"]
                                            "ok1")
                                          (.ok
                                            { contract := contract,
                                              locals :=
                                                skimSecondSafeTransferStore evmS evm0S evm2S I
                                                  balance0 balance1 }
                                            evm3S) := by
                                      have hs := safeTransferInternalCallReturns_decodeTrue
                                        (caller :=
                                          { contract := contract,
                                            locals :=
                                              skimSecondExcessStore evmS evm0S evm2S I
                                                balance0 balance1 })
                                        (evm := evm2S) (evm' := evm3S)
                                        (tokenExpr := .var "_token1") (toExpr := .var "to")
                                        (valueExpr := .var "excess1") (retVar := "ok1")
                                        (token :=
                                          uniswapAddressAtSlot
                                            (uniswapLockEnteredState evmS) ⟨7⟩)
                                        (recipient := skimToAddress I)
                                        (value := skimExcess1Word evm2S balance1)
                                        (calldata := safeData1) (out := out3)
                                        rfl
                                        (evalExprs_skim_safeTransfer1_args
                                          evmS evm0S evm2S I balance0 balance1)
                                        hdata1 htransfer1True hout3Empty hdecSafe1
                                      simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                        using hs
                                    obtain ⟨k5433, C5433, rd5433⟩ :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet
                                        rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                        hoSize ho32_2 hout2Size (by jump_dest)
                                    exact hfinish rd5433 hsafe1
                              · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                have hdecSafe1 :
                                    ABI.decodeReturnValueWithMode?
                                        config.abiDecodeMode boolTy out3 =
                                      none := by
                                  change
                                    ABI.decodeReturnValueWithMode?
                                        DecodeMode.legacySolc05 boolTy out3 =
                                      none
                                  exact decodeReturnValueWithMode_legacy_bool_none_huge
                                    (returndata := out3) hhi
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                    evmS evm0S evm1S evm2S evm3S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 henough1Source hdata1
                                    htransfer1True hout3Empty hdecSafe1
                                have rdRev :=
                                  RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                    rd6595True hout3Empty hhi hout3Size ho32 hoSize
                                    ho32_2 hout2Size
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  hdecode hbody
                · by_cases hout1Sign : out1.size < 2 ^ 255
                  · by_cases hshort1 : out1.size < 32
                    · have hdecSafe0 :
                          ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                            none := by
                        change
                          ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                            none
                        exact decodeReturnValueWithMode_legacy_bool_none_short
                          (returndata := out1) hshort1
                      have hbody :
                          ExecTransitionBody config contract evmS (skimStore I)
                            skimTransition.body .reverted := by
                        exact uniswapSkimBodyReverts_firstSafeTransferDecode
                          evmS evm0S evm1S I
                          (by simp only [evmS, initState]; exact hwv)
                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                          htransferTrue hout1Empty hdecSafe0
                      have rdRev :=
                        RD.uniswapSkimSafeTransferNonemptyShortReverts
                          rd6595True hout1Empty hshort1 hout1Sign ho32 hoSize
                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                        hdecode hbody
                    · have hout132 : 32 ≤ out1.size := not_lt.mp hshort1
                      let safeWord0 :=
                        UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
                      by_cases hword0 : safeWord0 = ⟨0⟩
                      · have hdecSafe0 :
                            ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                              some (.bool false) := by
                          change
                            ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                              some (.bool false)
                          exact decodeReturnValueWithMode_legacy_bool_false
                            (returndata := out1) hout132 hout1Sign hword0
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_firstSafeTransferDecodeFalse
                            evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                            htransferTrue hout1Empty hdecSafe0
                        have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyFalseReverts
                            rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          hdecode hbody
                      · have hdecSafe0 :
                            ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                              some (.bool true) := by
                          change
                            ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                              some (.bool true)
                          exact decodeReturnValueWithMode_legacy_bool_true
                            (returndata := out1) hout132 hout1Sign hword0
                        have hsafe0 :
                            ExecStmt config
                              { contract := contract,
                                locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                              (.internalCall "_safeTransfer"
                                [.var "_token0", .var "to", .var "excess0"] "ok0")
                              (.ok
                                { contract := contract,
                                  locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                                evm1S) := by
                          have hs := safeTransferInternalCallReturns_decodeTrue
                            (caller :=
                              { contract := contract,
                                locals := skimFirstExcessStore evmS evm0S I balance0 })
                            (evm := evm0S) (evm' := evm1S)
                            (tokenExpr := .var "_token0") (toExpr := .var "to")
                            (valueExpr := .var "excess0") (retVar := "ok0")
                            (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                            (recipient := skimToAddress I)
                            (value := skimExcess0Word evm0S balance0)
                            (calldata := safeData0) (out := out1)
                            rfl
                            (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                            hdata0 htransferTrue hout1Empty hdecSafe0
                          simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                        obtain ⟨k5330, C5330, rd5330⟩ :=
                          RD.uniswapSkimSafeTransferNonemptyTrueToRet
                            rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                            (by jump_dest)
                        have hPostTransferAccounts1 :
                            accountMapEquiv σ1 evm1S.accountMap := by
                          simpa [evm1S] using hPostTransferAccounts0
                        have hout1Small : out1.size < 2 ^ 138 := by
                          exact Theta_returnData_size_lt_2pow138_of_eq
                            (blob := I.blobVersionedHashes) (cA := cA')
                            (gh := evm0E.genesisBlockHeader) (blocks := evm0E.blocks)
                            (σ := σ') (σ₀ := evm0E.σ₀) (A := A_in1)
                            (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val))
                            (o := I.sender)
                            (r := AccountAddress.ofUInt256
                              (UInt256.land token0CleanE solcAddrMask))
                            (c := toExecute σ'
                              (AccountAddress.ofUInt256
                                (UInt256.land token0CleanE solcAddrMask)))
                            (g := callGas1) (p := UInt256.ofNat I.gasPrice)
                            (v := ⟨0⟩) (v' := ⟨0⟩) (d := safeData0)
                            (e := I.depth + 1) (H := I.header) (w := I.perm)
                            (by simpa [evm0E, safeData0, safeValue0, hperm] using hΘsafeEq)
                            (by
                              exact Ethereum.EVM.ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
                                _ _ _)
                        by_cases htoken1NoCode :
                            extCodeSizeWord σ1
                              (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                        · have hguard1 :=
                            skimToken1GuardAfterFirstTransfer_false
                              (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                              (I := I) (balance0 := balance0) (token1 := token1CleanE)
                              hPostTransferAccounts1 htarget1 htoken1NoCode
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_secondNoCode
                              evmS evm0S evm1S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                          have rdRev :=
                            RD.uniswapSkimSecondBalanceOfNoCodeReverts_dynamic
                              (value := safeValue0) (toWord := skimToMaskedWord I)
                              (token0 := token0CleanE) (token1 := token1CleanE)
                              (sel := uniswapSelWord I) rd5330 ho32 hoSize
                              hout1Empty hout1Sign htoken1NoCode
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            hdecode hbody
                        · have htoken1Code :
                              extCodeSizeWord σ1
                                (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                            htoken1NoCode
                          have hguard1 :=
                            skimToken1GuardAfterFirstTransfer_true
                              (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                              (I := I) (balance0 := balance0) (token1 := token1CleanE)
                              hPostTransferAccounts1 htarget1 htoken1Code
                          obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                              hΘ2, rd5273, hout2Size⟩ :=
                            RD.uniswapSkimSecondBalanceOfStaticcallMade_dynamic
                              (value := safeValue0) (toWord := skimToMaskedWord I)
                              (token0 := token0CleanE) (token1 := token1CleanE)
                              (sel := uniswapSelWord I) rd5330 ho32 hoSize
                              hout1Empty hout1Sign hdepth htoken1Code
                          have henv1 : evm1S.executionEnv = I := by
                            simpa [evm1S, evmS, uniswapLockEnteredState,
                              uniswapUnlockedState, initState, storageStore_executionEnv]
                              using henv0
                          obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                              hblocks2, henv2⟩ :=
                            uniswapSkimSecondBalanceTypedCall_source_dynamic
                              (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                              (I := I) (evm1S := evm1S)
                              (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                              (A_in2 := A_in2) (callGas2 := callGas2)
                              (o := o) (out1 := out1) (toWord := skimToMaskedWord I)
                              (value := safeValue0) (token1 := token1CleanE)
                              hPostTransferAccounts1
                              (by simp [evm1S])
                              (by simp [evm1S, hσ0])
                              (by simp [evm1S, hgenesis0])
                              (by simp [evm1S, hblocks0])
                              henv1 hdepth ho32 hoSize hout1Empty hout1Sign hΘ2
                          have htarget1E :
                              AccountAddress.ofUInt256
                                  (UInt256.land token1CleanE solcAddrMask) =
                                EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩) := by
                            change
                              AccountAddress.ofUInt256
                                  (UInt256.land token1CleanE solcAddrMask) =
                                EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩)
                            rw [htarget1]
                            exact
                              (uniswapAddress_self
                                (uniswapAddressAtSlot
                                  (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                          have hcall1 : typedCallViaEVM config evm1S
                              (EVM.address
                                (uniswapAddressAtSlot
                                  (uniswapLockEnteredState evmS) ⟨7⟩))
                              "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                              (z2, evm2S, out2) false := by
                            simpa [htarget1E] using hcall1Raw
                          by_cases hz2False : z2 = false
                          · have hcall1False : typedCallViaEVM config evm1S
                                (EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩))
                                "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                (false, evm2S, out2) false := by
                              simpa [hz2False] using hcall1
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_secondCallFailure
                                evmS evm0S evm1S evm2S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                hguard1 hcall1False
                            have hstatus :
                                (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                              simp [hz2False]
                            have rdRev :=
                              RD.uniswapSkimSecondBalanceCallFailureReverts_dynamic
                                rd5273 hstatus hout2Size
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                              hdecode hbody
                          · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                            have hcall1True : typedCallViaEVM config evm1S
                                (EVM.address
                                  (uniswapAddressAtSlot
                                    (uniswapLockEnteredState evmS) ⟨7⟩))
                                "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                (true, evm2S, out2) false := by
                              simpa [hz2True] using hcall1
                            have hstatus :
                                (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                              rw [hz2True]
                              decide
                            obtain ⟨k5291, C5291, rd5291⟩ :=
                              RD.uniswapSkimSecondBalanceCallSuccessToDecode_dynamic
                                rd5273 hstatus
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            by_cases hshort2 : out2.size < 32
                            · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                                change uniswapExternalABI.decode? "balanceOf" out2 = none
                                simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                                  (decodeReturnValueWithMode_legacy_uint256_none_short
                                    (returndata := out2) hshort2)
                              have hbody :
                                  ExecTransitionBody config contract evmS (skimStore I)
                                    skimTransition.body .reverted := by
                                exact uniswapSkimBodyReverts_secondCallDecode
                                  evmS evm0S evm1S evm2S I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                  hguard1 hcall1True hdec1
                              have rdRev :=
                                RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts_dynamic
                                  rd5291 ho32 hoSize hout1Empty hout1Sign hshort2 hout2Size
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                hdecode hbody
                            · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                              let balance1 :=
                                UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                              have hdec1 :
                                  config.externalABI.decode? "balanceOf" out2 =
                                    some [skimBalanceValue balance1] := by
                                simpa [balance1] using
                                  uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                              let reserve1E :=
                                UInt256.land reserve112Mask
                                  (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                              have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                                have h :=
                                  uniswapSkimSecondBalanceStaticReserve1
                                    hPostTransferAccounts1 henv1 hcall1True
                                simpa [reserve1E, u256_land_comm] using h
                              obtain ⟨k5314, C5314, rd5314⟩ :=
                                RD.uniswapSkimSecondBalanceReturnWordDecodeOk_dynamic
                                  rd5291 ho32 hoSize hout1Empty hout1Sign ho32_2 hout2Size
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hawBalance :=
                                skimSecondBalanceDynamicStaticcallWords_mload64_ptr_same
                                  out1 hout1Sign
                              have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨5314⟩
                                  (balance1 :: reserve1E :: ⟨5325⟩ :: skimToMaskedWord I ::
                                    token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceDynamicStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out1 out2)
                                  (skimSecondBalanceDynamicStaticcallWords out1)
                                  out2 (cA2, σ2) k5314 C5314 := by
                                simpa [balance1, reserve1E, u256_land_comm, hawBalance] using
                                  rd5314
                              by_cases hlt1 : balance1.toNat < reserve1E.toNat
                              · obtain ⟨k6879, C6879, rd6879⟩ :=
                                  RD.uniswapSkimFirstExcessToSub rd5314'
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have rd6879' := by
                                  simpa using rd6879
                                have rdRev :=
                                  RD.uniswapSafeMathSubUnderflow_dynamic rd6879'
                                    (by simpa [balance1, reserve1E, u256_land_comm] using hlt1)
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have hltSource :
                                    balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                                  rw [hsourceReserve1]
                                  exact hlt1
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondExcessUnderflow
                                    evmS evm0S evm1S evm2S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 hltSource
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  hdecode hbody
                              · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                                obtain ⟨k6879, C6879, rd6879⟩ :=
                                  RD.uniswapSkimFirstExcessToSub rd5314'
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6879⟩
                                    (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                      token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondBalanceDynamicStaticcallMem
                                      (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                      safeValue0 out1 out2)
                                    (skimSecondBalanceDynamicStaticcallWords out1)
                                    out2 (cA2, σ2) k6879 C6879 := by
                                  simpa using rd6879
                                obtain ⟨k6370, C6370, rd6370⟩ :=
                                  RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                let safeValue1 := UInt256.sub balance1 reserve1E
                                let safeData1 :=
                                  (skimSecondSafeTransferDynamicCallMem2
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out1 out2 safeValue1).readWithPadding
                                    (skimSecondSafeTransferDynamicCallPtr out1).toNat 68
                                have hdata1 :
                                    transferCalldata? (skimToAddress I)
                                        (skimExcess1Word evm2S balance1) =
                                      some safeData1 := by
                                  have hencoded :=
                                    skimSecondSafeTransferCalldata_dynamic
                                      (evm2S := evm2S) (I := I) (o := o) (out1 := out1)
                                      (out2 := out2) (balance1 := balance1)
                                      (reserve1 := reserve1E) (prevValue := safeValue0)
                                      (toWord := skimToMaskedWord I)
                                      (skimToAddress_word_eq_masked I)
                                      hsourceReserve1 hle1 ho32 hoSize hout1Empty
                                      hout1Sign ho32_2 hout2Size
                                  simpa [safeData1, safeValue1] using hencoded
                                have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6370⟩
                                    (safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondBalanceDynamicStaticcallMem
                                      (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                      safeValue0 out1 out2)
                                    (skimSecondBalanceDynamicStaticcallWords out1)
                                    out2 (cA2, σ2) k6370 C6370 := by
                                  simpa [safeValue1] using rd6370
                                obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                                    k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                                  RD.uniswapSkimSecondSafeTransferEntryToCallMade_dynamic_offset
                                    rd6370' ho32 hoSize hout1Empty hout1Sign ho32_2
                                    hout2Size hdepth
                                let evm2E : EVM.State :=
                                  { evm2S with
                                    accountMap := σ2
                                    createdAccounts := cA2
                                    σ₀ := σ₀
                                    genesisBlockHeader := gh
                                    blocks := bl
                                    executionEnv := I }
                                obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                                have hout3Small : out3.size < 2 ^ 138 := by
                                  exact Theta_returnData_size_lt_2pow138_of_eq
                                    (blob := I.blobVersionedHashes) (cA := cA2)
                                    (gh := evm2E.genesisBlockHeader) (blocks := evm2E.blocks)
                                    (σ := σ2) (σ₀ := evm2E.σ₀) (A := A_in3)
                                    (s := AccountAddress.ofUInt256
                                      (UInt256.ofNat I.codeOwner.val))
                                    (o := I.sender)
                                    (r := AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask))
                                    (c := toExecute σ2
                                      (AccountAddress.ofUInt256
                                        (UInt256.land token1CleanE solcAddrMask)))
                                    (g := callGas3) (p := UInt256.ofNat I.gasPrice)
                                    (v := ⟨0⟩) (v' := ⟨0⟩) (d := safeData1)
                                    (e := I.depth + 1) (H := I.header) (w := I.perm)
                                    (by
                                      simpa [evm2E, safeData1, safeValue1, hperm] using
                                        hΘsafeEq1)
                                    (by
                                      exact
                                        Ethereum.EVM.ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
                                          _ _ _)
                                have hcallE1 : callViaEVM evm2E
                                    (AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask))
                                    0 safeData1
                                    (z3,
                                      { evm2E with
                                        accountMap := σ3
                                        substate := A3E
                                        createdAccounts := cA3 },
                                      out3) := by
                                  refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                                    wordOfInt_zero.symm ?_ rfl ?_ ?_
                                  · refine ⟨callGas3, A_in3, ?_⟩
                                    simpa [evm2E, safeData1, safeValue1, hperm,
                                      accountAddress_roundtrip] using hΘsafeEq1
                                  · show (⟨0⟩ : UInt256) ≤ _
                                    exact Fin.zero_le _
                                  · intro hdepthEq
                                    have hdepthLt : I.depth.val < 1024 := hdepth
                                    rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                      at hdepthEq
                                    rw [hdepthEq] at hdepthLt
                                    exact absurd hdepthLt (by decide)
                                obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                                  callViaEVM_accountMapEquiv (storage := config.storage)
                                    (evm_evm := evm2E) (evm_solm := evm2S)
                                    hcallE1 hPost2
                                    (by simp [evm2E, hσ2])
                                    (by simp [evm2E, hcreated2])
                                    (by simp [evm2E, hgenesis2])
                                    (by simp [evm2E, hblocks2])
                                    (by simp [evm2E])
                                    (by simp [evm2E, henv2, henv1])
                                let evm3S : EVM.State :=
                                  { evm2S with
                                    accountMap := σ3S
                                    substate := A3S
                                    createdAccounts := cA3 }
                                have htransfer1Raw' : callViaEVM evm2S
                                    (AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask))
                                    0 safeData1 (z3, evm3S, out3) := by
                                  simpa [evm3S] using htransfer1Raw
                                have htransfer1Target :
                                    AccountAddress.ofUInt256
                                        (UInt256.land token1CleanE solcAddrMask) =
                                      EVM.address
                                        (uniswapAddressAtSlot
                                          (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                  rw [htarget1]
                                  exact (uniswapAddress_self
                                    (uniswapAddressAtSlot
                                      (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                                have htransfer1 : callViaEVM evm2S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    0 safeData1 (z3, evm3S, out3) := by
                                  simpa [htransfer1Target] using htransfer1Raw'
                                have hPostTransferAccounts3 :
                                    accountMapEquiv σ3 evm3S.accountMap := by
                                  simpa [evm3S] using hPostTransferAccounts2
                                have henv3 : evm3S.executionEnv = I := by
                                  simpa [evm3S] using henv2.trans henv1
                                have henough1Source :
                                    (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                                  rw [hsourceReserve1]
                                  exact hle1
                                have hfinish :
                                    ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                        ⟨5433⟩
                                        (token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                          ⟨570⟩ :: uniswapSelWord I :: [])
                                        mem aw outRet (cA3, σ3) kR CR →
                                      ExecStmt config
                                        { contract := contract,
                                          locals :=
                                            skimSecondExcessStore evmS evm0S evm2S I
                                              balance0 balance1 } evm2S
                                        (.internalCall "_safeTransfer"
                                          [.var "_token1", .var "to", .var "excess1"] "ok1")
                                        (.ok
                                          { contract := contract,
                                            locals :=
                                              skimSecondSafeTransferStore evmS evm0S evm2S I
                                                balance0 balance1 }
                                          evm3S) →
                                      runtimeEquivalenceFor config contract cA gh bl σ_evm
                                        σ_solm σ₀ g A I := by
                                  intro mem outRet aw kR CR rd5433 hsafe1
                                  have rdRet :=
                                    RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                                  have hbody :
                                      ExecTransitionBody config contract evmS (skimStore I)
                                        skimTransition.body
                                        (.returned
                                          { contract := contract,
                                            locals :=
                                              skimSecondSafeTransferStore evmS evm0S evm2S I
                                                balance0 balance1 }
                                          (uniswapLockExitedState evm3S) none) := by
                                    exact uniswapSkimBodyReturns
                                      evmS evm0S evm1S evm2S evm3S I
                                      (by simp only [evmS, initState]; exact hwv)
                                      hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                      hguard1 hcall1True hdec1 henough1Source hsafe1
                                  have hCreatedRet :
                                      cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                                    simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                      storageStore_createdAccounts]
                                  have hAccountsRet :
                                      accountMapEquiv
                                        (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                        (uniswapLockExitedState evm3S).accountMap := by
                                    have hs :=
                                      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                        hPostTransferAccounts3
                                    simpa [uniswapLockExitedState, uniswapUnlockedState,
                                      storageStore_accountMap, henv3] using hs
                                  exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                    hdecode hbody hCreatedRet
                                    hAccountsRet (returnEquiv.fallthrough rfl rfl (by native_decide))
                                by_cases hz3False : z3 = false
                                · have htransfer1False : callViaEVM evm2S
                                      (EVM.address
                                        (uniswapAddressAtSlot
                                          (uniswapLockEnteredState evmS) ⟨7⟩))
                                      0 safeData1 (false, evm3S, out3) := by
                                    simpa [hz3False] using htransfer1
                                  have hbody :
                                      ExecTransitionBody config contract evmS (skimStore I)
                                        skimTransition.body .reverted := by
                                    exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                      evmS evm0S evm1S evm2S evm3S I
                                      (by simp only [evmS, initState]; exact hwv)
                                      hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                      hguard1 hcall1True hdec1 henough1Source hdata1
                                      htransfer1False
                                  have rd6595False : RD uniswapV2PairBytecode I
                                      (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨6595⟩
                                      (⟨0⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                        UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                        safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                        token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      (skimSecondSafeTransferDynamicCallMem2
                                        (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                        safeValue0 out1 out2 safeValue1)
                                      (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                      (cA3, σ3) k6595b C6595b := by
                                    simpa [hz3False, safeValue1] using rd6595b
                                  by_cases hout3Empty : out3.size = 0
                                  · have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferEmptyFailureReverts_dynamic_offset
                                        rd6595False hout3Empty
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      hdecode hbody
                                  · by_cases hout3Sign : out3.size < 2 ^ 255
                                    · have rdRev :=
                                        RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts_dynamic_offset
                                          rd6595False hout3Empty hout3Sign ho32 hoSize
                                          hout1Empty hout1Sign ho32_2 hout2Size
                                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                                        hdecode hbody
                                    · have : out3.size < 2 ^ 255 := by
                                        exact lt_trans hout3Small (by norm_num)
                                      exact False.elim (hout3Sign this)
                                · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                                  have htransfer1True : callViaEVM evm2S
                                      (EVM.address
                                        (uniswapAddressAtSlot
                                          (uniswapLockEnteredState evmS) ⟨7⟩))
                                      0 safeData1 (true, evm3S, out3) := by
                                    simpa [hz3True] using htransfer1
                                  have rd6595True : RD uniswapV2PairBytecode I
                                      (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨6595⟩
                                      (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                        UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                        safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                        token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      (skimSecondSafeTransferDynamicCallMem2
                                        (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                        safeValue0 out1 out2 safeValue1)
                                      (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                      (cA3, σ3) k6595b C6595b := by
                                    simpa [hz3True, safeValue1] using rd6595b
                                  by_cases hout3Empty : out3.size = 0
                                  · have hsafe1 :
                                        ExecStmt config
                                          { contract := contract,
                                            locals :=
                                              skimSecondExcessStore evmS evm0S evm2S I
                                                balance0 balance1 } evm2S
                                          (.internalCall "_safeTransfer"
                                            [.var "_token1", .var "to", .var "excess1"] "ok1")
                                          (.ok
                                            { contract := contract,
                                              locals :=
                                                skimSecondSafeTransferStore evmS evm0S evm2S I
                                                  balance0 balance1 }
                                            evm3S) := by
                                      have hs := safeTransferInternalCallReturns_empty
                                        (caller :=
                                          { contract := contract,
                                            locals :=
                                              skimSecondExcessStore evmS evm0S evm2S I
                                                balance0 balance1 })
                                        (evm := evm2S) (evm' := evm3S)
                                        (tokenExpr := .var "_token1") (toExpr := .var "to")
                                        (valueExpr := .var "excess1") (retVar := "ok1")
                                        (token :=
                                          uniswapAddressAtSlot
                                            (uniswapLockEnteredState evmS) ⟨7⟩)
                                        (recipient := skimToAddress I)
                                        (value := skimExcess1Word evm2S balance1)
                                        (calldata := safeData1) (out := out3)
                                        rfl
                                        (evalExprs_skim_safeTransfer1_args
                                          evmS evm0S evm2S I balance0 balance1)
                                        hdata1 htransfer1True hout3Empty
                                      simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                        using hs
                                    obtain ⟨k5433, C5433, rd5433⟩ :=
                                      RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433_dynamic_offset
                                        rd6595True hout3Empty ho32 hoSize hout1Empty
                                        hout1Sign ho32_2 hout2Size
                                    exact hfinish rd5433 hsafe1
                                  · by_cases hout3Sign : out3.size < 2 ^ 255
                                    · by_cases hshort3 : out3.size < 32
                                      · have hdecSafe1 :
                                            ABI.decodeReturnValueWithMode?
                                                config.abiDecodeMode boolTy out3 =
                                              none := by
                                          change
                                            ABI.decodeReturnValueWithMode?
                                                DecodeMode.legacySolc05 boolTy out3 =
                                              none
                                          exact decodeReturnValueWithMode_legacy_bool_none_short
                                            (returndata := out3) hshort3
                                        have hbody :
                                            ExecTransitionBody config contract evmS (skimStore I)
                                              skimTransition.body .reverted := by
                                          exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                            evmS evm0S evm1S evm2S evm3S I
                                            (by simp only [evmS, initState]; exact hwv)
                                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                            hguard1 hcall1True hdec1 henough1Source hdata1
                                            htransfer1True hout3Empty hdecSafe1
                                        have rdRev :=
                                          RD.uniswapSkimSecondSafeTransferNonemptyShortReverts_dynamic_offset
                                            rd6595True hout3Empty hshort3 hout3Sign hout3Small
                                            ho32 hoSize hout1Empty hout1Sign hout1Small
                                            ho32_2 hout2Size
                                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                                          hdecode hbody
                                      · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                        let safeWord1 :=
                                          UInt256.ofNat
                                            (fromByteArrayBigEndian (out3.extract 0 32))
                                        by_cases hword1 : safeWord1 = ⟨0⟩
                                        · have hdecSafe1 :
                                              ABI.decodeReturnValueWithMode?
                                                  config.abiDecodeMode boolTy out3 =
                                                some (.bool false) := by
                                            change
                                              ABI.decodeReturnValueWithMode?
                                                  DecodeMode.legacySolc05 boolTy out3 =
                                                some (.bool false)
                                            exact decodeReturnValueWithMode_legacy_bool_false
                                              (returndata := out3) hout332 hout3Sign hword1
                                          have hbody :
                                              ExecTransitionBody config contract evmS (skimStore I)
                                                skimTransition.body .reverted := by
                                            exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                              evmS evm0S evm1S evm2S evm3S I
                                              (by simp only [evmS, initState]; exact hwv)
                                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                              hguard1 hcall1True hdec1 henough1Source hdata1
                                              htransfer1True hout3Empty hdecSafe1
                                          have rdRev :=
                                            RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts_dynamic_offset
                                              rd6595True hout3Empty hout332 hout3Sign hout3Small
                                              hword1 ho32 hoSize hout1Empty hout1Sign
                                              hout1Small ho32_2 hout2Size
                                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                                            hdecode hbody
                                        · have hdecSafe1 :
                                              ABI.decodeReturnValueWithMode?
                                                  config.abiDecodeMode boolTy out3 =
                                                some (.bool true) := by
                                            change
                                              ABI.decodeReturnValueWithMode?
                                                  DecodeMode.legacySolc05 boolTy out3 =
                                                some (.bool true)
                                            exact decodeReturnValueWithMode_legacy_bool_true
                                              (returndata := out3) hout332 hout3Sign hword1
                                          have hsafe1 :
                                              ExecStmt config
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondExcessStore evmS evm0S evm2S I
                                                      balance0 balance1 } evm2S
                                                (.internalCall "_safeTransfer"
                                                  [.var "_token1", .var "to", .var "excess1"]
                                                  "ok1")
                                                (.ok
                                                  { contract := contract,
                                                    locals :=
                                                      skimSecondSafeTransferStore evmS evm0S evm2S I
                                                        balance0 balance1 }
                                                  evm3S) := by
                                            have hs := safeTransferInternalCallReturns_decodeTrue
                                              (caller :=
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondExcessStore evmS evm0S evm2S I
                                                      balance0 balance1 })
                                              (evm := evm2S) (evm' := evm3S)
                                              (tokenExpr := .var "_token1") (toExpr := .var "to")
                                              (valueExpr := .var "excess1") (retVar := "ok1")
                                              (token :=
                                                uniswapAddressAtSlot
                                                  (uniswapLockEnteredState evmS) ⟨7⟩)
                                              (recipient := skimToAddress I)
                                              (value := skimExcess1Word evm2S balance1)
                                              (calldata := safeData1) (out := out3)
                                              rfl
                                              (evalExprs_skim_safeTransfer1_args
                                                evmS evm0S evm2S I balance0 balance1)
                                              hdata1 htransfer1True hout3Empty hdecSafe1
                                            simpa [resumeAfterInternalCall,
                                              skimSecondSafeTransferStore] using hs
                                          obtain ⟨k5433, C5433, rd5433⟩ :=
                                            RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet_dynamic_offset
                                              rd6595True hout3Empty hout332 hout3Sign
                                              hout3Small hword1 ho32 hoSize hout1Empty
                                              hout1Sign hout1Small ho32_2 hout2Size
                                              (by jump_dest)
                                          exact hfinish rd5433 hsafe1
                                    · have : out3.size < 2 ^ 255 := by
                                        exact lt_trans hout3Small (by norm_num)
                                      exact False.elim (hout3Sign this)
                  · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                    have hdecSafe0 :
                        ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                          none := by
                      change
                        ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                          none
                      exact decodeReturnValueWithMode_legacy_bool_none_huge
                        (returndata := out1) hhi
                    have hbody :
                        ExecTransitionBody config contract evmS (skimStore I)
                          skimTransition.body .reverted := by
                      exact uniswapSkimBodyReverts_firstSafeTransferDecode
                        evmS evm0S evm1S I
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                        htransferTrue hout1Empty hdecSafe0
                    have rdRev :=
                      RD.uniswapSkimSafeTransferNonemptyHugeReverts
                        rd6595True hout1Empty hhi hout1Size ho32 hoSize
                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                      hdecode hbody

      · rw [not_lt] at hdepth
        have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
        have hRuntime :
            RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
          have hsz4 : 4 ≤ I.calldata.size :=
            calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
          have hdecoded :=
            uniswapSkimX_decoded_masked
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
              (I := I) (g := Sat256.ofUInt256 g) hsz36 hsize
              (uniswapReachSkimBody
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                hcode hwv hsz4 hsize hsel)
          have hLock :=
            uniswapSkimRuntimeLockEntered
              (g := g) (toWord := skimToMaskedWord I) hperm hunlocked hdecoded
          obtain ⟨_, _, rd5257⟩ :=
            uniswapSkimRuntimeFirstBalanceOfExtcodesize
              (g := g) (toWord := skimToMaskedWord I) hLock
          obtain ⟨_, _, _, rd5272⟩ :=
            uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
              (g := g) (toWord := skimToMaskedWord I) rd5257 htoken0NoCode
          exact uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts
            rd5272 hdepth1024
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by simp only [List.length_cons, List.length_nil]; omega)
        exact uniswapSkimBodyCoreRevert_firstCallDepth
          (fun w : UInt256 => UInt256.land solcAddrMask w) hcode hwv hdepth1024
          hunlocked htoken0NoCode hdispatch
          hdecode hRuntime hAccounts

end UniswapV2Pair
