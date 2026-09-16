import Examples.UniswapV2Pair.MintBodyPrelude
import Examples.UniswapV2Pair.BalanceCallSource
import Examples.UniswapV2Pair.MintFeeFactoryCompleteCases
import Examples.UniswapV2Pair.MintSimpleFactoryCompleteCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair
set_option maxHeartbeats 3000000 in
theorem uniswapMintBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩
    · exact uniswapMintBodyRevert_locked hcode hsize hwv hsel hsz36 hlocked hdispatch
        hAccounts
    · have hunlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
          ⟨1⟩ := by
        exact not_not.mp hlocked
      have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C :=
        uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapMintX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz36 hsize hreach
      have hlockEntered := uniswapMintX_lockEntered (g := Sat256.ofUInt256 g)
        hperm hunlocked hdecoded
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hunlockedSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
        have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
        simpa [evmS, initState] using hword.symm.trans hunlocked
      by_cases htoken0NoCode :
        extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
          (UInt256.land solcAddrMask
            (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
          ⟨0⟩
      · have hguard0 :=
          mintToken0GuardFalse_initState_of_noCode
            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) hAccounts htoken0NoCode
        have hbody :
            ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
              .reverted := by
          exact uniswapMintBodyReverts_firstNoCode evmS I
            (by simp only [evmS, initState]; exact hwv)
            hunlockedSolm hguard0
        exact (uniswapMintRuntimeFirstBalanceOfMissingCodeReverts
            (g := g) hlockEntered htoken0NoCode).reEquivExecutionRevert
          hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
      · by_cases hdepth : I.depth.val < 1024
        · obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, hcont, hoSize⟩ :=
            uniswapMintRuntimeFirstBalanceOfResultBranches
              (g := g) hdepth hlockEntered htoken0NoCode
          obtain ⟨evm0S, hcallAll, hPostAccounts0, hcreated0, hσ0, hgenesis0, hblocks0,
              henv0⟩ :=
            uniswapFirstBalanceTypedCall_source
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (cA' := cA') (σ' := σ') (z := z) (o := o)
              (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
          have hguard0 :=
            mintToken0GuardTrue_initState_of_code
              (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hAccounts htoken0NoCode
          by_cases hz : z = false
          · exact (hrev hz).reEquivExecutionRevert hcode hdispatch
              (uniswapDecode_mint_ok hsz36) (by
                have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                    (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    "balanceOf" 0
                    [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                    (false, evm0S, o) false := by
                  simpa [evmS, hz] using hcallAll
                exact uniswapMintBodyReverts_firstCallFailure evmS evm0S I
                  (by simp only [evmS, initState]; exact hwv)
                  hunlockedSolm hguard0 hcall0)
          · by_cases hshort : o.size < 32
            · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
              have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                  (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                  "balanceOf" 0
                  [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                  (true, evm0S, o) false := by
                simpa [evmS, hzTrue] using hcallAll
              have hdec0 : config.externalABI.decode? "balanceOf" o = none := by
                change uniswapExternalABI.decode? "balanceOf" o = none
                simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                  (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o)
                    hshort)
              have hbody :
                  ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                    .reverted := by
                exact uniswapMintBodyReverts_firstCallDecode evmS evm0S I
                  (by simp only [evmS, initState]; exact hwv)
                  hunlockedSolm hguard0 hcall0 hdec0
              exact (hrevShort hzTrue hshort).reEquivExecutionRevert hcode hdispatch
                (uniswapDecode_mint_ok hsz36) hbody
            · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
              have ho32 : 32 ≤ o.size := not_lt.mp hshort
              let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
              have henv0I : evm0S.executionEnv = I := by
                simpa [evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
                  storageStore_executionEnv] using henv0
              have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                  (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                  "balanceOf" 0
                  [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                  (true, evm0S, o) false := by
                simpa [evmS, hzTrue] using hcallAll
              have hdec0 :
                  config.externalABI.decode? "balanceOf" o =
                    some [uniswapUint256Value balance0] := by
                simpa [balance0] using
                  uniswapBalanceOfDecode_ok (returndata := o) ho32
              obtain ⟨_, _, rd3505⟩ := hcont hzTrue ho32
              obtain ⟨_, _, rd3573⟩ :=
                uniswapMintRuntimeSecondBalanceOfExtcodesizeFromFirst rd3505 ho32 hoSize
              by_cases htoken1NoCode :
                extCodeSizeWord σ'
                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) = ⟨0⟩
              · have hbody :
                    ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                      .reverted := by
                  have hguard1 :=
                    mintToken1GuardFalse_of_noCode
                      (reserveEvm := uniswapLockEnteredState evmS)
                      (balance0 := uniswapUint256Value balance0)
                      hPostAccounts0 henv0I htoken1NoCode
                  exact uniswapMintBodyReverts_secondNoCode evmS evm0S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0 hdec0 hguard1
                exact (uniswapMintRuntimeSecondBalanceOfMissingCodeFromExtcodesize
                  rd3573 htoken1NoCode).reEquivExecutionRevert hcode hdispatch
                    (uniswapDecode_mint_ok hsz36) hbody
              · have hguard1 :=
                  mintToken1GuardTrue_of_code
                    (reserveEvm := uniswapLockEnteredState evmS)
                    (balance0 := uniswapUint256Value balance0)
                    hPostAccounts0 henv0I htoken1NoCode
                obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, hΘ1, hrev1, hrevShort1,
                    hcont1, ho1Size⟩ :=
                  uniswapMintRuntimeSecondBalanceOfResultBranchesFromExtcodesize
                    rd3573 hdepth ho32 hoSize htoken1NoCode
                obtain ⟨evm1S, hcall1All, hPostAccounts1, hcreated1, hσ01,
                    hgenesis1, hblocks1, henv1⟩ :=
                  uniswapSyncSecondBalanceTypedCall_source
                    (cA1 := cA') (gh := gh) (bl := bl) (σ1 := σ') (σ₀ := σ₀)
                    (I := I) (evm0S := evm0S) (cA2 := cA'') (σ2 := σ'')
                    (z2 := z1) (out2 := o1) (A_in2 := A_in1)
                    (callGas2 := callGas1) (o := o)
                    hPostAccounts0 hcreated0 hσ0 hgenesis0 hblocks0 henv0I hdepth
                    ho32 hoSize hΘ1
                by_cases hz1 : z1 = false
                · have hcall1 : typedCallViaEVM config evm0S
                      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                      [.address evm0S.executionEnv.codeOwner] (false, evm1S, o1) false := by
                    simpa [hz1] using hcall1All
                  have hbody :
                      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                        .reverted := by
                    exact uniswapMintBodyReverts_secondCallFailure evmS evm0S evm1S I
                      (by simp only [evmS, initState]; exact hwv)
                      hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1
                  exact (hrev1 hz1).reEquivExecutionRevert hcode hdispatch
                    (uniswapDecode_mint_ok hsz36) hbody
                · by_cases hshort1 : o1.size < 32
                  · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1
                    have hcall1 : typedCallViaEVM config evm0S
                        (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                        [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false := by
                      simpa [hz1True] using hcall1All
                    have hdec1 : config.externalABI.decode? "balanceOf" o1 = none := by
                      change uniswapExternalABI.decode? "balanceOf" o1 = none
                      simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                        (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o1)
                          hshort1)
                    have hbody :
                        ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                          .reverted := by
                      exact uniswapMintBodyReverts_secondCallDecode evmS evm0S evm1S I
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                    exact (hrevShort1 hz1True hshort1).reEquivExecutionRevert hcode hdispatch
                      (uniswapDecode_mint_ok hsz36) hbody
                  · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1
                    have ho132 : 32 ≤ o1.size := not_lt.mp hshort1
                    let balance1 := UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32))
                    have hcall1 : typedCallViaEVM config evm0S
                        (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                        [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false := by
                      simpa [hz1True] using hcall1All
                    have hdec1 :
                        config.externalABI.decode? "balanceOf" o1 =
                          some [uniswapUint256Value balance1] := by
                      simpa [balance1] using
                        uniswapBalanceOfDecode_ok (returndata := o1) ho132
                    obtain ⟨_, _, rd3630⟩ := hcont1 hz1True ho132
                    have hreserve0Eq :
                        uniswapReserve0Word (uniswapLockEnteredState evmS) =
                          reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
                      simpa [evmS] using
                        (mintReserve0Word_initState_eq_evm
                          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                          (I := I) (g := Sat256.ofUInt256 g) hAccounts)
                    have hreserve1Eq :
                        uniswapReserve1Word (uniswapLockEnteredState evmS) =
                          reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
                      simpa [evmS] using
                        (mintReserve1Word_initState_eq_evm
                          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
                          (I := I) (g := Sat256.ofUInt256 g) hAccounts)
                    by_cases hlt0 :
                      balance0.toNat <
                        (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I).toNat
                    · have hlt0Source :
                          balance0.toNat <
                            (uniswapReserve0Word (uniswapLockEnteredState evmS)).toNat := by
                        simpa [hreserve0Eq] using hlt0
                      have hbody :
                          ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                            .reverted := by
                        exact uniswapMintBodyReverts_amount0Underflow evmS evm0S evm1S I
                          (by simp only [evmS, initState]; exact hwv)
                          hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hlt0Source
                      exact (uniswapMintRuntimeAmount0SubUnderflowFromBalances
                        rd3630 hlt0 ho32 hoSize ho132 ho1Size).reEquivExecutionRevert
                          hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                    · have hle0 :
                          (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I).toNat ≤
                            balance0.toNat := by
                        omega
                      have hle0Source :
                          (uniswapReserve0Word (uniswapLockEnteredState evmS)).toNat ≤
                            balance0.toNat := by
                        simpa [hreserve0Eq] using hle0
                      obtain ⟨_, _, rd3661⟩ :=
                        uniswapMintRuntimeAmount0SubSuccessFromBalances rd3630 hle0
                      by_cases hlt1 :
                        balance1.toNat <
                          (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I).toNat
                      · have hlt1Source :
                            balance1.toNat <
                              (uniswapReserve1Word (uniswapLockEnteredState evmS)).toNat := by
                          simpa [hreserve1Eq] using hlt1
                        have hbody :
                            ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                              .reverted := by
                          exact uniswapMintBodyReverts_amount1Underflow evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
                            hle0Source hlt1Source
                        exact (uniswapMintRuntimeAmount1SubUnderflowFromAmount0
                          rd3661 hlt1 ho32 hoSize ho132 ho1Size).reEquivExecutionRevert
                            hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                      · have hle1 :
                            (reserve1Word
                              (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I).toNat ≤
                              balance1.toNat := by
                          omega
                        have hle1Source :
                            (uniswapReserve1Word (uniswapLockEnteredState evmS)).toNat ≤
                              balance1.toNat := by
                          simpa [hreserve1Eq] using hle1
                        let amount0 :=
                          UInt256.sub balance0
                            (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                        let amount1 :=
                          UInt256.sub balance1
                            (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                        obtain ⟨_, _, rd3690⟩ :=
                          uniswapMintRuntimeAmount1SubSuccessFromAmount0
                            (amount0 := amount0) rd3661 hle1
                        obtain ⟨_, _, rd7696⟩ :=
                          uniswapMintRuntimeMintFeeEntryFromAmounts rd3690
                        obtain ⟨_, _, rd7765⟩ :=
                          uniswapMintFeeRuntimeFactoryExtcodesize rd7696 ho32 hoSize ho132 ho1Size
                        have henv1I : evm1S.executionEnv = I := henv1.trans henv0I
                        by_cases hfactoryNoCode :
                          extCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) = ⟨0⟩
                        · have hfeeGuard :
                              evalExpr? config
                                (mintFeeCallFrame
                                  (uniswapReserve0Word (uniswapLockEnteredState evmS))
                                  (uniswapReserve1Word (uniswapLockEnteredState evmS)))
                                evm1S
                                (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
                                  .ok (.bool false) := by
                            exact mintFeeFactoryGuardFalse_of_noCode
                              (σ := σ'') (evm := evm1S) (I := I)
                              (reserve0 :=
                                uniswapReserve0Word (uniswapLockEnteredState evmS))
                              (reserve1 :=
                                uniswapReserve1Word (uniswapLockEnteredState evmS))
                              hPostAccounts1 henv1I hfactoryNoCode
                          have hbody :
                              ExecTransitionBody config contract evmS (mintStore I)
                                mintTransition.body .reverted := by
                            exact uniswapMintBodyReverts_mintFeeNoCode evmS evm0S evm1S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
                              hle0Source hle1Source hfeeGuard
                          exact (uniswapMintFeeRuntimeFactoryMissingCodeReverts rd7765
                              hfactoryNoCode).reEquivExecutionRevert
                            hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                        · obtain ⟨cAFee, σFee, zFee, outFee, A_inFee, callGasFee, _,
                              _, hΘFee, rd7781, houtFeeSize⟩ :=
                            uniswapMintFeeRuntimeFactoryStaticcallMade rd7765 hdepth
                              hfactoryNoCode
                          obtain ⟨evmFeeS, hfeeCallAll, hPostAccountsFee, hcreatedFee,
                              hσ0Fee, hgenesisFee, hblocksFee, henvFee⟩ :=
                            uniswapMintFeeToTypedCall_source
                              (cA1 := cA'') (gh := gh) (bl := bl) (σ1 := σ'')
                              (σ₀ := σ₀) (I := I) (evm1S := evm1S)
                              (cA2 := cAFee) (σ2 := σFee) (z2 := zFee)
                              (out2 := outFee) (A_in2 := A_inFee)
                              (callGas2 := callGasFee) (oPrev := o) (o := o1)
                              hPostAccounts1 hcreated1 hσ01 hgenesis1 hblocks1 henv1I
                              hdepth ho32 hoSize ho132 ho1Size hΘFee
                          have hfeeGuard :
                              evalExpr? config
                                (mintFeeCallFrame
                                  (uniswapReserve0Word (uniswapLockEnteredState evmS))
                                  (uniswapReserve1Word (uniswapLockEnteredState evmS)))
                                evm1S
                                (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
                                  .ok (.bool true) := by
                            exact mintFeeFactoryGuardTrue_of_code
                              (σ := σ'') (evm := evm1S) (I := I)
                              (reserve0 :=
                                uniswapReserve0Word (uniswapLockEnteredState evmS))
                              (reserve1 :=
                                uniswapReserve1Word (uniswapLockEnteredState evmS))
                              hPostAccounts1 henv1I hfactoryNoCode
                          obtain ⟨hFeeRev, hFeeRevShort, hFeeCont⟩ :=
                            uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781
                              ho32 hoSize ho132 ho1Size houtFeeSize
                          by_cases hzFee : zFee = false
                          · have hfeeCall : typedCallViaEVM config evm1S
                                (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
                                "feeTo" 0 [] (false, evmFeeS, outFee) false := by
                              simpa [hzFee] using hfeeCallAll
                            have hbody :
                                ExecTransitionBody config contract evmS (mintStore I)
                                  mintTransition.body .reverted := by
                              exact uniswapMintBodyReverts_mintFeeCallFailure
                                evmS evm0S evm1S evmFeeS I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
                                hle0Source hle1Source hfeeGuard hfeeCall
                            exact (hFeeRev hzFee).reEquivExecutionRevert
                              hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                          · by_cases houtFeeShort : outFee.size < 32
                            · have hzFeeTrue : zFee = true := Bool.eq_true_of_not_eq_false hzFee
                              have hfeeCall : typedCallViaEVM config evm1S
                                  (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
                                  "feeTo" 0 [] (true, evmFeeS, outFee) false := by
                                simpa [hzFeeTrue] using hfeeCallAll
                              have hfeeDec : config.externalABI.decode? "feeTo" outFee = none :=
                                uniswapFeeToDecode_none_short houtFeeShort
                              have hbody :
                                  ExecTransitionBody config contract evmS (mintStore I)
                                    mintTransition.body .reverted := by
                                exact uniswapMintBodyReverts_mintFeeDecode
                                  evmS evm0S evm1S evmFeeS I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1
                                  hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
                              exact (hFeeRevShort hzFeeTrue houtFeeShort).reEquivExecutionRevert
                                hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                            · have hzFeeTrue : zFee = true :=
                                Bool.eq_true_of_not_eq_false hzFee
                              have houtFee32 : 32 ≤ outFee.size := not_lt.mp houtFeeShort
                              let feeToWord : UInt256 :=
                                UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32))
                              let feeTo : AccountAddress :=
                                AccountAddress.ofNat
                                  (fromByteArrayBigEndian (outFee.extract 0 32))
                              have hfeeCall : typedCallViaEVM config evm1S
                                  (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
                                  "feeTo" 0 [] (true, evmFeeS, outFee) false := by
                                simpa [hzFeeTrue] using hfeeCallAll
                              have hfeeDec :
                                  config.externalABI.decode? "feeTo" outFee =
                                    some [.address feeTo] := by
                                simpa [feeTo] using uniswapFeeToDecode_ok houtFee32
                              have henvFeeI : evmFeeS.executionEnv = I := henvFee.trans henv1I
                              have hkLastEq :
                                  mintFeeKLastWord evmFeeS =
                                    mintFeeKLastSlotWord σFee I :=
                                mintFeeKLastWord_eq_slot_of_accountMapEquiv
                                  hPostAccountsFee henvFeeI
                              have htotalEq :
                                  mintFunctionTotalSupplyWord evmFeeS =
                                    uniswapSlotWord ⟨0⟩ σFee I :=
                                mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv
                                  hPostAccountsFee henvFeeI
                              have hamount0Eq := congrArg (balance0.sub ·) hreserve0Eq
                              have hamount1Eq := congrArg (balance1.sub ·) hreserve1Eq
                              by_cases hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩
                              · by_cases hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩
                                · exact uniswapMintFeeOnKLastNonzeroCompleteFromFactoryCases feeTo
                                    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1
                                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
                                    hfeeGuard hfeeCall hfeeDec rfl rd7781 ho32 hoSize
                                    ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
                                    hkLastEq hreserve0Eq hreserve1Eq rfl rfl
                                    (by simpa [mintAmount0Word, amount0, evmS] using hamount0Eq)
                                    (by simpa [mintAmount1Word, amount1, evmS] using hamount1Eq)
                                    hfeeToNonzero hkLastNonzero
                                    hPostAccountsFee henvFeeI hcreatedFee.symm rfl hperm
                                · exact uniswapMintFeeOnKLastZeroCompleteFromFactoryCases feeTo
                                    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1
                                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
                                    hfeeGuard hfeeCall hfeeDec rfl rd7781 ho32 hoSize
                                    ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
                                    hkLastEq htotalEq rfl hreserve0Eq hreserve1Eq rfl rfl
                                    (by simpa [mintAmount0Word, amount0, evmS] using hamount0Eq)
                                    (by simpa [mintAmount1Word, amount1, evmS] using hamount1Eq)
                                    hfeeToNonzero (not_not.mp hkLastNonzero)
                                    hPostAccountsFee henvFeeI hcreatedFee.symm rfl hperm
                              · have hfeeToZero := not_not.mp hfeeToNonzero
                                by_cases hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩
                                · exact uniswapMintFeeOffKLastNonzeroCompleteFromFactoryCases feeTo
                                    hcode hdispatch hsz36 hperm hwv hunlockedSolm hguard0 hguard1
                                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
                                    hfeeGuard hfeeCall hfeeDec rfl hPostAccountsFee henvFeeI rfl
                                    rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
                                    hkLastEq rfl hreserve0Eq hreserve1Eq rfl rfl
                                    (by simpa [mintAmount0Word, amount0, evmS] using hamount0Eq)
                                    (by simpa [mintAmount1Word, amount1, evmS] using hamount1Eq)
                                    hfeeToZero hkLastNonzero hcreatedFee.symm rfl
                                · exact uniswapMintFeeOffKLastZeroCompleteFromFactoryCases feeTo
                                    hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1
                                    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source
                                    hfeeGuard hfeeCall hfeeDec rfl rd7781 ho32 hoSize
                                    ho132 ho1Size houtFeeSize hzFeeTrue houtFee32
                                    hkLastEq htotalEq rfl hreserve0Eq hreserve1Eq rfl rfl
                                    (by simpa [mintAmount0Word, amount0, evmS] using hamount0Eq)
                                    (by simpa [mintAmount1Word, amount1, evmS] using hamount1Eq)
                                    hfeeToZero (not_not.mp hkLastNonzero)
                                    hPostAccountsFee henvFeeI hcreatedFee.symm rfl hperm
        · rw [not_lt] at hdepth
          have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
          let evmL := uniswapLockEnteredState evmS
          let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
          have hguard0 :=
            mintToken0GuardTrue_initState_of_code
              (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hAccounts htoken0NoCode
          have hdepthSolm : evmL.executionEnv.depth = 1024 := by
            simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
              storageStore_executionEnv] using hdepth1024
          have hcall0 : typedCallViaEVM config evmL target "balanceOf" 0
              [.address evmL.executionEnv.codeOwner]
              (false, { evmL with substate := (evmL.addAccessedAccount target).substate },
                ByteArray.empty) false := by
            exact callNotMade_depthLimit
              (cfg := config) (evm := evmL) (tgt := target)
              (name := "balanceOf") (args := [.address evmL.executionEnv.codeOwner])
              (callPerm := false)
              (balanceOfThisCalldataMem_encode evmL.executionEnv.codeOwner)
              hdepthSolm
          have hbody :
              ExecTransitionBody config contract evmS (mintStore I) mintTransition.body
                .reverted := by
            exact uniswapMintBodyReverts_firstCallFailure evmS
              { evmL with substate := (evmL.addAccessedAccount target).substate } I
              (by simp only [evmS, initState]; exact hwv)
              hunlockedSolm hguard0 hcall0
          have hRuntime :
              RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
            obtain ⟨_, _, _, rd3463⟩ :=
              uniswapMintRuntimeFirstBalanceOfStaticcallEntry
                (g := g) hlockEntered htoken0NoCode
            exact uniswapMintRuntimeFirstBalanceOfStaticcallDepthReverts
              rd3463 hdepth1024
              (by simp only [List.length_cons, List.length_nil]; omega)
              (by simp only [List.length_cons, List.length_nil]; omega)
          exact hRuntime.reEquivExecutionRevert hcode hdispatch
            (uniswapDecode_mint_ok hsz36) hbody
  · exact uniswapMintBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch
end UniswapV2Pair
