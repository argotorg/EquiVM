import Examples.UniswapV2Pair.MintBodyPrelude
import Examples.UniswapV2Pair.BalanceCallSource
import Examples.UniswapV2Pair.MintFeeSqrtLoopBridge
import Examples.UniswapV2Pair.MintInitialFactoryCases
import Examples.UniswapV2Pair.MintInitialProductOverflow
import Examples.UniswapV2Pair.MintLiquidityZeroFactoryCases
import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroFactoryCases
import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroInitialFactoryCases
import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroRevertCases
import Examples.UniswapV2Pair.MintProportionalProductOverflow
import Examples.UniswapV2Pair.MintProportionalSecondMintFactoryCases
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
                              by_cases hsmallInitial :
                                  UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                      uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
                                          amount0.toNat * amount1.toNat < UInt256.size ∧
                                            (UInt256.mul amount0 amount1).toNat ≤ 3
                              · exact
                                  uniswapMintInitialSmallRootRevertsFromFactoryCases
                                    feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0
                                    hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
                                    hle1Source hfeeGuard hfeeCall hfeeDec (by simp [feeTo])
                                    hPostAccountsFee henvFeeI hperm rd7781 ho32 hoSize ho132
                                    ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq htotalEq
                                    (by
                                      simpa [mintAmount0Word, amount0, evmS] using
                                        congrArg (fun w => balance0.sub w) hreserve0Eq)
                                    (by
                                      simpa [mintAmount1Word, amount1, evmS] using
                                        congrArg (fun w => balance1.sub w) hreserve1Eq)
                                    (Or.inl (by simpa [feeToWord] using hsmallInitial))
                              · by_cases hsmallInitialFeeOn :
                                  UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                    mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                      uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩ ∧
                                        amount0.toNat * amount1.toNat < UInt256.size ∧
                                          (UInt256.mul amount0 amount1).toNat ≤ 3
                                · exact
                                    uniswapMintInitialSmallRootRevertsFromFactoryCases
                                      feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0
                                      hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
                                      hle1Source hfeeGuard hfeeCall hfeeDec (by simp [feeTo])
                                      hPostAccountsFee henvFeeI hperm rd7781 ho32 hoSize
                                      ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 hkLastEq
                                      htotalEq
                                      (by
                                        simpa [mintAmount0Word, amount0, evmS] using
                                          congrArg (fun w => balance0.sub w) hreserve0Eq)
                                      (by
                                        simpa [mintAmount1Word, amount1, evmS] using
                                          congrArg (fun w => balance1.sub w) hreserve1Eq)
                                      (Or.inr
                                        (Or.inl
                                          (by simpa [feeToWord] using hsmallInitialFeeOn)))
                                · by_cases hsmallInitialFeeOffCleared :
                                    UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                      mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                        uniswapSlotWord ⟨0⟩
                                            (sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩)
                                            I =
                                          ⟨0⟩ ∧
                                          amount0.toNat * amount1.toNat < UInt256.size ∧
                                            (UInt256.mul amount0 amount1).toNat ≤ 3
                                  · exact
                                      uniswapMintInitialSmallRootRevertsFromFactoryCases
                                        feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0
                                        hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source
                                        hle1Source hfeeGuard hfeeCall hfeeDec
                                        (by simp [feeTo]) hPostAccountsFee henvFeeI hperm
                                        rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                        hzFeeTrue houtFee32 hkLastEq htotalEq
                                        (by
                                          simpa [mintAmount0Word, amount0, evmS] using
                                            congrArg (fun w => balance0.sub w) hreserve0Eq)
                                        (by
                                          simpa [mintAmount1Word, amount1, evmS] using
                                            congrArg (fun w => balance1.sub w) hreserve1Eq)
                                        (Or.inr
                                          (Or.inr
                                            (by simpa [feeToWord] using
                                              hsmallInitialFeeOffCleared)))
                                  · let memFee :=
                                      feeToStaticcallMem
                                        (balanceOfThisRebuiltStaticcallMem
                                          (UInt256.ofNat I.codeOwner.val) o o1)
                                        outFee
                                    let totalSupply := uniswapSlotWord ⟨0⟩ σFee I
                                    let reserve0 :=
                                      reserve0Word
                                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                                    let reserve1 :=
                                      reserve1Word
                                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                                    let liquidity :=
                                      minFunctionResultWord
                                        (UInt256.div (UInt256.mul amount0 totalSupply)
                                          reserve0)
                                        (UInt256.div (UInt256.mul amount1 totalSupply)
                                          reserve1)
                                    let σAfterMint :=
                                      sstoreAccountMap I.codeOwner
                                        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                          (totalSupply + liquidity))
                                        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
                                          (uniswapInternalMintBalanceHashMem (mintToMaskedWord I)
                                            memFee))
                                        (uniswapCodeOwnerStorageWord I
                                          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                            (totalSupply + liquidity))
                                          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
                                            memFee) + liquidity)
                                    by_cases hproportionalFeeOffKLastZero :
                                        UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                          mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                          totalSupply ≠ ⟨0⟩ ∧
                                          amount0.toNat * totalSupply.toNat < UInt256.size ∧
                                          amount1.toNat * totalSupply.toNat < UInt256.size ∧
                                          reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                          liquidity ≠ ⟨0⟩ ∧
                                          totalSupply.toNat + liquidity.toNat < UInt256.size ∧
                                          (uniswapCodeOwnerStorageWord I
                                            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                              (totalSupply + liquidity))
                                            (uniswapInternalMintBalanceHashSlot
                                              (mintToMaskedWord I) memFee)).toNat +
                                              liquidity.toNat <
                                            UInt256.size ∧
                                          mintFunctionToBalanceNewNat evmFeeS
                                              (AccountAddress.ofNat (mintToWord I).toNat)
                                              liquidity <
                                            UInt256.size ∧
                                          balance0.toNat ≤ reserve112Mask.toNat ∧
                                          balance1.toNat ≤ reserve112Mask.toNat ∧
                                          UInt256.land
                                              (uniswapUpdateElapsedWord
                                                (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
                                              reserve32Mask =
                                            ⟨0⟩ ∧
                                          syncTimeElapsedInt
                                              (mintFunctionPostState evmFeeS
                                                (AccountAddress.ofNat (mintToWord I).toNat)
                                                liquidity) =
                                            0
                                    · rcases hproportionalFeeOffKLastZero with
                                        ⟨hfeeToZero, hkLastZero, htotalNonzero, hmulFit0,
                                          hmulFit1, hreserve0Nonzero, hreserve1Nonzero,
                                          hliqNonzero, htotalFit, hbalanceFit,
                                          hbalanceFitSource, hbound0, hbound1, helapsed0,
                                          helapsedSource⟩
                                      have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
                                        exact
                                          accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
                                            (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                            hfeeToZero
                                      have hkLastSource :
                                          (mintFeeKLastWord evmFeeS).toNat = 0 := by
                                        rw [hkLastEq, hkLastZero]
                                        rfl
                                      have htotalSourceNonzero :
                                          mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
                                        intro hzero
                                        apply htotalNonzero
                                        simpa [totalSupply] using htotalEq.symm.trans hzero
                                      have hfitSource0 :
                                          mintAmountProductNat
                                              (mintAmount0Word (uniswapLockEnteredState evmS)
                                                balance0)
                                              (mintFunctionTotalSupplyWord evmFeeS) <
                                            UInt256.size := by
                                        simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                          totalSupply, hreserve0Eq, htotalEq] using hmulFit0
                                      have hfitSource1 :
                                          mintAmountProductNat
                                              (mintAmount1Word (uniswapLockEnteredState evmS)
                                                balance1)
                                              (mintFunctionTotalSupplyWord evmFeeS) <
                                            UInt256.size := by
                                        simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                          totalSupply, hreserve1Eq, htotalEq] using hmulFit1
                                      have hreserve0Source :
                                          uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                            ⟨0⟩ := by
                                        intro hzero
                                        apply hreserve0Nonzero
                                        simpa [reserve0, hreserve0Eq] using hzero
                                      have hreserve1Source :
                                          uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                            ⟨0⟩ := by
                                        intro hzero
                                        apply hreserve1Nonzero
                                        simpa [reserve1, hreserve1Eq] using hzero
                                      have hprod0 :
                                          mintAmountProductWord amount0 totalSupply =
                                            UInt256.mul amount0 totalSupply :=
                                        mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
                                      have hprod1 :
                                          mintAmountProductWord amount1 totalSupply =
                                            UInt256.mul amount1 totalSupply :=
                                        mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
                                      have hliquiditySource :
                                          liquidity =
                                            minFunctionResultWord
                                              (mintProportionalLiquidityWord
                                                (mintAmount0Word (uniswapLockEnteredState evmS)
                                                  balance0)
                                                (mintFunctionTotalSupplyWord evmFeeS)
                                                (uniswapReserve0Word
                                                  (uniswapLockEnteredState evmS)))
                                              (mintProportionalLiquidityWord
                                                (mintAmount1Word (uniswapLockEnteredState evmS)
                                                  balance1)
                                                (mintFunctionTotalSupplyWord evmFeeS)
                                                  (uniswapReserve1Word
                                                    (uniswapLockEnteredState evmS))) := by
                                        rw [show
                                            mintAmount0Word (uniswapLockEnteredState evmS)
                                                balance0 =
                                              amount0 by
                                            simp [mintAmount0Word, amount0, hreserve0Eq]]
                                        rw [show
                                            mintAmount1Word (uniswapLockEnteredState evmS)
                                                balance1 =
                                              amount1 by
                                            simp [mintAmount1Word, amount1, hreserve1Eq]]
                                        rw [show mintFunctionTotalSupplyWord evmFeeS =
                                            totalSupply by simpa [totalSupply] using htotalEq]
                                        rw [show
                                            uniswapReserve0Word (uniswapLockEnteredState evmS) =
                                              reserve0 by
                                            simpa [reserve0] using hreserve0Eq]
                                        rw [show
                                            uniswapReserve1Word (uniswapLockEnteredState evmS) =
                                              reserve1 by
                                            simpa [reserve1] using hreserve1Eq]
                                        simp [liquidity, mintProportionalLiquidityWord, hprod0,
                                          hprod1]
                                      have hfitSupplySource :
                                          mintFunctionTotalSupplyNewNat evmFeeS liquidity <
                                            UInt256.size := by
                                        simpa [mintFunctionTotalSupplyNewNat, totalSupply,
                                          htotalEq] using htotalFit
                                      obtain ⟨_, _, rd3701⟩ :=
                                        uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
                                          rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                          hzFeeTrue houtFee32 hfeeToZero hkLastZero
                                      have hmem :
                                          memFee.size = 164 :=
                                        feeToStaticcallMem_size_of_size_ge
                                          (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                          ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                      have hmem64 :
                                          memFee.readWithPadding 64 32 =
                                            UInt256.toByteArray ⟨128⟩ :=
                                        feeToStaticcallMem_read64_of_size_ge
                                          (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                          ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                      have hclean0 :
                                          UInt256.land reserve0 reserve112Mask = reserve0 := by
                                        exact reserve112Mask_clean_of_lt _ (by
                                          dsimp [reserve0, reserve0Word]
                                          exact reserve112Word_lt _)
                                      have hclean1 :
                                          UInt256.land reserve1 reserve112Mask = reserve1 := by
                                        exact reserve112Mask_clean_of_lt _ (by
                                          dsimp [reserve1, reserve1Word]
                                          exact reserve112Word_lt _)
                                      have hbound0Source :
                                          Int.ofNat balance0.toNat ≤ maxUint112 := by
                                        have hmask :
                                            reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                          native_decide
                                        have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                          simpa [hmask] using hbound0
                                        norm_num [maxUint112]
                                        exact_mod_cast hnat
                                      have hbound1Source :
                                          Int.ofNat balance1.toNat ≤ maxUint112 := by
                                        have hmask :
                                            reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                          native_decide
                                        have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                          simpa [hmask] using hbound1
                                        norm_num [maxUint112]
                                        exact_mod_cast hnat
                                      have hbody :
                                          ExecTransitionBody config contract evmS (mintStore I)
                                            mintTransition.body
                                            (.returned
                                              (let evmL := uniswapLockEnteredState evmS
                                               let recipient :=
                                                AccountAddress.ofNat (mintToWord I).toNat
                                               let amount0 := mintAmount0Word evmL balance0
                                               let amount1 := mintAmount1Word evmL balance1
                                               let totalSupply :=
                                                mintFunctionTotalSupplyWord evmFeeS
                                               let reserve0 := uniswapReserve0Word evmL
                                               let reserve1 := uniswapReserve1Word evmL
                                               let nextFrame :=
                                               resumeAfterInternalCall
                                                  { contract := contract,
                                                    locals :=
                                                      mintAmountStore evmL I balance0 balance1 }
                                                  "feeOn" (some [.bool false])
                                               let afterTotalSupplyLocals :=
                                                nextFrame.locals.insert "_totalSupply"
                                                  (uniswapUint256Value totalSupply)
                                               let liquidity0 :=
                                                mintProportionalLiquidityWord amount0 totalSupply
                                                  reserve0
                                               let liquidity1 :=
                                                mintProportionalLiquidityWord amount1 totalSupply
                                                  reserve1
                                               let afterBranch :=
                                                resumeAfterInternalCall
                                                  { contract := contract,
                                                    locals :=
                                                      (afterTotalSupplyLocals.insert "liquidity0"
                                                        (mintProportionalLiquidityValue amount0
                                                          totalSupply reserve0)).insert
                                                          "liquidity1"
                                                          (mintProportionalLiquidityValue amount1
                                                            totalSupply reserve1) }
                                                  "liquidity"
                                                  (some
                                                    [minFunctionResultValue liquidity0 liquidity1])
                                               let afterMint :=
                                                resumeAfterInternalCall afterBranch "_mintResult"
                                                  none
                                               resumeAfterInternalCall afterMint "_updateResult"
                                                none)
                                              (uniswapLockExitedState
                                                (syncUpdatePackedReserveState
                                                  (mintFunctionPostState evmFeeS
                                                    (AccountAddress.ofNat (mintToWord I).toNat)
                                                    liquidity)
                                                  balance0 balance1))
                                              (some [uniswapUint256Value liquidity])) := by
                                        exact ExecFuncBody.execBlockRet
                                          (uniswapMintProportionalFeeOffReturn_kLastZero
                                            evmS evm0S evm1S evmFeeS I feeTo
                                            (by simp only [evmS, initState]; exact hwv)
                                            hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1
                                            hdec1 hle0Source hle1Source hfeeGuard hfeeCall
                                            hfeeDec hfeeToAddr hkLastSource htotalSourceNonzero
                                            hfitSource0 hfitSource1 hreserve0Source
                                            hreserve1Source hliquiditySource hliqNonzero
                                            hfitSupplySource hbalanceFitSource hbound0Source
                                            hbound1Source helapsedSource)
                                      have hMintAccounts :
                                          accountMapEquiv σAfterMint
                                            (mintFunctionPostState evmFeeS
                                              (AccountAddress.ofNat (mintToWord I).toNat)
                                              liquidity).accountMap := by
                                        exact
                                          accountMapEquiv_mintFunctionPostState_of_runtimeMint
                                            hPostAccountsFee henvFeeI (by dsimp [memFee]; rw [hmem]; omega)
                                            hfitSupplySource hbalanceFitSource
                                      have henvMint :
                                          (mintFunctionPostState evmFeeS
                                            (AccountAddress.ofNat (mintToWord I).toNat)
                                            liquidity).executionEnv = I := by
                                        simp [mintFunctionPostState,
                                          mintFunctionAfterTotalSupplyState, henvFeeI,
                                          storageStore_executionEnv]
                                      have hslot8 :
                                          Solm.EVM.storageLoad
                                              (mintFunctionPostState evmFeeS
                                                (AccountAddress.ofNat (mintToWord I).toNat)
                                                liquidity)
                                              (mintFunctionPostState evmFeeS
                                                (AccountAddress.ofNat (mintToWord I).toNat)
                                                liquidity).executionEnv.codeOwner
                                              ⟨8⟩ =
                                            uniswapSlotWord ⟨8⟩ σAfterMint I := by
                                        have hword := accountMapEquiv_storage_findD hMintAccounts
                                          I.codeOwner ⟨8⟩ ⟨0⟩
                                        simpa [uniswapSlotWord, Solm.EVM.storageLoad,
                                          State.lookupAccount, Account.lookupStorage, henvMint]
                                          using hword.symm
                                      let packed :=
                                        uniswapUpdatePackedReserveWord
                                          (uniswapSlotWord ⟨8⟩ σAfterMint I)
                                          (uniswapUpdateTimestampWord I) balance1 balance0
                                      let σPacked :=
                                        sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
                                      have hPackedAccounts :
                                          accountMapEquiv σPacked
                                            (syncUpdatePackedReserveState
                                              (mintFunctionPostState evmFeeS
                                                (AccountAddress.ofNat (mintToWord I).toNat)
                                                liquidity)
                                              balance0 balance1).accountMap := by
                                        exact accountMapEquiv_syncUpdatePackedReserveState
                                          hMintAccounts henvMint hslot8 rfl
                                      have hAccountsRet :
                                          accountMapEquiv
                                            (sstoreAccountMap I.codeOwner σPacked ⟨12⟩
                                              (⟨1⟩ : UInt256))
                                            (uniswapLockExitedState
                                              (syncUpdatePackedReserveState
                                                (mintFunctionPostState evmFeeS
                                                  (AccountAddress.ofNat (mintToWord I).toNat)
                                                  liquidity)
                                                balance0 balance1)).accountMap := by
                                        have hs := accountMapEquiv_sstoreAccountMap I.codeOwner
                                          ⟨12⟩ ⟨1⟩ hPackedAccounts
                                        simpa [uniswapLockExitedState, uniswapUnlockedState,
                                          storageStore_accountMap, storageStore_executionEnv,
                                          syncUpdatePackedReserveState, henvMint] using hs
                                      have hCreatedRet :
                                          cAFee =
                                            (uniswapLockExitedState
                                              (syncUpdatePackedReserveState
                                                (mintFunctionPostState evmFeeS
                                                  (AccountAddress.ofNat (mintToWord I).toNat)
                                                  liquidity)
                                                balance0 balance1)).createdAccounts := by
                                        simp [uniswapLockExitedState, uniswapUnlockedState,
                                          syncUpdatePackedReserveState, mintFunctionPostState,
                                          mintFunctionAfterTotalSupplyState,
                                          storageStore_createdAccounts, hcreatedFee]
                                      have rdRet :
                                          RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
                                            (initState cA gh bl σ_evm σ₀
                                              (Sat256.ofUInt256 g) A I)
                                            (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩
                                              (⟨1⟩ : UInt256))
                                            (UInt256.toByteArray liquidity) := by
                                        simpa [memFee, totalSupply, reserve0, reserve1,
                                          liquidity, σAfterMint, packed, σPacked] using
                                          uniswapMintRuntimeAfterMintFeeProportionalFeeOffReturns
                                            (liquidity := liquidity) rd3701 rfl htotalNonzero
                                            hclean0 hclean1 hmulFit0 hmulFit1
                                            hreserve0Nonzero hreserve1Nonzero rfl hliqNonzero
                                            hperm htotalFit hbalanceFit hbound0 hbound1
                                            helapsed0 rfl hmem hmem64
                                      exact rdRet.reEquivExecutionGenAccountMapEquiv
                                        hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                                        hCreatedRet hAccountsRet
                                        (returnEquiv_of_encode
                                          (by simpa [uint256] using
                                            uint256ReturnEncoding liquidity))
                                    · by_cases hproportionalFeeOffKLastZeroCumulative :
                                        UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                          mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                          totalSupply ≠ ⟨0⟩ ∧
                                          amount0.toNat * totalSupply.toNat < UInt256.size ∧
                                          amount1.toNat * totalSupply.toNat < UInt256.size ∧
                                          reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                          liquidity ≠ ⟨0⟩ ∧
                                          totalSupply.toNat + liquidity.toNat < UInt256.size ∧
                                          (uniswapCodeOwnerStorageWord I
                                            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                              (totalSupply + liquidity))
                                            (uniswapInternalMintBalanceHashSlot
                                              (mintToMaskedWord I) memFee)).toNat +
                                              liquidity.toNat <
                                            UInt256.size ∧
                                          mintFunctionToBalanceNewNat evmFeeS
                                              (AccountAddress.ofNat (mintToWord I).toNat)
                                              liquidity <
                                            UInt256.size ∧
                                          balance0.toNat ≤ reserve112Mask.toNat ∧
                                          balance1.toNat ≤ reserve112Mask.toNat ∧
                                          UInt256.land
                                              (uniswapUpdateElapsedWord
                                                (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
                                              reserve32Mask ≠
                                            ⟨0⟩ ∧
                                          0 <
                                            syncTimeElapsedInt
                                              (mintFunctionPostState evmFeeS
                                                (AccountAddress.ofNat (mintToWord I).toNat)
                                                liquidity)
                                      · rcases hproportionalFeeOffKLastZeroCumulative with
                                          ⟨hfeeToZero, hkLastZero, htotalNonzero,
                                            hmulFit0, hmulFit1, hreserve0Nonzero,
                                            hreserve1Nonzero, hliqNonzero, htotalFit,
                                            hbalanceFit, hbalanceFitSource, hbound0, hbound1,
                                            helapsedNe, helapsedSource⟩
                                        have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
                                          exact
                                            accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
                                              (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                              hfeeToZero
                                        have hkLastSource :
                                            (mintFeeKLastWord evmFeeS).toNat = 0 := by
                                          rw [hkLastEq, hkLastZero]
                                          rfl
                                        have htotalSourceNonzero :
                                            mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
                                          intro hzero
                                          apply htotalNonzero
                                          simpa [totalSupply] using htotalEq.symm.trans hzero
                                        have hfitSource0 :
                                            mintAmountProductNat
                                                (mintAmount0Word (uniswapLockEnteredState evmS)
                                                  balance0)
                                                (mintFunctionTotalSupplyWord evmFeeS) <
                                              UInt256.size := by
                                          simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                            totalSupply, hreserve0Eq, htotalEq] using hmulFit0
                                        have hfitSource1 :
                                            mintAmountProductNat
                                                (mintAmount1Word (uniswapLockEnteredState evmS)
                                                  balance1)
                                                (mintFunctionTotalSupplyWord evmFeeS) <
                                              UInt256.size := by
                                          simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                            totalSupply, hreserve1Eq, htotalEq] using hmulFit1
                                        have hreserve0Source :
                                            uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                              ⟨0⟩ := by
                                          intro hzero
                                          apply hreserve0Nonzero
                                          simpa [reserve0, hreserve0Eq] using hzero
                                        have hreserve1Source :
                                            uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                              ⟨0⟩ := by
                                          intro hzero
                                          apply hreserve1Nonzero
                                          simpa [reserve1, hreserve1Eq] using hzero
                                        have hprod0 :
                                            mintAmountProductWord amount0 totalSupply =
                                              UInt256.mul amount0 totalSupply :=
                                          mintAmountProductWord_eq_mul amount0 totalSupply
                                            hmulFit0
                                        have hprod1 :
                                            mintAmountProductWord amount1 totalSupply =
                                              UInt256.mul amount1 totalSupply :=
                                          mintAmountProductWord_eq_mul amount1 totalSupply
                                            hmulFit1
                                        have hliquiditySource :
                                            liquidity =
                                              minFunctionResultWord
                                                (mintProportionalLiquidityWord
                                                  (mintAmount0Word (uniswapLockEnteredState evmS)
                                                    balance0)
                                                  (mintFunctionTotalSupplyWord evmFeeS)
                                                  (uniswapReserve0Word
                                                    (uniswapLockEnteredState evmS)))
                                                (mintProportionalLiquidityWord
                                                  (mintAmount1Word (uniswapLockEnteredState evmS)
                                                    balance1)
                                                  (mintFunctionTotalSupplyWord evmFeeS)
                                                    (uniswapReserve1Word
                                                      (uniswapLockEnteredState evmS))) := by
                                          rw [show
                                              mintAmount0Word (uniswapLockEnteredState evmS)
                                                  balance0 =
                                                amount0 by
                                              simp [mintAmount0Word, amount0, hreserve0Eq]]
                                          rw [show
                                              mintAmount1Word (uniswapLockEnteredState evmS)
                                                  balance1 =
                                                amount1 by
                                              simp [mintAmount1Word, amount1, hreserve1Eq]]
                                          rw [show mintFunctionTotalSupplyWord evmFeeS =
                                              totalSupply by simpa [totalSupply] using htotalEq]
                                          rw [show
                                              uniswapReserve0Word (uniswapLockEnteredState evmS) =
                                                reserve0 by
                                              simpa [reserve0] using hreserve0Eq]
                                          rw [show
                                              uniswapReserve1Word (uniswapLockEnteredState evmS) =
                                                reserve1 by
                                              simpa [reserve1] using hreserve1Eq]
                                          simp [liquidity, mintProportionalLiquidityWord, hprod0,
                                            hprod1]
                                        have hfitSupplySource :
                                            mintFunctionTotalSupplyNewNat evmFeeS liquidity <
                                              UInt256.size := by
                                          simpa [mintFunctionTotalSupplyNewNat, totalSupply,
                                            htotalEq] using htotalFit
                                        obtain ⟨_, _, rd3701⟩ :=
                                          uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
                                            rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                            hzFeeTrue houtFee32 hfeeToZero hkLastZero
                                        have hmem :
                                            memFee.size = 164 :=
                                          feeToStaticcallMem_size_of_size_ge
                                            (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                            ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                        have hmem64 :
                                            memFee.readWithPadding 64 32 =
                                              UInt256.toByteArray ⟨128⟩ :=
                                          feeToStaticcallMem_read64_of_size_ge
                                            (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                            ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                        have hclean0 :
                                            UInt256.land reserve0 reserve112Mask = reserve0 := by
                                          exact reserve112Mask_clean_of_lt _ (by
                                            dsimp [reserve0, reserve0Word]
                                            exact reserve112Word_lt _)
                                        have hclean1 :
                                            UInt256.land reserve1 reserve112Mask = reserve1 := by
                                          exact reserve112Mask_clean_of_lt _ (by
                                            dsimp [reserve1, reserve1Word]
                                            exact reserve112Word_lt _)
                                        have hbound0Source :
                                            Int.ofNat balance0.toNat ≤ maxUint112 := by
                                          have hmask :
                                              reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                            native_decide
                                          have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                            simpa [hmask] using hbound0
                                          norm_num [maxUint112]
                                          exact_mod_cast hnat
                                        have hbound1Source :
                                            Int.ofNat balance1.toNat ≤ maxUint112 := by
                                          have hmask :
                                              reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                            native_decide
                                          have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                            simpa [hmask] using hbound1
                                          norm_num [maxUint112]
                                          exact_mod_cast hnat
                                        have hbody :=
                                          ExecFuncBody.execBlockRet
                                            (uniswapMintProportionalFeeOffCumulativeReturn_kLastZero
                                              evmS evm0S evm1S evmFeeS I feeTo
                                              (by simp only [evmS, initState]; exact hwv)
                                              hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                              hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                              hfeeCall hfeeDec hfeeToAddr hkLastSource
                                              htotalSourceNonzero hfitSource0 hfitSource1
                                              hreserve0Source hreserve1Source hliquiditySource
                                              hliqNonzero hfitSupplySource hbalanceFitSource
                                              hbound0Source hbound1Source helapsedSource)
                                        exact
                                          uniswapMintFinishProportionalFeeOffCumulative
                                            hcode hdispatch hsz36
                                            (by simpa [hreserve0Eq, hreserve1Eq] using hbody)
                                            rd3701 hPostAccountsFee henvFeeI hcreatedFee
                                            (by rfl) htotalNonzero hclean0 hclean1 hmulFit0
                                            hmulFit1 hreserve0Nonzero hreserve1Nonzero
                                            (by rfl) hliqNonzero hperm htotalFit
                                            hbalanceFit hfitSupplySource hbalanceFitSource
                                            hbound0 hbound1 helapsedNe (by rfl) hmem hmem64
                                      · let packed :=
                                        uniswapUpdatePackedReserveWord
                                          (uniswapSlotWord ⟨8⟩ σAfterMint I)
                                          (uniswapUpdateTimestampWord I) balance1 balance0
                                        let σPacked :=
                                          sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
                                        let kLastWord :=
                                          UInt256.mul
                                            (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I)
                                              reserve112Mask)
                                            (UInt256.land
                                              (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I)
                                                reserve112Shift)
                                              reserve112Mask)
                                        let postMint :=
                                          mintFunctionPostState evmFeeS
                                            (AccountAddress.ofNat (mintToWord I).toNat)
                                            liquidity
                                        let syncState := syncUpdatePackedReserveState postMint balance0 balance1
                                        let σCumulativeWith :=
                                          uniswapUpdateCumulativePackedMapWith σAfterMint I balance0
                                            balance1 reserve0 reserve1
                                        let syncCumulativeStateWith :=
                                          syncUpdateCumulativePackedReserveStateWith postMint balance0
                                            balance1 reserve0 reserve1
                                        by_cases hproportionalFeeOnKLastZero :
                                            UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                              mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                              totalSupply ≠ ⟨0⟩ ∧
                                              amount0.toNat * totalSupply.toNat < UInt256.size ∧
                                              amount1.toNat * totalSupply.toNat < UInt256.size ∧
                                              reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                              liquidity ≠ ⟨0⟩ ∧
                                              totalSupply.toNat + liquidity.toNat < UInt256.size ∧
                                              (uniswapCodeOwnerStorageWord I
                                                (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                                  (totalSupply + liquidity))
                                                (uniswapInternalMintBalanceHashSlot
                                                  (mintToMaskedWord I) memFee)).toNat +
                                                  liquidity.toNat <
                                                UInt256.size ∧
                                              mintFunctionToBalanceNewNat evmFeeS
                                                  (AccountAddress.ofNat (mintToWord I).toNat)
                                                  liquidity <
                                                UInt256.size ∧
                                              balance0.toNat ≤ reserve112Mask.toNat ∧
                                              balance1.toNat ≤ reserve112Mask.toNat ∧
                                              UInt256.land
                                                  (uniswapUpdateElapsedWord
                                                    (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
                                                  reserve32Mask =
                                                ⟨0⟩ ∧
                                              (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I)
                                                    reserve112Mask).toNat *
                                                  (UInt256.land
                                                    (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I)
                                                      reserve112Shift)
                                                    reserve112Mask).toNat <
                                                UInt256.size ∧
                                              syncTimeElapsedInt postMint = 0 ∧
                                              mintFeeReserveProductNat
                                                  (uniswapReserve0Word syncState)
                                                  (uniswapReserve1Word syncState) <
                                                UInt256.size
                                        · rcases hproportionalFeeOnKLastZero with
                                            ⟨hfeeToNonzero, hkLastZero, htotalNonzero,
                                              hmulFit0, hmulFit1, hreserve0Nonzero,
                                              hreserve1Nonzero, hliqNonzero, htotalFit,
                                              hbalanceFit, hbalanceFitSource, hbound0, hbound1,
                                              helapsed0, hfitKLastRuntime, helapsedSource,
                                              hfitKLastSource⟩
                                          have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
                                            exact
                                              accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
                                                (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                                hfeeToNonzero
                                          have hkLastSource :
                                              (mintFeeKLastWord evmFeeS).toNat = 0 := by
                                            rw [hkLastEq, hkLastZero]
                                            rfl
                                          have htotalSourceNonzero :
                                              mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
                                            intro hzero
                                            apply htotalNonzero
                                            simpa [totalSupply] using htotalEq.symm.trans hzero
                                          have hfitSource0 :
                                              mintAmountProductNat
                                                  (mintAmount0Word (uniswapLockEnteredState evmS)
                                                    balance0)
                                                  (mintFunctionTotalSupplyWord evmFeeS) <
                                                UInt256.size := by
                                            simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                              totalSupply, hreserve0Eq, htotalEq] using hmulFit0
                                          have hfitSource1 :
                                              mintAmountProductNat
                                                  (mintAmount1Word (uniswapLockEnteredState evmS)
                                                    balance1)
                                                  (mintFunctionTotalSupplyWord evmFeeS) <
                                                UInt256.size := by
                                            simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                              totalSupply, hreserve1Eq, htotalEq] using hmulFit1
                                          have hreserve0Source :
                                              uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                                ⟨0⟩ := by
                                            intro hzero
                                            apply hreserve0Nonzero
                                            simpa [reserve0, hreserve0Eq] using hzero
                                          have hreserve1Source :
                                              uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                                ⟨0⟩ := by
                                            intro hzero
                                            apply hreserve1Nonzero
                                            simpa [reserve1, hreserve1Eq] using hzero
                                          have hprod0 :
                                              mintAmountProductWord amount0 totalSupply =
                                                UInt256.mul amount0 totalSupply :=
                                            mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
                                          have hprod1 :
                                              mintAmountProductWord amount1 totalSupply =
                                                UInt256.mul amount1 totalSupply :=
                                            mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
                                          have hliquiditySource :
                                              liquidity =
                                                minFunctionResultWord
                                                  (mintProportionalLiquidityWord
                                                    (mintAmount0Word
                                                      (uniswapLockEnteredState evmS) balance0)
                                                    (mintFunctionTotalSupplyWord evmFeeS)
                                                    (uniswapReserve0Word
                                                      (uniswapLockEnteredState evmS)))
                                                  (mintProportionalLiquidityWord
                                                    (mintAmount1Word
                                                      (uniswapLockEnteredState evmS) balance1)
                                                    (mintFunctionTotalSupplyWord evmFeeS)
                                                    (uniswapReserve1Word
                                                      (uniswapLockEnteredState evmS))) := by
                                            rw [show
                                                mintAmount0Word (uniswapLockEnteredState evmS)
                                                    balance0 =
                                                  amount0 by
                                                simp [mintAmount0Word, amount0, hreserve0Eq]]
                                            rw [show
                                                mintAmount1Word (uniswapLockEnteredState evmS)
                                                    balance1 =
                                                  amount1 by
                                                simp [mintAmount1Word, amount1, hreserve1Eq]]
                                            rw [show mintFunctionTotalSupplyWord evmFeeS =
                                                totalSupply by simpa [totalSupply] using htotalEq]
                                            rw [show
                                                uniswapReserve0Word (uniswapLockEnteredState evmS) =
                                                  reserve0 by
                                                simpa [reserve0] using hreserve0Eq]
                                            rw [show
                                                uniswapReserve1Word (uniswapLockEnteredState evmS) =
                                                  reserve1 by
                                                simpa [reserve1] using hreserve1Eq]
                                            simp [liquidity, mintProportionalLiquidityWord, hprod0,
                                              hprod1]
                                          have hfitSupplySource :
                                              mintFunctionTotalSupplyNewNat evmFeeS liquidity <
                                                UInt256.size := by
                                            simpa [mintFunctionTotalSupplyNewNat, totalSupply,
                                              htotalEq] using htotalFit
                                          obtain ⟨_, _, rd3701⟩ :=
                                            uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
                                              rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                              hzFeeTrue houtFee32 hfeeToNonzero hkLastZero
                                          have hmem :
                                              memFee.size = 164 :=
                                            feeToStaticcallMem_size_of_size_ge
                                              (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                              ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                          have hmem64 :
                                              memFee.readWithPadding 64 32 =
                                                UInt256.toByteArray ⟨128⟩ :=
                                            feeToStaticcallMem_read64_of_size_ge
                                              (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                              ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                          have hclean0 :
                                              UInt256.land reserve0 reserve112Mask = reserve0 := by
                                            exact reserve112Mask_clean_of_lt _ (by
                                              dsimp [reserve0, reserve0Word]
                                              exact reserve112Word_lt _)
                                          have hclean1 :
                                              UInt256.land reserve1 reserve112Mask = reserve1 := by
                                            exact reserve112Mask_clean_of_lt _ (by
                                              dsimp [reserve1, reserve1Word]
                                              exact reserve112Word_lt _)
                                          have hbound0Source :
                                              Int.ofNat balance0.toNat ≤ maxUint112 := by
                                            have hmask :
                                                reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                              native_decide
                                            have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                              simpa [hmask] using hbound0
                                            norm_num [maxUint112]
                                            exact_mod_cast hnat
                                          have hbound1Source :
                                              Int.ofNat balance1.toNat ≤ maxUint112 := by
                                            have hmask :
                                                reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                              native_decide
                                            have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                              simpa [hmask] using hbound1
                                            norm_num [maxUint112]
                                            exact_mod_cast hnat
                                          have hbody :=
                                            ExecFuncBody.execBlockRet
                                              (uniswapMintProportionalFeeOnReturn_kLastZero
                                                evmS evm0S evm1S evmFeeS I feeTo
                                                (by simp only [evmS, initState]; exact hwv)
                                                hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                hfeeCall hfeeDec hfeeToAddr hkLastSource
                                                htotalSourceNonzero hfitSource0 hfitSource1
                                                hreserve0Source hreserve1Source hliquiditySource
                                                hliqNonzero hfitSupplySource hbalanceFitSource
                                                hbound0Source hbound1Source helapsedSource
                                                hfitKLastSource)
                                          have hMintAccounts :
                                              accountMapEquiv σAfterMint postMint.accountMap := by
                                            exact
                                              accountMapEquiv_mintFunctionPostState_of_runtimeMint
                                                hPostAccountsFee henvFeeI
                                                (by dsimp [memFee]; rw [hmem]; omega)
                                                hfitSupplySource hbalanceFitSource
                                          have henvMint : postMint.executionEnv = I := by
                                            simp [postMint, mintFunctionPostState,
                                              mintFunctionAfterTotalSupplyState, henvFeeI,
                                              storageStore_executionEnv]
                                          have hslot8 :
                                              Solm.EVM.storageLoad postMint
                                                  postMint.executionEnv.codeOwner ⟨8⟩ =
                                                uniswapSlotWord ⟨8⟩ σAfterMint I := by
                                            have hword := accountMapEquiv_storage_findD
                                              hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
                                            simpa [postMint, uniswapSlotWord, Solm.EVM.storageLoad,
                                              State.lookupAccount, Account.lookupStorage, henvMint]
                                              using hword.symm
                                          have hPackedAccounts :
                                              accountMapEquiv σPacked syncState.accountMap := by
                                            exact accountMapEquiv_syncUpdatePackedReserveState
                                              hMintAccounts henvMint hslot8 rfl
                                          have henvSync : syncState.executionEnv = I := by
                                            simp [syncState, postMint, syncUpdatePackedReserveState,
                                              henvMint, storageStore_executionEnv]
                                          have hslot8Sync :
                                              Solm.EVM.storageLoad syncState
                                                  syncState.executionEnv.codeOwner ⟨8⟩ =
                                                uniswapSlotWord ⟨8⟩ σPacked I := by
                                            have hword := accountMapEquiv_storage_findD
                                              hPackedAccounts I.codeOwner ⟨8⟩ ⟨0⟩
                                            simpa [syncState, uniswapSlotWord, Solm.EVM.storageLoad,
                                              State.lookupAccount, Account.lookupStorage, henvSync]
                                              using hword.symm
                                          have hsyncReserve0 :
                                              uniswapReserve0Word syncState =
                                                UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I)
                                                  reserve112Mask := by
                                            simp [uniswapReserve0Word, hslot8Sync]
                                          have hsyncReserve1 :
                                              uniswapReserve1Word syncState =
                                                UInt256.land
                                                  (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I)
                                                    reserve112Shift)
                                                  reserve112Mask := by
                                            simp [uniswapReserve1Word, hslot8Sync]
                                          have hkLastValue :
                                              mintFeeReserveProductWord
                                                  (uniswapReserve0Word syncState)
                                                  (uniswapReserve1Word syncState) =
                                                kLastWord := by
                                            rw [hsyncReserve0, hsyncReserve1]
                                            dsimp [kLastWord]
                                            exact mintFeeReserveProductWord_eq_mul _ _
                                              (by
                                                simpa [mintFeeReserveProductNat] using
                                                  hfitKLastRuntime)
                                          have hKLastAccounts :
                                              accountMapEquiv
                                                (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
                                                  kLastWord)
                                                (mintKLastUpdatedState syncState).accountMap := by
                                            have hs := accountMapEquiv_sstoreAccountMap
                                              I.codeOwner ⟨11⟩ kLastWord hPackedAccounts
                                            simpa [mintKLastUpdatedState, storageStore_accountMap,
                                              henvSync, hkLastValue] using hs
                                          have hAccountsRet :
                                              accountMapEquiv
                                                (sstoreAccountMap I.codeOwner
                                                  (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
                                                    kLastWord) ⟨12⟩ (⟨1⟩ : UInt256))
                                                (uniswapLockExitedState
                                                  (mintKLastUpdatedState syncState)).accountMap := by
                                            have hs := accountMapEquiv_sstoreAccountMap
                                              I.codeOwner ⟨12⟩ ⟨1⟩ hKLastAccounts
                                            simpa [uniswapLockExitedState, uniswapUnlockedState,
                                              storageStore_accountMap, storageStore_executionEnv,
                                              mintKLastUpdatedState, henvSync] using hs
                                          have hCreatedRet :
                                              cAFee =
                                                (uniswapLockExitedState
                                                  (mintKLastUpdatedState syncState)).createdAccounts := by
                                            simp [uniswapLockExitedState, uniswapUnlockedState,
                                              mintKLastUpdatedState, syncState, postMint,
                                              syncUpdatePackedReserveState, mintFunctionPostState,
                                              mintFunctionAfterTotalSupplyState,
                                              storageStore_createdAccounts, hcreatedFee]
                                          have rdRet :
                                              RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
                                                (initState cA gh bl σ_evm σ₀
                                                  (Sat256.ofUInt256 g) A I)
                                                (cAFee, sstoreAccountMap I.codeOwner
                                                  (sstoreAccountMap I.codeOwner σPacked ⟨11⟩
                                                    kLastWord) ⟨12⟩ (⟨1⟩ : UInt256))
                                                (UInt256.toByteArray liquidity) := by
                                            simpa [memFee, totalSupply, reserve0, reserve1,
                                              liquidity, σAfterMint, packed, σPacked, kLastWord]
                                              using
                                                uniswapMintRuntimeAfterMintFeeProportionalFeeOnReturns
                                                  (liquidity := liquidity) rd3701 rfl
                                                  htotalNonzero hclean0 hclean1 hmulFit0
                                                  hmulFit1 hreserve0Nonzero hreserve1Nonzero rfl
                                                  hliqNonzero hperm htotalFit hbalanceFit hbound0
                                                  hbound1 helapsed0
                                                  (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
                                                  hfitKLastRuntime hmem hmem64
                                          exact rdRet.reEquivExecutionGenAccountMapEquiv
                                            hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                                            hCreatedRet hAccountsRet
                                            (returnEquiv_of_encode
                                              (by simpa [uint256] using
                                                uint256ReturnEncoding liquidity))
                                        · by_cases hproportionalFeeOnKLastZeroCumulative :
                                            UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                              mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                              totalSupply ≠ ⟨0⟩ ∧
                                              amount0.toNat * totalSupply.toNat < UInt256.size ∧
                                              amount1.toNat * totalSupply.toNat < UInt256.size ∧
                                              reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                              liquidity ≠ ⟨0⟩ ∧
                                              totalSupply.toNat + liquidity.toNat < UInt256.size ∧
                                              (uniswapCodeOwnerStorageWord I
                                                (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                                  (totalSupply + liquidity))
                                                (uniswapInternalMintBalanceHashSlot
                                                  (mintToMaskedWord I) memFee)).toNat +
                                                  liquidity.toNat <
                                                UInt256.size ∧
                                              mintFunctionToBalanceNewNat evmFeeS
                                                  (AccountAddress.ofNat (mintToWord I).toNat)
                                                  liquidity <
                                                UInt256.size ∧
                                              balance0.toNat ≤ reserve112Mask.toNat ∧
                                              balance1.toNat ≤ reserve112Mask.toNat ∧
                                              UInt256.land
                                                  (uniswapUpdateElapsedWord
                                                    (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
                                                  reserve32Mask ≠
                                                ⟨0⟩ ∧
                                              0 <
                                                syncTimeElapsedInt
                                                  (mintFunctionPostState evmFeeS
                                                    (AccountAddress.ofNat (mintToWord I).toNat)
                                                    liquidity) ∧
                                              (UInt256.land
                                                    (uniswapSlotWord ⟨8⟩
                                                      σCumulativeWith I)
                                                    reserve112Mask).toNat *
                                                  (UInt256.land
                                                    (UInt256.div
                                                      (uniswapSlotWord ⟨8⟩
                                                        σCumulativeWith I)
                                                      reserve112Shift)
                                                    reserve112Mask).toNat <
                                                UInt256.size ∧
                                              mintFeeReserveProductNat
                                                  (uniswapReserve0Word
                                                    syncCumulativeStateWith)
                                                  (uniswapReserve1Word
                                                    syncCumulativeStateWith) <
                                                UInt256.size
                                          · rcases hproportionalFeeOnKLastZeroCumulative with
                                            ⟨hfeeToNonzero, hkLastZero, htotalNonzero,
                                              hmulFit0, hmulFit1, hreserve0Nonzero,
                                              hreserve1Nonzero, hliqNonzero, htotalFit,
                                              hbalanceFit, hbalanceFitSource, hbound0, hbound1,
                                              helapsedNe, helapsedSource, hfitKLastRuntime,
                                              hfitKLastSource⟩
                                            have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
                                              exact
                                                accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
                                                  (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                                  hfeeToNonzero
                                            have hkLastSource :
                                                (mintFeeKLastWord evmFeeS).toNat = 0 := by
                                              rw [hkLastEq, hkLastZero]
                                              rfl
                                            have htotalSourceNonzero :
                                                mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
                                              intro hzero
                                              apply htotalNonzero
                                              simpa [totalSupply] using htotalEq.symm.trans hzero
                                            have hfitSource0 :
                                                mintAmountProductNat
                                                    (mintAmount0Word (uniswapLockEnteredState evmS)
                                                      balance0)
                                                    (mintFunctionTotalSupplyWord evmFeeS) <
                                                  UInt256.size := by
                                              simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                                totalSupply, hreserve0Eq, htotalEq] using hmulFit0
                                            have hfitSource1 :
                                                mintAmountProductNat
                                                    (mintAmount1Word (uniswapLockEnteredState evmS)
                                                      balance1)
                                                    (mintFunctionTotalSupplyWord evmFeeS) <
                                                  UInt256.size := by
                                              simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                                totalSupply, hreserve1Eq, htotalEq] using hmulFit1
                                            have hreserve0Source :
                                                uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                                  ⟨0⟩ := by
                                              intro hzero
                                              apply hreserve0Nonzero
                                              simpa [reserve0, hreserve0Eq] using hzero
                                            have hreserve1Source :
                                                uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                                  ⟨0⟩ := by
                                              intro hzero
                                              apply hreserve1Nonzero
                                              simpa [reserve1, hreserve1Eq] using hzero
                                            have hprod0 :
                                                mintAmountProductWord amount0 totalSupply =
                                                  UInt256.mul amount0 totalSupply :=
                                              mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
                                            have hprod1 :
                                                mintAmountProductWord amount1 totalSupply =
                                                  UInt256.mul amount1 totalSupply :=
                                              mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
                                            have hliquiditySource :
                                                liquidity =
                                                  minFunctionResultWord
                                                    (mintProportionalLiquidityWord
                                                      (mintAmount0Word
                                                        (uniswapLockEnteredState evmS) balance0)
                                                      (mintFunctionTotalSupplyWord evmFeeS)
                                                      (uniswapReserve0Word
                                                        (uniswapLockEnteredState evmS)))
                                                    (mintProportionalLiquidityWord
                                                      (mintAmount1Word
                                                        (uniswapLockEnteredState evmS) balance1)
                                                      (mintFunctionTotalSupplyWord evmFeeS)
                                                      (uniswapReserve1Word
                                                        (uniswapLockEnteredState evmS))) := by
                                              rw [show
                                                  mintAmount0Word (uniswapLockEnteredState evmS)
                                                      balance0 =
                                                    amount0 by
                                                  simp [mintAmount0Word, amount0, hreserve0Eq]]
                                              rw [show
                                                  mintAmount1Word (uniswapLockEnteredState evmS)
                                                      balance1 =
                                                    amount1 by
                                                  simp [mintAmount1Word, amount1, hreserve1Eq]]
                                              rw [show mintFunctionTotalSupplyWord evmFeeS =
                                                  totalSupply by simpa [totalSupply] using htotalEq]
                                              rw [show
                                                  uniswapReserve0Word (uniswapLockEnteredState evmS) =
                                                    reserve0 by
                                                  simpa [reserve0] using hreserve0Eq]
                                              rw [show
                                                  uniswapReserve1Word (uniswapLockEnteredState evmS) =
                                                    reserve1 by
                                                  simpa [reserve1] using hreserve1Eq]
                                              simp [liquidity, mintProportionalLiquidityWord, hprod0,
                                                hprod1]
                                            have hfitSupplySource :
                                                mintFunctionTotalSupplyNewNat evmFeeS liquidity <
                                                  UInt256.size := by
                                              simpa [mintFunctionTotalSupplyNewNat, totalSupply,
                                                htotalEq] using htotalFit
                                            obtain ⟨_, _, rd3701⟩ :=
                                              uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
                                                rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                                hzFeeTrue houtFee32 hfeeToNonzero hkLastZero
                                            have hmem :
                                                memFee.size = 164 :=
                                              feeToStaticcallMem_size_of_size_ge
                                                (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                            have hmem64 :
                                                memFee.readWithPadding 64 32 =
                                                  UInt256.toByteArray ⟨128⟩ :=
                                              feeToStaticcallMem_read64_of_size_ge
                                                (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                            have hclean0 :
                                                UInt256.land reserve0 reserve112Mask = reserve0 := by
                                              exact reserve112Mask_clean_of_lt _ (by
                                                dsimp [reserve0, reserve0Word]
                                                exact reserve112Word_lt _)
                                            have hclean1 :
                                                UInt256.land reserve1 reserve112Mask = reserve1 := by
                                              exact reserve112Mask_clean_of_lt _ (by
                                                dsimp [reserve1, reserve1Word]
                                                exact reserve112Word_lt _)
                                            have hbound0Source :
                                                Int.ofNat balance0.toNat ≤ maxUint112 := by
                                              have hmask :
                                                  reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                native_decide
                                              have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                                simpa [hmask] using hbound0
                                              norm_num [maxUint112]
                                              exact_mod_cast hnat
                                            have hbound1Source :
                                                Int.ofNat balance1.toNat ≤ maxUint112 := by
                                              have hmask :
                                                  reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                native_decide
                                              have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                                simpa [hmask] using hbound1
                                              norm_num [maxUint112]
                                              exact_mod_cast hnat
                                            have hfitKLastSource' :
                                                mintFeeReserveProductNat
                                                    (uniswapReserve0Word
                                                      (syncUpdateCumulativePackedReserveStateWith
                                                        (mintFunctionPostState evmFeeS
                                                          (AccountAddress.ofNat
                                                            (mintToWord I).toNat) liquidity)
                                                        balance0 balance1
                                                        (uniswapReserve0Word
                                                          (uniswapLockEnteredState evmS))
                                                        (uniswapReserve1Word
                                                          (uniswapLockEnteredState evmS))))
                                                    (uniswapReserve1Word
                                                      (syncUpdateCumulativePackedReserveStateWith
                                                        (mintFunctionPostState evmFeeS
                                                          (AccountAddress.ofNat
                                                            (mintToWord I).toNat) liquidity)
                                                        balance0 balance1
                                                        (uniswapReserve0Word
                                                          (uniswapLockEnteredState evmS))
                                                        (uniswapReserve1Word
                                                          (uniswapLockEnteredState evmS)))) <
                                                  UInt256.size := by
                                              rw [show
                                                  uniswapReserve0Word
                                                      (uniswapLockEnteredState evmS) =
                                                    reserve0 by
                                                  simpa [reserve0] using hreserve0Eq]
                                              rw [show
                                                  uniswapReserve1Word
                                                      (uniswapLockEnteredState evmS) =
                                                    reserve1 by
                                                  simpa [reserve1] using hreserve1Eq]
                                              exact hfitKLastSource
                                            have hbody :=
                                              ExecFuncBody.execBlockRet
                                                (uniswapMintProportionalFeeOnCumulativeReturn_kLastZero
                                                  evmS evm0S evm1S evmFeeS I feeTo
                                                  (by simp only [evmS, initState]; exact hwv)
                                                  hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                  hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                  hfeeCall hfeeDec hfeeToAddr hkLastSource
                                                  htotalSourceNonzero hfitSource0 hfitSource1
                                                  hreserve0Source hreserve1Source hliquiditySource
                                                  hliqNonzero hfitSupplySource hbalanceFitSource
                                                  hbound0Source hbound1Source
                                                  helapsedSource hfitKLastSource')
                                            exact
                                              uniswapMintFinishProportionalFeeOnCumulativeKLastUpdated
                                                hcode hdispatch hsz36
                                                (by simpa [hreserve0Eq, hreserve1Eq] using hbody)
                                                rd3701 hPostAccountsFee henvFeeI hcreatedFee
                                                (by rfl) htotalNonzero hclean0 hclean1
                                                hmulFit0 hmulFit1 hreserve0Nonzero
                                                hreserve1Nonzero (by rfl) hliqNonzero
                                                hperm htotalFit hbalanceFit hfitSupplySource
                                                hbalanceFitSource hbound0 hbound1 helapsedNe
                                                hfitKLastRuntime hmem hmem64
                                          · let σCleared :=
                                            sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩
                                            let evmAfterFee := mintFeeKLastClearedState evmFeeS
                                            let totalSupplyCleared :=
                                              uniswapSlotWord ⟨0⟩ σCleared I
                                            let liquidityCleared :=
                                              minFunctionResultWord
                                                (UInt256.div
                                                  (UInt256.mul amount0 totalSupplyCleared) reserve0)
                                                (UInt256.div
                                                  (UInt256.mul amount1 totalSupplyCleared) reserve1)
                                            let σAfterMintCleared :=
                                              sstoreAccountMap I.codeOwner
                                                (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
                                                  (totalSupplyCleared + liquidityCleared))
                                                (uniswapInternalMintBalanceHashSlot
                                                  (mintToMaskedWord I)
                                                  (uniswapInternalMintBalanceHashMem
                                                    (mintToMaskedWord I) memFee))
                                                (uniswapCodeOwnerStorageWord I
                                                  (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
                                                    (totalSupplyCleared + liquidityCleared))
                                                  (uniswapInternalMintBalanceHashSlot
                                                    (mintToMaskedWord I) memFee) + liquidityCleared)
                                            by_cases hproportionalFeeOffKLastNonzero :
                                                UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                  mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                  totalSupplyCleared ≠ ⟨0⟩ ∧
                                                  amount0.toNat * totalSupplyCleared.toNat <
                                                    UInt256.size ∧
                                                  amount1.toNat * totalSupplyCleared.toNat <
                                                    UInt256.size ∧
                                                  reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                  liquidityCleared ≠ ⟨0⟩ ∧
                                                  totalSupplyCleared.toNat + liquidityCleared.toNat <
                                                    UInt256.size ∧
                                                  (uniswapCodeOwnerStorageWord I
                                                    (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
                                                      (totalSupplyCleared + liquidityCleared))
                                                    (uniswapInternalMintBalanceHashSlot
                                                      (mintToMaskedWord I) memFee)).toNat +
                                                      liquidityCleared.toNat <
                                                    UInt256.size ∧
                                                  mintFunctionToBalanceNewNat evmAfterFee
                                                      (AccountAddress.ofNat (mintToWord I).toNat)
                                                      liquidityCleared <
                                                    UInt256.size ∧
                                                  balance0.toNat ≤ reserve112Mask.toNat ∧
                                                  balance1.toNat ≤ reserve112Mask.toNat ∧
                                                  UInt256.land
                                                      (uniswapUpdateElapsedWord
                                                        (uniswapSlotWord ⟨8⟩ σAfterMintCleared I) I)
                                                      reserve32Mask =
                                                    ⟨0⟩ ∧
                                                  syncTimeElapsedInt
                                                      (mintFunctionPostState evmAfterFee
                                                        (AccountAddress.ofNat (mintToWord I).toNat)
                                                        liquidityCleared) =
                                                    0
                                            · rcases hproportionalFeeOffKLastNonzero with
                                                ⟨hfeeToZero, hkLastNonzero, htotalNonzero,
                                                  hmulFit0, hmulFit1, hreserve0Nonzero,
                                                  hreserve1Nonzero, hliqNonzero, htotalFit,
                                                  hbalanceFit, hbalanceFitSource, hbound0, hbound1,
                                                  helapsed0, helapsedSource⟩
                                              have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
                                                exact
                                                  accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
                                                    (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                                    hfeeToZero
                                              have hkLastSource :
                                                  (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
                                                intro hzero
                                                apply hkLastNonzero
                                                rw [← hkLastEq]
                                                exact uint256_toNat_eq_zero hzero
                                              have hPostCleared :
                                                  accountMapEquiv σCleared evmAfterFee.accountMap := by
                                                have hstore :=
                                                  accountMapEquiv_sstoreAccountMap I.codeOwner
                                                    ⟨11⟩ ⟨0⟩ hPostAccountsFee
                                                simpa [σCleared, evmAfterFee,
                                                  mintFeeKLastClearedState, henvFeeI,
                                                  storageStore_accountMap] using hstore
                                              have henvCleared : evmAfterFee.executionEnv = I := by
                                                simp [evmAfterFee, mintFeeKLastClearedState, henvFeeI,
                                                  storageStore_executionEnv]
                                              have htotalEqCleared :
                                                  mintFunctionTotalSupplyWord evmAfterFee =
                                                    totalSupplyCleared := by
                                                simpa [totalSupplyCleared] using
                                                  mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv
                                                    hPostCleared henvCleared
                                              have htotalSourceNonzero :
                                                  mintFunctionTotalSupplyWord evmAfterFee ≠ ⟨0⟩ := by
                                                intro hzero
                                                apply htotalNonzero
                                                simpa [totalSupplyCleared] using
                                                  htotalEqCleared.symm.trans hzero
                                              have hfitSource0 :
                                                  mintAmountProductNat
                                                      (mintAmount0Word (uniswapLockEnteredState evmS)
                                                        balance0)
                                                      (mintFunctionTotalSupplyWord evmAfterFee) <
                                                    UInt256.size := by
                                                simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                                  totalSupplyCleared, hreserve0Eq, htotalEqCleared]
                                                  using hmulFit0
                                              have hfitSource1 :
                                                  mintAmountProductNat
                                                      (mintAmount1Word (uniswapLockEnteredState evmS)
                                                        balance1)
                                                      (mintFunctionTotalSupplyWord evmAfterFee) <
                                                    UInt256.size := by
                                                simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                                  totalSupplyCleared, hreserve1Eq, htotalEqCleared]
                                                  using hmulFit1
                                              have hreserve0Source :
                                                  uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                                    ⟨0⟩ := by
                                                intro hzero
                                                apply hreserve0Nonzero
                                                simpa [reserve0, hreserve0Eq] using hzero
                                              have hreserve1Source :
                                                  uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                                    ⟨0⟩ := by
                                                intro hzero
                                                apply hreserve1Nonzero
                                                simpa [reserve1, hreserve1Eq] using hzero
                                              have hprod0 :
                                                  mintAmountProductWord amount0 totalSupplyCleared =
                                                    UInt256.mul amount0 totalSupplyCleared :=
                                                mintAmountProductWord_eq_mul amount0 totalSupplyCleared
                                                  hmulFit0
                                              have hprod1 :
                                                  mintAmountProductWord amount1 totalSupplyCleared =
                                                    UInt256.mul amount1 totalSupplyCleared :=
                                                mintAmountProductWord_eq_mul amount1 totalSupplyCleared
                                                  hmulFit1
                                              have hliquiditySource :
                                                  liquidityCleared =
                                                    minFunctionResultWord
                                                      (mintProportionalLiquidityWord
                                                        (mintAmount0Word
                                                          (uniswapLockEnteredState evmS) balance0)
                                                        (mintFunctionTotalSupplyWord evmAfterFee)
                                                        (uniswapReserve0Word
                                                          (uniswapLockEnteredState evmS)))
                                                      (mintProportionalLiquidityWord
                                                        (mintAmount1Word
                                                          (uniswapLockEnteredState evmS) balance1)
                                                        (mintFunctionTotalSupplyWord evmAfterFee)
                                                        (uniswapReserve1Word
                                                          (uniswapLockEnteredState evmS))) := by
                                                rw [show
                                                    mintAmount0Word (uniswapLockEnteredState evmS)
                                                        balance0 =
                                                      amount0 by
                                                    simp [mintAmount0Word, amount0, hreserve0Eq]]
                                                rw [show
                                                    mintAmount1Word (uniswapLockEnteredState evmS)
                                                        balance1 =
                                                      amount1 by
                                                    simp [mintAmount1Word, amount1, hreserve1Eq]]
                                                rw [show mintFunctionTotalSupplyWord evmAfterFee =
                                                    totalSupplyCleared by
                                                  simpa [totalSupplyCleared] using htotalEqCleared]
                                                rw [show
                                                    uniswapReserve0Word
                                                        (uniswapLockEnteredState evmS) =
                                                      reserve0 by
                                                    simpa [reserve0] using hreserve0Eq]
                                                rw [show
                                                    uniswapReserve1Word
                                                        (uniswapLockEnteredState evmS) =
                                                      reserve1 by
                                                    simpa [reserve1] using hreserve1Eq]
                                                simp [liquidityCleared, mintProportionalLiquidityWord,
                                                  hprod0, hprod1]
                                              have hfitSupplySource :
                                                  mintFunctionTotalSupplyNewNat evmAfterFee
                                                      liquidityCleared <
                                                    UInt256.size := by
                                                simpa [mintFunctionTotalSupplyNewNat,
                                                  totalSupplyCleared, htotalEqCleared] using
                                                  htotalFit
                                              obtain ⟨_, _, rd3701⟩ :=
                                                uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
                                                  rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                                  hzFeeTrue houtFee32 hfeeToZero hperm
                                                  hkLastNonzero
                                              have hmem :
                                                  memFee.size = 164 :=
                                                feeToStaticcallMem_size_of_size_ge
                                                  (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                  ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                              have hmem64 :
                                                  memFee.readWithPadding 64 32 =
                                                    UInt256.toByteArray ⟨128⟩ :=
                                                feeToStaticcallMem_read64_of_size_ge
                                                  (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                  ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                              have hclean0 :
                                                  UInt256.land reserve0 reserve112Mask = reserve0 := by
                                                exact reserve112Mask_clean_of_lt _ (by
                                                  dsimp [reserve0, reserve0Word]
                                                  exact reserve112Word_lt _)
                                              have hclean1 :
                                                  UInt256.land reserve1 reserve112Mask = reserve1 := by
                                                exact reserve112Mask_clean_of_lt _ (by
                                                  dsimp [reserve1, reserve1Word]
                                                  exact reserve112Word_lt _)
                                              have hbound0Source :
                                                  Int.ofNat balance0.toNat ≤ maxUint112 := by
                                                have hmask :
                                                    reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                  native_decide
                                                have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                                  simpa [hmask] using hbound0
                                                norm_num [maxUint112]
                                                exact_mod_cast hnat
                                              have hbound1Source :
                                                  Int.ofNat balance1.toNat ≤ maxUint112 := by
                                                have hmask :
                                                    reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                  native_decide
                                                have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                                  simpa [hmask] using hbound1
                                                norm_num [maxUint112]
                                                exact_mod_cast hnat
                                              have hbody :=
                                                ExecFuncBody.execBlockRet
                                                  (uniswapMintProportionalFeeOffReturn_kLastNonzero
                                                    evmS evm0S evm1S evmFeeS I feeTo
                                                    (by simp only [evmS, initState]; exact hwv)
                                                    hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                    hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                    hfeeCall hfeeDec hfeeToAddr hkLastSource
                                                    htotalSourceNonzero hfitSource0 hfitSource1
                                                    hreserve0Source hreserve1Source
                                                    hliquiditySource hliqNonzero hfitSupplySource
                                                    hbalanceFitSource hbound0Source hbound1Source
                                                    helapsedSource)
                                              let postMintCleared :=
                                                mintFunctionPostState evmAfterFee
                                                  (AccountAddress.ofNat (mintToWord I).toNat)
                                                  liquidityCleared
                                              have hMintAccounts :
                                                  accountMapEquiv σAfterMintCleared
                                                    postMintCleared.accountMap := by
                                                exact
                                                  accountMapEquiv_mintFunctionPostState_of_runtimeMint
                                                    hPostCleared henvCleared
                                                    (by dsimp [memFee]; rw [hmem]; omega)
                                                    hfitSupplySource hbalanceFitSource
                                              have henvMint : postMintCleared.executionEnv = I := by
                                                simp [postMintCleared, mintFunctionPostState,
                                                  mintFunctionAfterTotalSupplyState, henvCleared,
                                                  storageStore_executionEnv]
                                              have hslot8 :
                                                  Solm.EVM.storageLoad postMintCleared
                                                      postMintCleared.executionEnv.codeOwner ⟨8⟩ =
                                                    uniswapSlotWord ⟨8⟩ σAfterMintCleared I := by
                                                have hword := accountMapEquiv_storage_findD
                                                  hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
                                                simpa [postMintCleared, uniswapSlotWord,
                                                  Solm.EVM.storageLoad, State.lookupAccount,
                                                  Account.lookupStorage, henvMint] using hword.symm
                                              let packedCleared :=
                                                uniswapUpdatePackedReserveWord
                                                  (uniswapSlotWord ⟨8⟩ σAfterMintCleared I)
                                                  (uniswapUpdateTimestampWord I) balance1 balance0
                                              let σPackedCleared :=
                                                sstoreAccountMap I.codeOwner σAfterMintCleared ⟨8⟩
                                                  packedCleared
                                              have hPackedAccounts :
                                                  accountMapEquiv σPackedCleared
                                                    (syncUpdatePackedReserveState postMintCleared
                                                      balance0 balance1).accountMap := by
                                                exact accountMapEquiv_syncUpdatePackedReserveState
                                                  hMintAccounts henvMint hslot8 rfl
                                              have hAccountsRet :
                                                  accountMapEquiv
                                                    (sstoreAccountMap I.codeOwner σPackedCleared ⟨12⟩
                                                      (⟨1⟩ : UInt256))
                                                    (uniswapLockExitedState
                                                      (syncUpdatePackedReserveState postMintCleared
                                                        balance0 balance1)).accountMap := by
                                                have hs := accountMapEquiv_sstoreAccountMap
                                                  I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccounts
                                                simpa [uniswapLockExitedState, uniswapUnlockedState,
                                                  storageStore_accountMap, storageStore_executionEnv,
                                                  syncUpdatePackedReserveState, henvMint] using hs
                                              have hCreatedRet :
                                                  cAFee =
                                                    (uniswapLockExitedState
                                                      (syncUpdatePackedReserveState postMintCleared
                                                        balance0 balance1)).createdAccounts := by
                                                simp [uniswapLockExitedState, uniswapUnlockedState,
                                                  syncUpdatePackedReserveState, postMintCleared,
                                                  mintFunctionPostState,
                                                  mintFunctionAfterTotalSupplyState,
                                                  evmAfterFee, mintFeeKLastClearedState,
                                                  storageStore_createdAccounts, hcreatedFee]
                                              have rdRet :
                                                  RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
                                                    (initState cA gh bl σ_evm σ₀
                                                      (Sat256.ofUInt256 g) A I)
                                                    (cAFee, sstoreAccountMap I.codeOwner
                                                      σPackedCleared ⟨12⟩ (⟨1⟩ : UInt256))
                                                    (UInt256.toByteArray liquidityCleared) := by
                                                simpa [memFee, σCleared, totalSupplyCleared, reserve0,
                                                  reserve1, liquidityCleared, σAfterMintCleared,
                                                  packedCleared, σPackedCleared] using
                                                  uniswapMintRuntimeAfterMintFeeProportionalFeeOffReturns
                                                    (liquidity := liquidityCleared) rd3701 rfl
                                                    htotalNonzero hclean0 hclean1 hmulFit0
                                                    hmulFit1 hreserve0Nonzero hreserve1Nonzero rfl
                                                    hliqNonzero hperm htotalFit hbalanceFit hbound0
                                                    hbound1 helapsed0 rfl hmem hmem64
                                              exact rdRet.reEquivExecutionGenAccountMapEquiv
                                                hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
                                                hCreatedRet hAccountsRet
                                                (returnEquiv_of_encode
                                                  (by simpa [uint256] using
                                                    uint256ReturnEncoding liquidityCleared))
                                            · by_cases hproportionalFeeOffKLastNonzeroCumulative :
                                                UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                  mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                  totalSupplyCleared ≠ ⟨0⟩ ∧
                                                  amount0.toNat * totalSupplyCleared.toNat <
                                                    UInt256.size ∧
                                                  amount1.toNat * totalSupplyCleared.toNat <
                                                    UInt256.size ∧
                                                  reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                  liquidityCleared ≠ ⟨0⟩ ∧
                                                  totalSupplyCleared.toNat + liquidityCleared.toNat <
                                                    UInt256.size ∧
                                                  (uniswapCodeOwnerStorageWord I
                                                    (sstoreAccountMap I.codeOwner σCleared ⟨0⟩
                                                      (totalSupplyCleared + liquidityCleared))
                                                    (uniswapInternalMintBalanceHashSlot
                                                      (mintToMaskedWord I) memFee)).toNat +
                                                      liquidityCleared.toNat <
                                                    UInt256.size ∧
                                                  mintFunctionToBalanceNewNat evmAfterFee
                                                      (AccountAddress.ofNat (mintToWord I).toNat)
                                                      liquidityCleared <
                                                    UInt256.size ∧
                                                  balance0.toNat ≤ reserve112Mask.toNat ∧
                                                  balance1.toNat ≤ reserve112Mask.toNat ∧
                                                  UInt256.land
                                                      (uniswapUpdateElapsedWord
                                                        (uniswapSlotWord ⟨8⟩ σAfterMintCleared I) I)
                                                      reserve32Mask ≠
                                                    ⟨0⟩ ∧
                                                  0 <
                                                    syncTimeElapsedInt
                                                      (mintFunctionPostState evmAfterFee
                                                        (AccountAddress.ofNat (mintToWord I).toNat)
                                                        liquidityCleared)
                                              · rcases hproportionalFeeOffKLastNonzeroCumulative with
                                                  ⟨hfeeToZero, hkLastNonzero, htotalNonzero,
                                                    hmulFit0, hmulFit1, hreserve0Nonzero,
                                                    hreserve1Nonzero, hliqNonzero, htotalFit,
                                                    hbalanceFit, hbalanceFitSource, hbound0, hbound1,
                                                    helapsedNe, helapsedSource⟩
                                                have hfeeToAddr : feeTo = AccountAddress.ofNat 0 := by
                                                  exact
                                                    accountAddress_ofNat_eq_zero_of_land_solcAddrMask_eq_zero
                                                      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
                                                      hfeeToZero
                                                have hkLastSource :
                                                    (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
                                                  intro hzero
                                                  apply hkLastNonzero
                                                  rw [← hkLastEq]
                                                  exact uint256_toNat_eq_zero hzero
                                                have hPostCleared :
                                                    accountMapEquiv σCleared evmAfterFee.accountMap := by
                                                  have hstore :=
                                                    accountMapEquiv_sstoreAccountMap I.codeOwner
                                                      ⟨11⟩ ⟨0⟩ hPostAccountsFee
                                                  simpa [σCleared, evmAfterFee,
                                                    mintFeeKLastClearedState, henvFeeI,
                                                    storageStore_accountMap] using hstore
                                                have henvCleared :
                                                    evmAfterFee.executionEnv = I := by
                                                  simp [evmAfterFee, mintFeeKLastClearedState,
                                                    henvFeeI, storageStore_executionEnv]
                                                have hcreatedCleared :
                                                    evmAfterFee.createdAccounts = cAFee := by
                                                  simp [evmAfterFee, mintFeeKLastClearedState,
                                                    storageStore_createdAccounts, hcreatedFee]
                                                have htotalEqCleared :
                                                    mintFunctionTotalSupplyWord evmAfterFee =
                                                      totalSupplyCleared := by
                                                  simpa [totalSupplyCleared] using
                                                    mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv
                                                      hPostCleared henvCleared
                                                have htotalSourceNonzero :
                                                    mintFunctionTotalSupplyWord evmAfterFee ≠ ⟨0⟩ := by
                                                  intro hzero
                                                  apply htotalNonzero
                                                  simpa [totalSupplyCleared] using
                                                    htotalEqCleared.symm.trans hzero
                                                have hfitSource0 :
                                                    mintAmountProductNat
                                                        (mintAmount0Word
                                                          (uniswapLockEnteredState evmS) balance0)
                                                        (mintFunctionTotalSupplyWord evmAfterFee) <
                                                      UInt256.size := by
                                                  simpa [mintAmountProductNat, mintAmount0Word, amount0,
                                                    totalSupplyCleared, hreserve0Eq, htotalEqCleared]
                                                    using hmulFit0
                                                have hfitSource1 :
                                                    mintAmountProductNat
                                                        (mintAmount1Word
                                                          (uniswapLockEnteredState evmS) balance1)
                                                        (mintFunctionTotalSupplyWord evmAfterFee) <
                                                      UInt256.size := by
                                                  simpa [mintAmountProductNat, mintAmount1Word, amount1,
                                                    totalSupplyCleared, hreserve1Eq, htotalEqCleared]
                                                    using hmulFit1
                                                have hreserve0Source :
                                                    uniswapReserve0Word (uniswapLockEnteredState evmS) ≠
                                                      ⟨0⟩ := by
                                                  intro hzero
                                                  apply hreserve0Nonzero
                                                  simpa [reserve0, hreserve0Eq] using hzero
                                                have hreserve1Source :
                                                    uniswapReserve1Word (uniswapLockEnteredState evmS) ≠
                                                      ⟨0⟩ := by
                                                  intro hzero
                                                  apply hreserve1Nonzero
                                                  simpa [reserve1, hreserve1Eq] using hzero
                                                have hprod0 :
                                                    mintAmountProductWord amount0 totalSupplyCleared =
                                                      UInt256.mul amount0 totalSupplyCleared :=
                                                  mintAmountProductWord_eq_mul amount0 totalSupplyCleared
                                                    hmulFit0
                                                have hprod1 :
                                                    mintAmountProductWord amount1 totalSupplyCleared =
                                                      UInt256.mul amount1 totalSupplyCleared :=
                                                  mintAmountProductWord_eq_mul amount1 totalSupplyCleared
                                                    hmulFit1
                                                have hliquiditySource :
                                                    liquidityCleared =
                                                      minFunctionResultWord
                                                        (mintProportionalLiquidityWord
                                                          (mintAmount0Word
                                                            (uniswapLockEnteredState evmS) balance0)
                                                          (mintFunctionTotalSupplyWord evmAfterFee)
                                                          (uniswapReserve0Word
                                                            (uniswapLockEnteredState evmS)))
                                                        (mintProportionalLiquidityWord
                                                          (mintAmount1Word
                                                            (uniswapLockEnteredState evmS) balance1)
                                                          (mintFunctionTotalSupplyWord evmAfterFee)
                                                          (uniswapReserve1Word
                                                            (uniswapLockEnteredState evmS))) := by
                                                  rw [show
                                                      mintAmount0Word (uniswapLockEnteredState evmS)
                                                          balance0 =
                                                        amount0 by
                                                      simp [mintAmount0Word, amount0, hreserve0Eq]]
                                                  rw [show
                                                      mintAmount1Word (uniswapLockEnteredState evmS)
                                                          balance1 =
                                                        amount1 by
                                                      simp [mintAmount1Word, amount1, hreserve1Eq]]
                                                  rw [show mintFunctionTotalSupplyWord evmAfterFee =
                                                      totalSupplyCleared by
                                                    simpa [totalSupplyCleared] using htotalEqCleared]
                                                  rw [show
                                                      uniswapReserve0Word
                                                          (uniswapLockEnteredState evmS) =
                                                        reserve0 by
                                                      simpa [reserve0] using hreserve0Eq]
                                                  rw [show
                                                      uniswapReserve1Word
                                                          (uniswapLockEnteredState evmS) =
                                                        reserve1 by
                                                      simpa [reserve1] using hreserve1Eq]
                                                  simp [liquidityCleared, mintProportionalLiquidityWord,
                                                    hprod0, hprod1]
                                                have hfitSupplySource :
                                                    mintFunctionTotalSupplyNewNat evmAfterFee
                                                        liquidityCleared <
                                                      UInt256.size := by
                                                  simpa [mintFunctionTotalSupplyNewNat,
                                                    totalSupplyCleared, htotalEqCleared] using
                                                    htotalFit
                                                obtain ⟨_, _, rd3701⟩ :=
                                                  uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
                                                    rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                                    hzFeeTrue houtFee32 hfeeToZero hperm
                                                    hkLastNonzero
                                                have hmem :
                                                    memFee.size = 164 :=
                                                  feeToStaticcallMem_size_of_size_ge
                                                    (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                    ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                                have hmem64 :
                                                    memFee.readWithPadding 64 32 =
                                                      UInt256.toByteArray ⟨128⟩ :=
                                                  feeToStaticcallMem_read64_of_size_ge
                                                    (UInt256.ofNat I.codeOwner.val) o o1 outFee
                                                    ho32 hoSize ho132 ho1Size houtFee32 houtFeeSize
                                                have hclean0 :
                                                    UInt256.land reserve0 reserve112Mask = reserve0 := by
                                                  exact reserve112Mask_clean_of_lt _ (by
                                                    dsimp [reserve0, reserve0Word]
                                                    exact reserve112Word_lt _)
                                                have hclean1 :
                                                    UInt256.land reserve1 reserve112Mask = reserve1 := by
                                                  exact reserve112Mask_clean_of_lt _ (by
                                                    dsimp [reserve1, reserve1Word]
                                                    exact reserve112Word_lt _)
                                                have hbound0Source :
                                                    Int.ofNat balance0.toNat ≤ maxUint112 := by
                                                  have hmask :
                                                      reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                    native_decide
                                                  have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by
                                                    simpa [hmask] using hbound0
                                                  norm_num [maxUint112]
                                                  exact_mod_cast hnat
                                                have hbound1Source :
                                                    Int.ofNat balance1.toNat ≤ maxUint112 := by
                                                  have hmask :
                                                      reserve112Mask.toNat = 2 ^ 112 - 1 := by
                                                    native_decide
                                                  have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by
                                                    simpa [hmask] using hbound1
                                                  norm_num [maxUint112]
                                                  exact_mod_cast hnat
                                                have hbody :=
                                                  ExecFuncBody.execBlockRet
                                                    (uniswapMintProportionalFeeOffCumulativeReturn_kLastNonzero
                                                      evmS evm0S evm1S evmFeeS I feeTo
                                                      (by simp only [evmS, initState]; exact hwv)
                                                      hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                      hcall1 hdec1 hle0Source hle1Source
                                                      hfeeGuard hfeeCall hfeeDec hfeeToAddr
                                                      hkLastSource htotalSourceNonzero
                                                      hfitSource0 hfitSource1 hreserve0Source
                                                      hreserve1Source hliquiditySource hliqNonzero
                                                      hfitSupplySource hbalanceFitSource hbound0Source
                                                      hbound1Source helapsedSource)
                                                exact
                                                  uniswapMintFinishProportionalFeeOffCumulative
                                                    hcode hdispatch hsz36
                                                    (by
                                                      simpa [hreserve0Eq, hreserve1Eq] using hbody)
                                                    rd3701 hPostCleared henvCleared
                                                    hcreatedCleared (by rfl)
                                                    htotalNonzero hclean0 hclean1 hmulFit0
                                                    hmulFit1 hreserve0Nonzero hreserve1Nonzero
                                                    (by rfl) hliqNonzero hperm
                                                    htotalFit hbalanceFit hfitSupplySource
                                                    hbalanceFitSource hbound0 hbound1
                                                    helapsedNe (by rfl) hmem hmem64
                                              · by_cases hsmallNoMint :
                                                UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                                  mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                  (UInt256.mul reserve0 reserve1).toNat ≤ 3 ∧
                                                  (mintFeeKLastSlotWord σFee I).toNat ≤ 3 ∧
                                                  (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then
                                                      (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
                                                    (if mintFeeKLastSlotWord σFee I = ⟨0⟩ then
                                                      (⟨0⟩ : UInt256) else ⟨1⟩).toNat ∧
                                                  totalSupply ≠ ⟨0⟩ ∧
                                                  amount0.toNat * totalSupply.toNat <
                                                    UInt256.size ∧
                                                  amount1.toNat * totalSupply.toNat <
                                                    UInt256.size ∧
                                                  reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                  liquidity ≠ ⟨0⟩ ∧
                                                  totalSupply.toNat + liquidity.toNat <
                                                    UInt256.size ∧
                                                  (uniswapCodeOwnerStorageWord I
                                                    (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                                      (totalSupply + liquidity))
                                                    (uniswapInternalMintBalanceHashSlot
                                                      (mintToMaskedWord I) memFee)).toNat +
                                                      liquidity.toNat <
                                                    UInt256.size ∧
                                                  mintFunctionToBalanceNewNat evmFeeS
                                                      (AccountAddress.ofNat (mintToWord I).toNat)
                                                      liquidity <
                                                    UInt256.size ∧
                                                  balance0.toNat ≤ reserve112Mask.toNat ∧
                                                  balance1.toNat ≤ reserve112Mask.toNat ∧
                                                  UInt256.land
                                                      (uniswapUpdateElapsedWord
                                                        (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
                                                      reserve32Mask =
                                                    ⟨0⟩ ∧
                                                  (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I)
                                                        reserve112Mask).toNat *
                                                      (UInt256.land
                                                        (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I)
                                                          reserve112Shift)
                                                        reserve112Mask).toNat <
                                                    UInt256.size ∧
                                                  syncTimeElapsedInt postMint = 0 ∧
                                                  mintFeeReserveProductNat
                                                      (uniswapReserve0Word syncState)
                                                      (uniswapReserve1Word syncState) <
                                                    UInt256.size
                                                · exact
                                                    uniswapMintFeeOnKLastNonzeroSmallNoMintFromFactoryCase
                                                      feeTo hcode hdispatch hsz36 hperm hwv
                                                      hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                      hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                      hfeeCall hfeeDec hPostAccountsFee henvFeeI
                                                      hcreatedFee hreserve0Eq hreserve1Eq rfl rfl
                                                      (by
                                                        simpa [mintAmount0Word, amount0, evmS] using
                                                          congrArg (fun w => balance0.sub w) hreserve0Eq)
                                                      (by
                                                        simpa [mintAmount1Word, amount1, evmS] using
                                                          congrArg (fun w => balance1.sub w)
                                                            hreserve1Eq)
                                                      hkLastEq rfl (by simpa [totalSupply] using htotalEq)
                                                      rd7781 ho32 hoSize ho132 ho1Size houtFeeSize
                                                      hzFeeTrue houtFee32 rfl rfl rfl rfl rfl
                                                      (by
                                                        simpa [feeToWord, totalSupply, liquidity,
                                                          σAfterMint, packed, σPacked, postMint,
                                                          syncState, memFee] using hsmallNoMint)
                                                · by_cases hzeroKLastZero :
                                                    (UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                        totalSupply ≠ ⟨0⟩ ∧
                                                        amount0.toNat * totalSupply.toNat <
                                                          UInt256.size ∧
                                                        amount1.toNat * totalSupply.toNat <
                                                          UInt256.size ∧
                                                        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                        liquidity = ⟨0⟩) ∨
                                                      (UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                                        mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                        totalSupply ≠ ⟨0⟩ ∧
                                                        amount0.toNat * totalSupply.toNat <
                                                          UInt256.size ∧
                                                        amount1.toNat * totalSupply.toNat <
                                                          UInt256.size ∧
                                                        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                        liquidity = ⟨0⟩)
                                                  · exact
                                                      uniswapMintProportionalKLastZeroLiquidityZeroFromFactoryCase
                                                        feeTo hcode hdispatch hsz36 hwv
                                                        hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                        hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                        hfeeCall hfeeDec (by simp [feeTo]) rd7781
                                                        ho32 hoSize ho132 ho1Size houtFeeSize
                                                        hzFeeTrue houtFee32 hkLastEq
                                                        (by simpa [totalSupply] using htotalEq)
                                                        (by rfl) (by rfl) (by rfl)
                                                        hreserve0Eq hreserve1Eq
                                                        (by
                                                          simpa [mintAmount0Word, amount0, evmS] using
                                                            congrArg (fun w => balance0.sub w)
                                                              hreserve0Eq)
                                                        (by
                                                          simpa [mintAmount1Word, amount1, evmS] using
                                                            congrArg (fun w => balance1.sub w)
                                                              hreserve1Eq)
                                                        (by
                                                          simpa [feeToWord, liquidity] using
                                                            hzeroKLastZero)
                                                  · by_cases hzeroFeeOffKLastNonzero :
                                                      UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                        mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                        totalSupplyCleared ≠ ⟨0⟩ ∧
                                                        amount0.toNat * totalSupplyCleared.toNat <
                                                          UInt256.size ∧
                                                        amount1.toNat * totalSupplyCleared.toNat <
                                                          UInt256.size ∧
                                                        reserve0 ≠ ⟨0⟩ ∧ reserve1 ≠ ⟨0⟩ ∧
                                                        liquidityCleared = ⟨0⟩
                                                    · exact
                                                        uniswapMintProportionalFeeOffKLastNonzeroLiquidityZeroFromFactoryCase
                                                          feeTo hcode hdispatch hsz36 hwv
                                                          hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                          hcall1 hdec1 hle0Source hle1Source hfeeGuard
                                                          hfeeCall hfeeDec (by simp [feeTo])
                                                          hPostAccountsFee henvFeeI (by rfl) rd7781
                                                          ho32 hoSize ho132 ho1Size houtFeeSize
                                                          hzFeeTrue houtFee32 hperm hkLastEq
                                                          (by rfl) (by rfl) (by rfl)
                                                          hreserve0Eq hreserve1Eq
                                                          (by
                                                            simpa [mintAmount0Word, amount0, evmS] using
                                                              congrArg (fun w => balance0.sub w)
                                                                hreserve0Eq)
                                                          (by
                                                            simpa [mintAmount1Word, amount1, evmS] using
                                                              congrArg (fun w => balance1.sub w)
                                                                hreserve1Eq)
                                                          (by
                                                            simpa [feeToWord, liquidityCleared] using
                                                              hzeroFeeOffKLastNonzero)
                                                    · by_cases hinitialMinOverflowFeeOffKLastZero :
                                                        UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                          mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                          totalSupply = ⟨0⟩ ∧
                                                          amount0.toNat * amount1.toNat <
                                                            UInt256.size ∧
                                                          UInt256.size ≤
                                                            (uniswapCodeOwnerStorageWord I
                                                              (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                                                (totalSupply + (⟨1000⟩ : UInt256)))
                                                              (uniswapInternalMintBalanceHashSlot ⟨0⟩
                                                                memFee)).toNat +
                                                              (⟨1000⟩ : UInt256).toNat
                                                      · rcases hinitialMinOverflowFeeOffKLastZero with
                                                          ⟨hfeeToZero, hkLastZero, htotalZero, hfit,
                                                            hbalanceOverflow⟩
                                                        exact
                                                          uniswapMintInitialFeeOffKLastZeroMinimumMintBalanceOverflowFromFactoryCase
                                                            feeTo hcode hdispatch hsz36 hwv
                                                            hunlockedSolm hguard0 hguard1 hcall0 hdec0
                                                            hcall1 hdec1 hle0Source hle1Source
                                                            hfeeGuard hfeeCall hfeeDec (by simp [feeTo])
                                                            hPostAccountsFee henvFeeI hperm rd7781
                                                            ho32 hoSize ho132 ho1Size houtFeeSize
                                                            hzFeeTrue houtFee32 hkLastEq htotalEq
                                                            (by
                                                              simpa [mintAmount0Word, amount0, evmS]
                                                                using congrArg (fun w => balance0.sub w)
                                                                  hreserve0Eq)
                                                            (by
                                                              simpa [mintAmount1Word, amount1, evmS]
                                                                using congrArg (fun w => balance1.sub w)
                                                                  hreserve1Eq)
                                                            (by simpa [feeToWord] using hfeeToZero)
                                                            hkLastZero
                                                            (by simpa [totalSupply] using htotalZero)
                                                            hfit
                                                            (by
                                                              simpa [memFee, totalSupply] using
                                                                hbalanceOverflow)
                                                      · by_cases hinitialMinOverflowFeeOnKLastZero :
                                                          UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩ ∧
                                                            mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                            totalSupply = ⟨0⟩ ∧
                                                            amount0.toNat * amount1.toNat <
                                                              UInt256.size ∧
                                                            UInt256.size ≤
                                                              (uniswapCodeOwnerStorageWord I
                                                                (sstoreAccountMap I.codeOwner σFee ⟨0⟩
                                                                  (totalSupply + (⟨1000⟩ : UInt256)))
                                                                (uniswapInternalMintBalanceHashSlot ⟨0⟩
                                                                  memFee)).toNat +
                                                                (⟨1000⟩ : UInt256).toNat
                                                        · rcases hinitialMinOverflowFeeOnKLastZero with
                                                            ⟨hfeeToNonzero, hkLastZero, htotalZero, hfit,
                                                              hbalanceOverflow⟩
                                                          exact
                                                            uniswapMintInitialFeeOnKLastZeroMinimumMintBalanceOverflowFromFactoryCase
                                                              feeTo hcode hdispatch hsz36 hwv
                                                              hunlockedSolm hguard0 hguard1 hcall0
                                                              hdec0 hcall1 hdec1 hle0Source hle1Source
                                                              hfeeGuard hfeeCall hfeeDec (by simp [feeTo])
                                                              hPostAccountsFee henvFeeI hperm rd7781
                                                              ho32 hoSize ho132 ho1Size houtFeeSize
                                                              hzFeeTrue houtFee32 hkLastEq htotalEq
                                                              (by
                                                                simpa [mintAmount0Word, amount0, evmS]
                                                                  using
                                                                    congrArg (fun w => balance0.sub w)
                                                                      hreserve0Eq)
                                                              (by
                                                                simpa [mintAmount1Word, amount1, evmS]
                                                                  using
                                                                    congrArg (fun w => balance1.sub w)
                                                                      hreserve1Eq)
                                                              (by simpa [feeToWord] using hfeeToNonzero)
                                                              hkLastZero
                                                              (by simpa [totalSupply] using htotalZero)
                                                              hfit
                                                              (by
                                                                simpa [memFee, totalSupply] using
                                                                  hbalanceOverflow)
                                                        · by_cases hinitialMinOverflowFeeOffKLastNonzero :
                                                            UInt256.land feeToWord solcAddrMask = ⟨0⟩ ∧
                                                              mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                              totalSupplyCleared = ⟨0⟩ ∧
                                                              amount0.toNat * amount1.toNat <
                                                                UInt256.size ∧
                                                              UInt256.size ≤
                                                                (uniswapCodeOwnerStorageWord I
                                                                  (sstoreAccountMap I.codeOwner
                                                                    σCleared ⟨0⟩
                                                                    (totalSupplyCleared +
                                                                      (⟨1000⟩ : UInt256)))
                                                                  (uniswapInternalMintBalanceHashSlot
                                                                    ⟨0⟩ memFee)).toNat +
                                                                  (⟨1000⟩ : UInt256).toNat
                                                          · rcases hinitialMinOverflowFeeOffKLastNonzero with
                                                              ⟨hfeeToZero, hkLastNonzero, htotalZero,
                                                                hfit, hbalanceOverflow⟩
                                                            exact
                                                              uniswapMintInitialFeeOffKLastNonzeroMinimumMintBalanceOverflowFromFactoryCase
                                                                feeTo hcode hdispatch hsz36 hwv
                                                                hunlockedSolm hguard0 hguard1 hcall0
                                                                hdec0 hcall1 hdec1 hle0Source
                                                                hle1Source hfeeGuard hfeeCall hfeeDec
                                                                (by simp [feeTo]) hPostAccountsFee
                                                                henvFeeI hperm rd7781 ho32 hoSize
                                                                ho132 ho1Size houtFeeSize hzFeeTrue
                                                                houtFee32 hkLastEq
                                                                (by
                                                                  simpa [mintAmount0Word, amount0, evmS]
                                                                    using
                                                                      congrArg (fun w => balance0.sub w)
                                                                        hreserve0Eq)
                                                                (by
                                                                  simpa [mintAmount1Word, amount1, evmS]
                                                                    using
                                                                      congrArg (fun w => balance1.sub w)
                                                                        hreserve1Eq)
                                                                (by simpa [feeToWord] using hfeeToZero)
                                                                hkLastNonzero
                                                                (by
                                                                  simpa [totalSupplyCleared] using
                                                                    htotalZero)
                                                                hfit
                                                                (by
                                                                  simpa [memFee, σCleared,
                                                                    totalSupplyCleared] using
                                                                    hbalanceOverflow)
                                                          · by_cases hinitialProductOverflow :
                                                              (UInt256.land feeToWord solcAddrMask =
                                                                  ⟨0⟩ ∧
                                                                mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                                totalSupply = ⟨0⟩ ∧
                                                                UInt256.size ≤
                                                                  amount0.toNat * amount1.toNat) ∨
                                                              (UInt256.land feeToWord solcAddrMask ≠
                                                                  ⟨0⟩ ∧
                                                                mintFeeKLastSlotWord σFee I = ⟨0⟩ ∧
                                                                totalSupply = ⟨0⟩ ∧
                                                                UInt256.size ≤
                                                                  amount0.toNat * amount1.toNat) ∨
                                                              (UInt256.land feeToWord solcAddrMask =
                                                                  ⟨0⟩ ∧
                                                                mintFeeKLastSlotWord σFee I ≠ ⟨0⟩ ∧
                                                                totalSupplyCleared = ⟨0⟩ ∧
                                                                UInt256.size ≤
                                                                  amount0.toNat * amount1.toNat)
                                                            · exact
                                                                uniswapMintInitialProductOverflowFromFactoryCases
                                                                  feeTo hcode hdispatch hsz36 hwv
                                                                  hunlockedSolm hguard0 hguard1 hcall0
                                                                  hdec0 hcall1 hdec1 hle0Source
                                                                  hle1Source hfeeGuard hfeeCall hfeeDec
                                                                  (by simp [feeTo]) hPostAccountsFee
                                                                  henvFeeI hperm rd7781 ho32 hoSize
                                                                  ho132 ho1Size houtFeeSize hzFeeTrue
                                                                  houtFee32 hkLastEq htotalEq
                                                                  (by
                                                                    simpa [mintAmount0Word, amount0,
                                                                      evmS] using
                                                                        congrArg (fun w =>
                                                                          balance0.sub w) hreserve0Eq)
                                                                  (by
                                                                    simpa [mintAmount1Word, amount1,
                                                                      evmS] using
                                                                        congrArg (fun w =>
                                                                          balance1.sub w) hreserve1Eq)
                                                                  (by
                                                                    simpa [feeToWord, totalSupply,
                                                                      totalSupplyCleared] using
                                                                      hinitialProductOverflow)
                                                            · by_cases hproductOverflow :
                                                                mintProportionalProductOverflowCase
                                                                  feeToWord totalSupply totalSupplyCleared
                                                                  amount0 amount1 reserve0 reserve1 σFee I
                                                              · exact
                                                                  uniswapMintProportionalProductOverflowFromFactoryCases
                                                                    feeTo hcode hdispatch hsz36 hperm
                                                                    hwv hunlockedSolm hguard0 hguard1
                                                                    hcall0 hdec0 hcall1 hdec1
                                                                    hle0Source hle1Source hfeeGuard
                                                                    hfeeCall hfeeDec (by simp [feeTo])
                                                                    hPostAccountsFee henvFeeI (by rfl)
                                                                    rd7781 ho32 hoSize ho132 ho1Size
                                                                    houtFeeSize hzFeeTrue houtFee32
                                                                    hkLastEq htotalEq (by rfl) (by rfl)
                                                                    hreserve0Eq hreserve1Eq (by rfl)
                                                                    (by rfl)
                                                                    (by
                                                                      simpa [mintAmount0Word, amount0,
                                                                        evmS] using
                                                                          congrArg (balance0.sub ·)
                                                                            hreserve0Eq)
                                                                    (by
                                                                      simpa [mintAmount1Word, amount1,
                                                                        evmS] using
                                                                          congrArg (balance1.sub ·)
                                                                            hreserve1Eq)
                                                                    (by rfl)
                                                                    (by
                                                                      simpa
                                                                        [mintProportionalProductOverflowCase,
                                                                          feeToWord, totalSupply,
                                                                          totalSupplyCleared, amount0,
                                                                          amount1, reserve0, reserve1]
                                                                        using hproductOverflow)
                                                              · by_cases hsecondMintOverflow :
                                                                mintProportionalSecondMintOverflowCase
                                                                  feeToWord totalSupply totalSupplyCleared
                                                                  amount0 amount1 balance0 balance1 reserve0 reserve1
                                                                  liquidity liquidityCleared σFee
                                                                  σCleared evmFeeS I (mintToMaskedWord I)
                                                                  memFee
                                                                · exact
                                                                    uniswapMintProportionalSecondMintOverflowFromFactoryCases
                                                                      feeTo hcode hdispatch hsz36 hperm
                                                                      hwv hunlockedSolm hguard0 hguard1
                                                                      hcall0 hdec0 hcall1 hdec1
                                                                      hle0Source hle1Source hfeeGuard
                                                                      hfeeCall hfeeDec (by simp [feeTo])
                                                                      hPostAccountsFee henvFeeI (by rfl)
                                                                      rd7781 ho32 hoSize ho132 ho1Size
                                                                      houtFeeSize hzFeeTrue houtFee32
                                                                      hkLastEq htotalEq (by rfl) (by rfl)
                                                                      (by rfl) (by rfl) hreserve0Eq
                                                                      hreserve1Eq
                                                                      (by
                                                                        simpa [mintAmount0Word, amount0,
                                                                          evmS] using
                                                                            congrArg (balance0.sub ·)
                                                                              hreserve0Eq)
                                                                      (by
                                                                        simpa [mintAmount1Word, amount1,
                                                                          evmS] using
                                                                            congrArg (balance1.sub ·)
                                                                              hreserve1Eq)
                                                                      (by
                                                                        simpa
                                                                          [mintProportionalSecondMintOverflowCase,
                                                                            feeToWord, totalSupply,
                                                                            totalSupplyCleared, amount0,
                                                                            amount1, balance0, balance1,
                                                                            reserve0, reserve1, σCleared,
                                                                            memFee]
                                                                        using hsecondMintOverflow)
                                                                · by_cases hfeeOnKLastNonzeroSuccess :
                                                                    mintFeeOnKLastNonzeroSuccessFromFactoryCasesData
                                                                      feeTo feeToWord totalSupply amount0 amount1
                                                                      balance0 balance1 reserve0 reserve1
                                                                      (mintToMaskedWord I) liquidity σFee evmFeeS I
                                                                      memFee
                                                                  · exact
                                                                      uniswapMintFeeOnKLastNonzeroSuccessFromFactoryCases
                                                                        feeTo hcode hdispatch hsz36 hperm
                                                                        hwv hunlockedSolm hguard0 hguard1
                                                                        hcall0 hdec0 hcall1 hdec1
                                                                        hle0Source hle1Source hfeeGuard
                                                                        hfeeCall hfeeDec hPostAccountsFee
                                                                        henvFeeI hcreatedFee hreserve0Eq
                                                                        hreserve1Eq rfl rfl
                                                                        (by
                                                                          simpa [mintAmount0Word, amount0,
                                                                            evmS] using
                                                                              congrArg (balance0.sub ·)
                                                                                hreserve0Eq)
                                                                        (by
                                                                          simpa [mintAmount1Word, amount1,
                                                                            evmS] using
                                                                              congrArg (balance1.sub ·)
                                                                                hreserve1Eq)
                                                                        hkLastEq rfl
                                                                        (by simpa [totalSupply] using
                                                                          htotalEq)
                                                                        rd7781 ho32 hoSize ho132 ho1Size
                                                                        houtFeeSize hzFeeTrue houtFee32
                                                                        rfl rfl rfl rfl rfl
                                                                        (by
                                                                          simpa [feeToWord, totalSupply,
                                                                            liquidity, memFee] using
                                                                            hfeeOnKLastNonzeroSuccess)
                                                                  · by_cases hfeeOnKLastNonzeroInitial :
                                                                      mintFeeOnKLastNonzeroInitialOverflowFromFactoryCasesData
                                                                        feeToWord reserve0 reserve1
                                                                        amount0 amount1 balance0
                                                                        balance1 σFee evmFeeS
                                                                        (uniswapLockEnteredState evmS) I
                                                                        memFee
                                                                    · exact
                                                                        uniswapMintFeeOnKLastNonzeroInitialOverflowFromFactoryCases
                                                                          feeTo hcode hdispatch hsz36
                                                                          hperm hwv hunlockedSolm hguard0
                                                                          hguard1 hcall0 hdec0 hcall1 hdec1
                                                                          hle0Source hle1Source hfeeGuard
                                                                          hfeeCall hfeeDec hPostAccountsFee
                                                                          henvFeeI hcreatedFee hreserve0Eq
                                                                          hreserve1Eq rfl rfl
                                                                          (by
                                                                            simpa [mintAmount0Word, amount0,
                                                                              evmS] using
                                                                                congrArg (balance0.sub ·)
                                                                                  hreserve0Eq)
                                                                          (by
                                                                            simpa [mintAmount1Word, amount1,
                                                                              evmS] using
                                                                                congrArg (balance1.sub ·)
                                                                                  hreserve1Eq)
                                                                          hkLastEq htotalEq rd7781 ho32
                                                                          hoSize ho132 ho1Size houtFeeSize
                                                                          hzFeeTrue houtFee32 rfl rfl rfl
                                                                          rfl hfeeOnKLastNonzeroInitial
                                                                    · by_cases hrootArithmetic : mintFeeOnKLastNonzeroRootArithmeticOverflowFromFactoryCaseData feeToWord σFee evmFeeS I
                                                                      · exact uniswapMintFeeOnKLastNonzeroRootArithmeticOverflowFromFactoryCase feeTo hcode hdispatch hsz36 hwv hunlockedSolm hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hreserve0Eq hreserve1Eq rfl rfl hkLastEq htotalEq rd7781 ho32 hoSize ho132 ho1Size houtFeeSize hzFeeTrue houtFee32 rfl rfl rfl hrootArithmetic
                                                                      · by_cases htotalZeroFinal : totalSupply = ⟨0⟩
                                                                        · by_cases hfeeToNonzeroFinal :
                                                                            UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩
                                                                          · by_cases hkLastNonzeroFinal :
                                                                              mintFeeKLastSlotWord σFee I ≠ ⟨0⟩
                                                                            · -- WIP: broken by the Reasoning library port.
                                                                              exact sorry
                                                                            · -- WIP: broken by the Reasoning library port.
                                                                              exact sorry
                                                                          · -- WIP: broken by the Reasoning library port.
                                                                            exact sorry
                                                                        · by_cases hfeeToNonzeroFinal :
                                                                            UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩
                                                                          · by_cases hkLastNonzeroFinal :
                                                                              mintFeeKLastSlotWord σFee I ≠ ⟨0⟩
                                                                            · -- WIP: broken by the Reasoning library port —
                                                                              -- simp_all diverges on drift-spelled state hyps.
                                                                              exact sorry
                                                                            · -- WIP: broken by the Reasoning library port.
                                                                              exact sorry
                                                                          · -- WIP: broken by the Reasoning library port.
                                                                            exact sorry
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
