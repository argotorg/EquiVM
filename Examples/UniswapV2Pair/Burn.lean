import Examples.UniswapV2Pair.BurnUpdatedBalanceCases
import Examples.UniswapV2Pair.BurnUpdatedBalance1Runtime
import Examples.UniswapV2Pair.BurnAfterUpdateCases
import Examples.UniswapV2Pair.PairReturnEncoding
import Examples.UniswapV2Pair.UpdateDynamicCallRuntimeCases
import Examples.UniswapV2Pair.BalanceCallMemory
import Examples.UniswapV2Pair.SafeTransferFinalMemory
import Examples.UniswapV2Pair.BurnTransfersSource
import Examples.UniswapV2Pair.BurnSecondBalanceRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1500000 in
theorem uniswapBurnBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some burnTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩
    · exact uniswapBurnBodyRevert_locked hcode hsize hwv hsel hsz36 hlocked hdispatch
        hAccounts
    · have hunlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
          ⟨1⟩ := by
        exact not_not.mp hlocked
      have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1163⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ_evm) k C :=
        uniswapReachBurnBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapBurnX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz36 hsize hreach
      have hlockEntered := uniswapBurnX_lockEntered (g := Sat256.ofUInt256 g)
        hperm hunlocked hdecoded
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hunlockedSolm :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
        have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
        simpa [evmS, initState] using hword.symm.trans hunlocked
      obtain ⟨_, _, rd4179⟩ := hlockEntered
      obtain ⟨_, _, rd4267⟩ := uniswapBurnRuntimeFirstBalanceOfExtcodesize rd4179
      have hpost : accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
          (uniswapLockEnteredState evmS).accountMap := by
        simpa only [uniswapLockEnteredState, uniswapUnlockedState, storageStore_accountMap,
          evmS, initState] using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
      have he : (uniswapLockEnteredState evmS).executionEnv = I := by
        simp only [uniswapLockEnteredState, uniswapUnlockedState, storageStore_executionEnv,
          evmS, initState]
      have hguard := evalExpr_uniswap_codeGuard hpost
        (uniswapAddressAtSlot_eq_runtime ⟨6⟩ hpost he)
        (show evalExpr? config
          { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evmS) I }
          (uniswapLockEnteredState evmS) (.var "_token0") =
            .ok (.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)) from by
              simp only [evalExpr?, EvalResult.ofOption, burnCacheStore_token0])
      by_cases hnoCode : extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
          (UInt256.land solcAddrMask
            (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) = ⟨0⟩
      · have hbody := uniswapBurnBodyReverts_firstNoCode evmS I
          (by simpa only [evmS, initState] using hwv) hunlockedSolm
          (by simpa only [hnoCode] using hguard)
        exact (uniswapBurnRuntimeFirstBalanceOfMissingCodeReverts rd4267 hnoCode
          (by simp only [List.length_cons, List.length_nil]; omega)).reEquivExecutionRevert
            hcode hdispatch (uniswapDecode_burn_ok hsz36) hbody
      · have hpositive : 0 < (extCodeSizeWord
            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I))).toNat := by
          exact Nat.pos_of_ne_zero (fun hz => hnoCode (uint256_toNat_eq_zero hz))
        simp only [hpositive, decide_true] at hguard
        let evmL := uniswapLockEnteredState evmS
        let locals := burnCacheStore evmL I
        have hreceiver : evalExpr? config { contract := contract, locals := locals } evmL
            (.var "_token0") = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
          simp only [locals, evalExpr?, EvalResult.ofOption, burnCacheStore_token0]
        have hargs := evalExprs_uniswap_this_single evmL locals
        by_cases hdepth : I.depth.val < 1024
        · obtain ⟨cA0, σ0, z, out, A_in, callGas, hΘ, hrev, hshortRev, hcont, houtSize⟩ :=
            uniswapBurnRuntimeFirstBalanceOfResultBranchesOfTail rd4267 hdepth hnoCode
              (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨evm0, hcallRaw, ha0, hc0, hs0, hg0, hb0, he0⟩ :=
            uniswapBalanceTypedCallFromState_source (evm1S := evmL) (inOff := ⟨128⟩)
              hpost
              (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                storageStore_createdAccounts, evmS, initState])
              (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                balanceCallStorageStore_sigma0, evmS, initState])
              (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                balanceCallStorageStore_genesisBlockHeader, evmS, initState])
              (by simp only [evmL, uniswapLockEnteredState, uniswapUnlockedState,
                balanceCallStorageStore_blocks, evmS, initState])
              he hdepth (balanceOfThisCalldataMem_encode I.codeOwner) hΘ
          have hcall : typedCallViaEVM config evmL
              (EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)) "balanceOf" 0
              [.address evmL.executionEnv.codeOwner] (z, evm0, out) false := by
            rw [balanceCallAddress_self, uniswapAddressAtSlot_eq_runtime ⟨6⟩ hpost he]
            exact hcallRaw
          cases hz : z with
          | false =>
            have hfirst := checkedExternalCallFailure (retVar := "balance0")
              hguard hreceiver hargs (by simpa only [hz] using hcall)
            exact (hrev hz).reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
              (uniswapBurnBodyReverts_firstBalanceBlock evmS I
                (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst)
          | true =>
            have hcall0 : typedCallViaEVM config evmL
                (EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)) "balanceOf" 0
                [.address evmL.executionEnv.codeOwner] (true, evm0, out) false := by
              simpa only [hz] using hcall
            by_cases hshort : out.size < 32
            · have hdec : config.externalABI.decode? "balanceOf" out = none := by
                change uniswapExternalABI.decode? "balanceOf" out = none
                simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                  decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort
              have hfirst := checkedExternalCallDecodeRevert (retVar := "balance0")
                hguard hreceiver hargs hcall0 hdec
              exact (hshortRev hz hshort).reEquivExecutionRevert hcode hdispatch
                (uniswapDecode_burn_ok hsz36)
                (uniswapBurnBodyReverts_firstBalanceBlock evmS I
                  (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst)
            · have hout32 : 32 ≤ out.size := by omega
              obtain ⟨_, _, rd4324⟩ := hcont hz hout32
              let balance0 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
              let token1 := UInt256.land solcAddrMask
                (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
              have hdec0 : config.externalABI.decode? "balanceOf" out =
                  some [uniswapUint256Value balance0] := uniswapBalanceOfDecode_ok hout32
              have hfirst : ExecBlock config { contract := contract, locals := locals } evmL
                  (balanceOfThisStmts (.var "_token0") "balance0")
                  (.ok { contract := contract, locals := burnBalance0Store evmL I balance0 } evm0) :=
                checkedExternalCallSuccess (value := [uniswapUint256Value balance0])
                  (retVar := "balance0") hguard hreceiver hargs hcall0 hdec0
              obtain ⟨_, _, rd4387⟩ := uniswapBurnRuntimeSecondBalanceOfExtcodesize
                rd4324 hout32 houtSize (by simp only [List.length_cons, List.length_nil]; omega)
              have hclean1 : UInt256.land token1 solcAddrMask = token1 := by
                rw [u256_land_comm token1 solcAddrMask]
                exact u256_land_solcAddrMask_idem_left _
              dsimp only [token1] at hclean1
              simp only [hclean1] at rd4387
              have haddr1 : uniswapAddressAtSlot evmL ⟨7⟩ = AccountAddress.ofUInt256 token1 :=
                uniswapAddressAtSlot_eq_runtime ⟨7⟩ hpost he
              have hget1 : (burnBalance0Store evmL I balance0).get? "_token1" =
                  some (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
                rw [burnBalance0Store, store_get_ne _ _ (by decide), burnCacheStore_token1]
              have hreceiver1 : evalExpr? config
                  { contract := contract, locals := burnBalance0Store evmL I balance0 }
                  evm0 (.var "_token1") = .ok (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
                simp only [evalExpr?, EvalResult.ofOption, hget1]
              have hguard1 := evalExpr_uniswap_codeGuard ha0 haddr1 hreceiver1
              have hargs1 := evalExprs_uniswap_this_single evm0 (burnBalance0Store evmL I balance0)
              by_cases hnoCode1 : extCodeSizeWord σ0 token1 = ⟨0⟩
              · have hsecond := checkedExternalCallVarNoCode (retVar := "balance1")
                  (name := "balanceOf") (sendVal := 0) (args := [this]) (perm := false)
                  (by simpa only [hnoCode1] using hguard1)
                exact (uniswapBurnRuntimeSecondBalanceOfMissingCodeReverts rd4387 hnoCode1
                  (by simp only [List.length_cons, List.length_nil]; omega)).reEquivExecutionRevert
                    hcode hdispatch (uniswapDecode_burn_ok hsz36)
                    (uniswapBurnBodyReverts_secondBalanceBlock evmS evm0 I balance0
                      (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst hsecond)
              · have hpos1 : 0 < (extCodeSizeWord σ0 token1).toNat :=
                  Nat.pos_of_ne_zero (fun hz => hnoCode1 (uint256_toNat_eq_zero hz))
                simp only [hpos1, decide_true] at hguard1
                obtain ⟨cA1, σ1, z1, out1, A_in1, callGas1, hΘ1, hrev1, hshortRev1,
                    hcont1, hout1Size⟩ := uniswapBurnRuntimeSecondBalanceOfResultBranchesOfTail
                  rd4387 hdepth hnoCode1 hout32 houtSize
                  (by simp only [List.length_cons, List.length_nil]; omega)
                have he0I := he0.trans he
                obtain ⟨evm1, hcallRaw1, ha1, hc1, hs1, hg1, hb1, he1⟩ :=
                  uniswapBalanceTypedCallFromState_source (evm1S := evm0) (inOff := ⟨128⟩)
                    ha0 hc0 hs0 hg0 hb0 he0I hdepth
                    (balanceOfThisRebuiltCalldataMem_encode I.codeOwner out hout32 houtSize) hΘ1
                have hcall1 : typedCallViaEVM config evm0
                    (EVM.address (uniswapAddressAtSlot evmL ⟨7⟩)) "balanceOf" 0
                    [.address evm0.executionEnv.codeOwner] (z1, evm1, out1) false := by
                  rw [balanceCallAddress_self, haddr1]
                  exact hcallRaw1
                cases hz1 : z1 with
                | false =>
                  have hsecond := checkedExternalCallFailure (retVar := "balance1")
                    hguard1 hreceiver1 hargs1 (by simpa only [hz1] using hcall1)
                  exact (hrev1 hz1).reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                    (uniswapBurnBodyReverts_secondBalanceBlock evmS evm0 I balance0
                      (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst hsecond)
                | true =>
                  have hcall1True : typedCallViaEVM config evm0
                      (EVM.address (uniswapAddressAtSlot evmL ⟨7⟩)) "balanceOf" 0
                      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false := by
                    simpa only [hz1] using hcall1
                  by_cases hshort1 : out1.size < 32
                  · have hdec : config.externalABI.decode? "balanceOf" out1 = none := by
                      change uniswapExternalABI.decode? "balanceOf" out1 = none
                      simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                        decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out1) hshort1
                    have hsecond := checkedExternalCallDecodeRevert (retVar := "balance1")
                      hguard1 hreceiver1 hargs1 hcall1True hdec
                    exact (hshortRev1 hz1 hshort1).reEquivExecutionRevert hcode hdispatch
                      (uniswapDecode_burn_ok hsz36)
                      (uniswapBurnBodyReverts_secondBalanceBlock evmS evm0 I balance0
                        (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst hsecond)
                  · have hout132 : 32 ≤ out1.size := by omega
                    obtain ⟨_, _, rd4444⟩ := hcont1 hz1 hout132
                    let balance1 := UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
                    have hdec1 : config.externalABI.decode? "balanceOf" out1 =
                        some [uniswapUint256Value balance1] := uniswapBalanceOfDecode_ok hout132
                    have hsecond : ExecBlock config
                        { contract := contract, locals := burnBalance0Store evmL I balance0 }
                        evm0 (balanceOfThisStmts (.var "_token1") "balance1")
                        (.ok { contract := contract, locals := burnBalanceStore evmL I balance0 balance1 } evm1) :=
                      checkedExternalCallSuccess (value := [uniswapUint256Value balance1])
                        (retVar := "balance1") hguard1 hreceiver1 hargs1 hcall1True hdec1
                    have hprefix := uniswapBurnBeforeFeePrefix evmS evm0 evm1 I balance0 balance1
                      (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst hsecond
                    have he1I := he1.trans he0I
                    have hbaseSize := balanceOfThisRebuiltStaticcallMem_size_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) out out1 hout32 houtSize hout132 hout1Size
                    have hbaseRead := balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) out out1 hout32 houtSize hout132 hout1Size
                    obtain ⟨_, _, rd7696⟩ := uniswapBurnRuntimeMintFeeEntry rd4444
                      (by simp only [List.length_cons, List.length_nil]; omega)
                    have hliqEq := burnLiquidityWord_eq_runtime ha1 he1I (by rw [hbaseSize]; omega)
                    rw [← hliqEq] at rd7696
                    have hr0 : uniswapReserve0Word evmL =
                        reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
                      simpa only [evmL, evmS] using mintReserve0Word_initState_eq_evm
                        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hAccounts
                    have hr1 : uniswapReserve1Word evmL =
                        reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I := by
                      simpa only [evmL, evmS] using mintReserve1Word_initState_eq_evm
                        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hAccounts
                    have hfeeArgs := evalExprs_burn_mintFeeArgs evmL evm1 I balance0 balance1
                    rw [hr0, hr1] at hfeeArgs
                    have hcleanR0 : UInt256.land
                        (reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                        reserve112Mask = reserve0Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                      reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
                    have hcleanR1 : UInt256.land
                        (reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                        reserve112Mask = reserve1Word (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I :=
                      reserve112Mask_clean_of_lt _ (reserve112Word_lt _)
                    rcases uniswapMintFeeCallRuntimeCasesWithMemory (retVar := "feeOn") evm1 rfl hfeeArgs rd7696
                        ha1 he1I hc1 hs1 hg1 hb1 hdepth hcleanR0 hcleanR1 hperm
                        ((uniswapInternalMintBalanceHashMem_size_of_ge64
                          (UInt256.ofNat I.codeOwner.val) (by rw [hbaseSize]; omega)).trans hbaseSize)
                        (uniswapInternalMintBalanceHashMem_read64_of_ge96
                          (UInt256.ofNat I.codeOwner.val) (by rw [hbaseSize]; omega) hbaseRead)
                        (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega) with
                      ⟨hfee, rdRev⟩ | ⟨feeOn, evmFee, σFee, cAFee, memFee, dataFee, kFee, CFee,
                        hfee, haFee, heFee, hcFee, hsFee, hgFee, hbFee, rd4472, hmFee, h64Fee, h96Fee⟩
                    · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                        (uniswapBurnBodyReverts_mintFeeBlock evmS evm1 I balance0 balance1 hprefix hfee)
                    · have h96FeeZero : memFee.readWithPadding 96 32 = UInt256.toByteArray ⟨0⟩ :=
                        h96Fee.trans ((uniswapInternalMintBalanceHashMem_read96
                          (UInt256.ofNat I.codeOwner.val) (by rw [hbaseSize]; omega)).trans
                          (balanceOfThisRebuiltStaticcallMem_read96_zero
                            (UInt256.ofNat I.codeOwner.val) out out1 hout32 houtSize hout132 hout1Size))
                      obtain ⟨_, _, rd4479⟩ := uniswapBurnRuntimeTotalSupplyLoaded rd4472
                        (by simp only [List.length_cons, List.length_nil]; omega)
                      have htotalEq := mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv haFee heFee
                      rw [← htotalEq] at rd4479
                      have hbeforeAmounts := uniswapBurnBeforeAmountsPrefix evmS evm1 evmFee I
                        balance0 balance1 feeOn hprefix hfee
                      obtain ⟨hliqGet, hb0Get, hb1Get, htotalGet⟩ :=
                        burnTotalSupplyStore_gets evmL evm1 evmFee I balance0 balance1 feeOn
                      rcases uniswapBurnAmountsRuntimeCases evmFee rd4479
                          hliqGet hb0Get hb1Get htotalGet hmFee h64Fee
                          (by simp only [List.length_cons, List.length_nil]; omega) with
                        ⟨hamounts, hfail⟩ | ⟨kAmounts, CAmounts, hamounts, rd4533⟩
                      · have hbody := uniswapBurnBodyReverts_amounts evmS evm1 evmFee I
                          balance0 balance1 feeOn hbeforeAmounts hamounts
                        exact hfail.elim
                          (fun hrev ↦ hrev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_burn_ok hsz36) hbody)
                          (fun hinvalid ↦ hinvalid.reEquivExecutionInvalid hcode hdispatch
                            (uniswapDecode_burn_ok hsz36) hbody)
                      · obtain ⟨hliqAmounts, ha0Amounts, ha1Amounts⟩ :=
                          burnAmountsStore_gets _ _ balance0 balance1 _ hliqGet
                        rcases uniswapBurnAmountsGuardAndBurnCasesWithMemory evmFee rd4533 haFee heFee
                            hliqAmounts ha0Amounts ha1Amounts hperm hmFee h64Fee
                            (by simp only [List.length_cons, List.length_nil]; omega) with
                          ⟨hburn, rdRev⟩ | ⟨memBurn, kBurn, CBurn, hburn, haBurn, rd4617,
                            hmBurn, h64Burn, h96Burn⟩
                        · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                            (uniswapBurnBodyReverts_beforeTransfers evmS I
                              (execBlock_append (execBlock_append hbeforeAmounts hamounts) hburn))
                        · have h96BurnZero : memBurn.readWithPadding 96 32 = UInt256.toByteArray ⟨0⟩ :=
                            h96Burn.trans h96FeeZero
                          have hbeforeTransfers :=
                            execBlock_append (execBlock_append hbeforeAmounts hamounts) hburn
                          let evmBurn := burnFunctionPostState evmFee I.codeOwner (burnLiquidityWord evm1)
                          have heBurn : evmBurn.executionEnv = I := by
                            simpa only [evmBurn, burnFunctionPostState, burnFunctionAfterBalanceState,
                              storageStore_executionEnv] using heFee
                          have hcBurn : evmBurn.createdAccounts = cAFee := by
                            simpa only [evmBurn, burnFunctionPostState, burnFunctionAfterBalanceState,
                              storageStore_createdAccounts] using hcFee
                          have hsBurn : evmBurn.σ₀ = σ₀ := by
                            simpa only [evmBurn, burnFunctionPostState, burnFunctionAfterBalanceState,
                              balanceCallStorageStore_sigma0, initState] using hsFee
                          have hgBurn : evmBurn.genesisBlockHeader = gh := by
                            simpa only [evmBurn, burnFunctionPostState, burnFunctionAfterBalanceState,
                              balanceCallStorageStore_genesisBlockHeader, initState] using hgFee
                          have hbBurn : evmBurn.blocks = bl := by
                            simpa only [evmBurn, burnFunctionPostState, burnFunctionAfterBalanceState,
                              balanceCallStorageStore_blocks, initState] using hbFee
                          obtain ⟨_, _, rd6370⟩ := uniswapBurnRuntimeFirstSafeTransferEntry rd4617
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          have htransferArgs := evalExprs_burn_firstSafeTransferArgs
                            evmL evm1 evmFee evmBurn I balance0 balance1 feeOn
                          have htarget0 : EVM.address (uniswapAddressAtSlot evmL ⟨6⟩) =
                              AccountAddress.ofUInt256 (UInt256.land
                                (UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩
                                  (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) solcAddrMask) := by
                            rw [uniswapAddress_self, uniswapAddressAtSlot_eq_runtime ⟨6⟩ hpost he]
                            exact congrArg AccountAddress.ofUInt256
                              ((u256_land_comm _ solcAddrMask).trans
                                (u256_land_solcAddrMask_idem_left _)).symm
                          have hrecipient : UInt256.ofNat (AccountAddress.ofNat (burnToWord I).toNat).val =
                              UInt256.land solcAddrMask (burnToMaskedWord I) := by
                            rw [burnToMaskedWord, u256_land_solcAddrMask_idem_left]
                            exact (keyValueToWord_address _).symm.trans
                              (keyValueToWord_address_ofNat_mask (burnToWord I))
                          rcases uniswapSafeTransferCallRuntimeCases (retVar := "ok0") evmBurn
                              (uniswapAddressAtSlot evmL ⟨6⟩) (AccountAddress.ofNat (burnToWord I).toNat)
                              rd6370 haBurn heBurn hcBurn hsBurn hgBurn hbBurn rfl htransferArgs
                              htarget0 hrecipient hdepth hperm hmBurn h64Burn h96BurnZero
                              (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega) with
                            ⟨htransfer0, rdRev⟩ | ⟨evmTransfer0, σTransfer0, cATransfer0, outTransfer0,
                              kTransfer0, CTransfer0, htransfer0, haTransfer0, hcTransfer0, hsTransfer0,
                              hgTransfer0, hbTransfer0, heTransfer0, houtTransfer0, rd4628⟩
                          · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                              (uniswapBurnBodyReverts_firstTransfer evmS evmBurn I _ hbeforeTransfers htransfer0)
                          · obtain ⟨ptr1, hmTransfer0, hgapTransfer0, hptrTransfer0, hbaseTransfer0,
                              hcapTransfer0, hawTransfer0, hawLoTransfer0, h64Transfer0, h96Transfer0⟩ :=
                              safeTransferRuntimeFinalMemory_invariants (burnToMaskedWord I)
                                (burnAmountWord (burnLiquidityWord evm1) balance0 (mintFunctionTotalSupplyWord evmFee))
                                outTransfer0 hmBurn h96BurnZero houtTransfer0
                            obtain ⟨_, _, rd6370Second⟩ := uniswapBurnRuntimeSecondSafeTransferEntry rd4628
                              (by simp only [List.length_cons, List.length_nil]; omega)
                            have htransferArgs1 := evalExprs_burn_secondSafeTransferArgs
                              evmL evm1 evmFee evmTransfer0 I balance0 balance1 feeOn
                            have htarget1 : EVM.address (uniswapAddressAtSlot evmL ⟨7⟩) =
                                AccountAddress.ofUInt256 (UInt256.land
                                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩
                                    (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) solcAddrMask) := by
                              rw [uniswapAddress_self, uniswapAddressAtSlot_eq_runtime ⟨7⟩ hpost he]
                              exact congrArg AccountAddress.ofUInt256
                                ((u256_land_comm _ solcAddrMask).trans
                                  (u256_land_solcAddrMask_idem_left _)).symm
                            rcases uniswapSafeTransferDynamicCallRuntimeCases (ptr := ptr1) (retVar := "ok1") evmTransfer0
                                (uniswapAddressAtSlot evmL ⟨7⟩) (AccountAddress.ofNat (burnToWord I).toNat)
                                rd6370Second haTransfer0 heTransfer0 hcTransfer0 hsTransfer0 hgTransfer0 hbTransfer0
                                rfl htransferArgs1 htarget1 hrecipient hdepth hperm
                                hmTransfer0 hgapTransfer0 hptrTransfer0 hbaseTransfer0 hcapTransfer0
                                hawTransfer0 hawLoTransfer0 h64Transfer0 h96Transfer0
                                (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega) with
                              ⟨htransfer1, rdRev⟩ | ⟨evmTransfer1, σTransfer1, cATransfer1, outTransfer1,
                                kTransfer1, CTransfer1, htransfer1, haTransfer1, hcTransfer1, hsTransfer1,
                                hgTransfer1, hbTransfer1, heTransfer1, houtTransfer1, rd4639⟩
                            · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                                (uniswapBurnBodyReverts_secondTransfer evmS evmBurn evmTransfer0 I _
                                  hbeforeTransfers htransfer0 htransfer1)
                            · have hfitTransfer1 : ptr1.toNat + outTransfer1.size + 355 < UInt256.size := by
                                have hnum : 2 ^ 255 + 1024 + 2 ^ 138 + 355 < UInt256.size := by native_decide
                                omega
                              obtain ⟨ptr2, hmTransfer1, hgapTransfer1, hptrTransfer1, hbaseTransfer1,
                                hcapTransfer1, hawTransfer1, hawLoTransfer1, h64Transfer1, h96Transfer1⟩ :=
                                safeTransferDynamicFinalMemory_invariants
                                  (safeTransferRuntimeFinalActiveWords outTransfer0) ptr1 (burnToMaskedWord I)
                                  (burnAmountWord (burnLiquidityWord evm1) balance1 (mintFunctionTotalSupplyWord evmFee))
                                  outTransfer1 hmTransfer0 hgapTransfer0 hptrTransfer0 hbaseTransfer0
                                  hawTransfer0 hfitTransfer1 h96Transfer0
                              have hfitPtr2 : ptr2.toNat + 67 < UInt256.size := by omega
                              have hbeforeBalances := uniswapBurnBeforeUpdatedBalancesPrefix evmS evmBurn evmTransfer0
                                evmTransfer1 I _ hbeforeTransfers htransfer0 htransfer1
                              let localsTransfers := burnAfterTransfersStore (burnAfterInternalStore evmL evm1 evmFee I balance0 balance1 feeOn)
                              obtain ⟨hgetToken0, hgetToken1⟩ := burnAfterTransfersStore_tokens evmL evm1 evmFee I balance0 balance1 feeOn
                              have hreceiver2 : evalExpr? config { contract := contract, locals := localsTransfers }
                                  evmTransfer1 (.var "_token0") = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
                                simp only [localsTransfers, evalExpr?, EvalResult.ofOption, hgetToken0]
                              obtain ⟨_, _, rd4697⟩ := RD.uniswapBurnUpdatedBalance0Prepared rd4639
                                (le_trans (by decide) hmTransfer1) hgapTransfer1 (by omega) hawTransfer1 (by omega) hfitPtr2 h64Transfer1
                                (by simp only [List.length_cons, List.length_nil]; omega)
                              rcases uniswapBurnUpdatedBalanceCallRuntimeCases (second := false)
                                  evmTransfer1 (uniswapAddressAtSlot evmL ⟨6⟩) localsTransfers "_token0" "newBalance0"
                                  rd4697 haTransfer1 heTransfer1 hcTransfer1 hsTransfer1 hgTransfer1 hbTransfer1 hreceiver2
                                  (by simpa only [uniswapAddress_self] using htarget0) hdepth
                                  (le_trans (by decide) hmTransfer1) hgapTransfer1 (by omega) hawTransfer1 hfitPtr2 h64Transfer1
                                  (by simp only [List.length_cons, List.length_nil]; omega) with
                                ⟨hbalance2, rdRev⟩ | ⟨evmBalance2, σBalance2, cABalance2, outBalance2, kBalance2, CBalance2,
                                  hbalance2, haBalance2, hcBalance2, hsBalance2, hgBalance2, hbBalance2, heBalance2,
                                  houtBalance2Lo, houtBalance2, rd4754⟩
                              · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                                  (uniswapBurnBodyReverts_updatedBalance0 evmS evmTransfer1 I _ hbeforeBalances hbalance2)
                              · let memTransfer1 := safeTransferDynamicFinalMem
                                  (safeTransferRuntimeFinalMem memBurn (burnToMaskedWord I)
                                    (burnAmountWord (burnLiquidityWord evm1) balance0 (mintFunctionTotalSupplyWord evmFee)) outTransfer0)
                                  ptr1 (burnToMaskedWord I)
                                  (burnAmountWord (burnLiquidityWord evm1) balance1 (mintFunctionTotalSupplyWord evmFee)) outTransfer1
                                let wordsTransfer1 := safeTransferDynamicFinalWords (safeTransferRuntimeFinalActiveWords outTransfer0) ptr1 outTransfer1
                                have hmemSizeBalance2 : (balanceDynamicReturnMem memTransfer1 ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2).size =
                                    max memTransfer1.size (ptr2.toNat + 36) :=
                                  balanceDynamicReturnMem_size ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2 hgapTransfer1 (by omega) houtBalance2
                                have hgapBalance2 : ptr2.toNat -
                                    (balanceDynamicReturnMem memTransfer1 ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2).size < USize.size := by
                                  rw [hmemSizeBalance2]
                                  have hu : 0 < USize.size := lt_usize 0 (by omega)
                                  omega
                                have hmBalance2 : 128 ≤ (balanceDynamicReturnMem memTransfer1 ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2).size := by
                                  rw [hmemSizeBalance2]; omega
                                have h64Balance2 := (balanceDynamicReturnMem_read_below ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2 64
                                  (le_trans (by decide) hmTransfer1) (by omega) hgapTransfer1 (by omega) houtBalance2).trans h64Transfer1
                                obtain ⟨_, hawBalance2, hcoverBalance2⟩ := balanceDynamicWords_bounds wordsTransfer1 ptr2 hawTransfer1 hfitPtr2
                                let newBalance0 := UInt256.ofNat (fromByteArrayBigEndian (outBalance2.extract 0 32))
                                let localsBalance0 := localsTransfers.insert "newBalance0" (uniswapUint256Value newBalance0)
                                have hreceiver3 : evalExpr? config { contract := contract, locals := localsBalance0 }
                                    evmBalance2 (.var "_token1") = .ok (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
                                  simp only [localsBalance0, localsTransfers, evalExpr?, EvalResult.ofOption,
                                    store_get_ne _ (k := "newBalance0") (a := "_token1") _ (by decide), hgetToken1]
                                obtain ⟨_, _, rd4815⟩ := RD.uniswapBurnUpdatedBalance1Prepared rd4754
                                  (le_trans (by decide) hmBalance2) hgapBalance2 (by omega) hawBalance2 (le_trans (by omega) hcoverBalance2) hfitPtr2 h64Balance2
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                                rcases uniswapBurnUpdatedBalanceCallRuntimeCases (second := true)
                                    evmBalance2 (uniswapAddressAtSlot evmL ⟨7⟩) localsBalance0 "_token1" "newBalance1"
                                    rd4815 haBalance2 heBalance2 hcBalance2 hsBalance2 hgBalance2 hbBalance2 hreceiver3
                                    (by simpa only [uniswapAddress_self] using htarget1) hdepth
                                    (le_trans (by decide) hmBalance2) hgapBalance2 (by omega) hawBalance2 hfitPtr2 h64Balance2
                                    (by simp only [List.length_cons, List.length_nil]; omega) with
                                  ⟨hbalance3, rdRev⟩ | ⟨evmBalance3, σBalance3, cABalance3, outBalance3, kBalance3, CBalance3,
                                    hbalance3, haBalance3, hcBalance3, hsBalance3, hgBalance3, hbBalance3, heBalance3,
                                    houtBalance3Lo, houtBalance3, rd4872⟩
                                · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                                    (uniswapBurnBodyReverts_beforeUpdate evmS I
                                      (execBlock_append (execBlock_append hbeforeBalances hbalance2) hbalance3))
                                · have hbeforeUpdate := execBlock_append (execBlock_append hbeforeBalances hbalance2) hbalance3
                                  obtain ⟨_, _, rd6959⟩ := RD.uniswapBurnUpdateEntry rd4872
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                  let memBalance2 := balanceDynamicReturnMem memTransfer1 ptr2 (UInt256.ofNat I.codeOwner.val) outBalance2
                                  let memBalance3 := balanceDynamicReturnMem memBalance2 ptr2 (UInt256.ofNat I.codeOwner.val) outBalance3
                                  have hmemSizeBalance3 : memBalance3.size = max memBalance2.size (ptr2.toNat + 36) :=
                                    balanceDynamicReturnMem_size ptr2 (UInt256.ofNat I.codeOwner.val) outBalance3 hgapBalance2 (by omega) houtBalance3
                                  have hgapBalance3 : ptr2.toNat - memBalance3.size < USize.size := by
                                    rw [hmemSizeBalance3]
                                    have hu : 0 < USize.size := lt_usize 0 (by omega)
                                    omega
                                  have hmBalance3 : 96 ≤ memBalance3.size := by rw [hmemSizeBalance3]; omega
                                  have h64Balance3 := (balanceDynamicReturnMem_read_below ptr2 (UInt256.ofNat I.codeOwner.val) outBalance3 64
                                    (le_trans (by decide) hmBalance2) (by omega) hgapBalance2 (by omega) houtBalance3).trans h64Balance2
                                  obtain ⟨_, hawBalance3, hcoverBalance3⟩ := balanceDynamicWords_bounds
                                    (balanceDynamicCalldataWords wordsTransfer1 ptr2) ptr2 hawBalance2 hfitPtr2
                                  have hfitUpdate : ptr2.toNat + 131 < UInt256.size := by
                                    have hnum : 2 ^ 255 + 1024 + 2 ^ 138 + 358 < UInt256.size := by native_decide
                                    omega
                                  let newBalance1 := UInt256.ofNat (fromByteArrayBigEndian (outBalance3.extract 0 32))
                                  have hargsUpdate := evalExprs_burn_updateArgs evmL evm1 evmFee evmBalance3 I
                                    balance0 balance1 feeOn newBalance0 newBalance1
                                  rw [hr0, hr1] at hargsUpdate
                                  rcases uniswapUpdateCallRuntimeCases_dynamic (retVar := "_updateResult") evmBalance3 rd6959
                                      haBalance3 heBalance3 hargsUpdate hcleanR0 hcleanR1 hperm hmBalance3
                                      (by omega) hgapBalance3 hfitUpdate hawBalance3 (le_trans (by omega) hcoverBalance3)
                                      h64Balance3 (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega) with
                                    ⟨hupdate, rdRev⟩ | ⟨evmUpdate, σUpdate, packedUpdate, kUpdate, CUpdate,
                                      hupdate, haUpdate, heUpdate, hcUpdate, rd4885, hmemSizeUpdate, h64Update⟩
                                  · exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_burn_ok hsz36)
                                      (uniswapBurnBodyReverts_updateCall evmS evmBalance3 I _ hbeforeUpdate hupdate)
                                  · let memUpdate := pairDynamicMem memBalance3 ptr2
                                      (uniswapSyncReserve0Word packedUpdate) (uniswapSyncReserve1Word packedUpdate)
                                    change memUpdate.size = max memBalance3.size (ptr2.toNat + 64) at hmemSizeUpdate
                                    have hmUpdate : 96 ≤ memUpdate.size := by rw [hmemSizeUpdate]; omega
                                    have hgapUpdate : ptr2.toNat - memUpdate.size < USize.size := by
                                      rw [hmemSizeUpdate]
                                      have hz : 0 < USize.size := lt_usize 0 (by omega)
                                      omega
                                    obtain ⟨hawUpdate, hcoverUpdate⟩ := pairDynamicWords_bounds
                                      (balanceDynamicCalldataWords (balanceDynamicCalldataWords wordsTransfer1 ptr2) ptr2)
                                      ptr2 hawBalance3 (by omega)
                                    obtain ⟨_, _, _, _, hfeeUpdate, ha0Update, ha1Update⟩ :=
                                      burnBeforeUpdateStore_gets evmL evm1 evmFee I balance0 balance1 feeOn newBalance0 newBalance1
                                    obtain ⟨hr0Base, hr1Base, hkBase, huBase⟩ :=
                                      burnAfterUpdateStore_bases evmL evm1 evmFee I balance0 balance1 feeOn newBalance0 newBalance1
                                    obtain ⟨evmFinal, σFinal, htail, haFinal, hcFinal, rdRet⟩ :=
                                      uniswapBurnAfterUpdateRuntimeReturns
                                        (locals := (burnBeforeUpdateStore evmL evm1 evmFee I balance0 balance1 feeOn newBalance0 newBalance1).insert
                                          "_updateResult" .unit)
                                        evmUpdate feeOn rd4885 haUpdate heUpdate rfl
                                        (by rw [store_get_ne _ _ (by decide)]; exact hfeeUpdate)
                                        (by rw [store_get_ne _ _ (by decide)]; exact ha0Update)
                                        (by rw [store_get_ne _ _ (by decide)]; exact ha1Update)
                                        hr0Base hr1Base hkBase huBase hmUpdate (by omega) hgapUpdate (by omega)
                                        hawUpdate hcoverUpdate h64Update hperm (by simp only [List.length_cons, List.length_nil]; omega)
                                    have hbody := uniswapBurnBodyReturns_afterUpdate evmS evmBalance3 evmUpdate I _ _ _
                                      hbeforeUpdate hupdate htail
                                    exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                      (uniswapDecode_burn_ok hsz36) hbody
                                      (by rw [hcFinal, hcUpdate, hcBalance3]) haFinal
                                      (returnEquiv.returned rfl (uniswapUint256PairReturnEncoding _ _))
        · have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
          let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
          have hcall : typedCallViaEVM config evmL target "balanceOf" 0
              [.address evmL.executionEnv.codeOwner]
              (false, { evmL with substate := (evmL.addAccessedAccount target).substate },
                ByteArray.empty) false :=
            callNotMade_depthLimit (balanceOfThisCalldataMem_encode evmL.executionEnv.codeOwner)
              (by simpa only [evmL, he] using hdepth1024)
          have hfirst := checkedExternalCallFailure (retVar := "balance0")
            hguard hreceiver hargs hcall
          exact (uniswapBurnRuntimeFirstBalanceOfDepthReverts rd4267 hdepth1024 hnoCode
            (by simp only [List.length_cons, List.length_nil]; omega)).reEquivExecutionRevert
              hcode hdispatch (uniswapDecode_burn_ok hsz36)
              (uniswapBurnBodyReverts_firstBalanceBlock evmS I
                (by simpa only [evmS, initState] using hwv) hunlockedSolm hfirst)
  · exact uniswapBurnBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
