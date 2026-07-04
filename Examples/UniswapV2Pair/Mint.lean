import Examples.UniswapV2Pair.MintRuntimeFinalize

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_mint_none_short (I := I) hsz4 hshort
  exact (uniswapMintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapMintBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1041⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS] using
      (initState_codeOwner_storageLoad_ne_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot := ⟨12⟩) (val := ⟨1⟩) hAccounts hlocked)
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact uniswapMintBodyReverts_locked evmS I
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact (uniswapMintX_locked (g := Sat256.ofUInt256 g) hlocked
      (uniswapMintX_decoded_masked (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

theorem uniswapMintBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
  exact uniswapMintBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapMintBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ rfl hsel
  exact uniswapMintBodyCoreRevert_locked hcode hsize hwv hsz36 hlocked hdispatch
    (uniswapReachMintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

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
        uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
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
            uniswapSkimFirstBalanceTypedCall_source
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
                    some (uniswapUint256Value balance0) := by
                simpa [balance0, skimBalanceValue, uniswapUint256Value] using
                  uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
              obtain ⟨_, _, rd3505⟩ := hcont hzTrue ho32
              obtain ⟨_, _, rd3573⟩ :=
                uniswapMintRuntimeSecondBalanceOfExtcodesizeFromFirst rd3505 ho32 hoSize
              by_cases htoken1NoCode :
                uniswapExtCodeSizeWord σ'
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
                          some (uniswapUint256Value balance1) := by
                      simpa [balance1, skimBalanceValue, uniswapUint256Value] using
                        uniswapSkimBalanceOfDecode_ok (returndata := o1) ho132
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
                        sorry
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
