import Benchmarks.Dss.Cure.LoadTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

theorem cureDispatchLoad {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 9)) :
    dispatchMsg contract I.calldata = some loadTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some loadTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes]
  native_decide

theorem cureDecode_load_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (loadTransition.params.map Param.name)
      (transitionSignature loadTransition).paramTypes I.calldata =
        some (loadLocals I) := by
  simpa [config, loadTransition, loadLocals, loadSrc] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "src") hsz36)

theorem cureDecode_load_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (loadTransition.params.map Param.name)
      (transitionSignature loadTransition).paramTypes I.calldata = none := by
  simpa [config, loadTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "src") hsz4 hshort)

set_option maxHeartbeats 10000000 in
theorem cureLoadBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 9))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 9) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some loadTransition :=
    cureDispatchLoad hsel
  have hreach := cureReachLoadBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (loadTransition.params.map Param.name)
          (transitionSignature loadTransition).paramTypes I.calldata = some (loadLocals I) :=
      cureDecode_load_ok hsz36
    let key := loadKey I
    let locals := loadLocals I
    have hliveWord :
        cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hposWord :
        cureSlotWord (loadPosSlotFor I) σ_evm I =
          cureSlotWord (loadPosSlotFor I) σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner (loadPosSlotFor I) ⟨0⟩
    have hposSlotEq : loadPosSlotFor I = solcMappingSlot ⟨5⟩ key := by
      simpa [key] using loadPosSlotFor_eq I
    obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
      (code := cureBytecode) (sel := sel) (entry := ⟨486⟩) (ret := ⟨484⟩)
      (decoded := ⟨508⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) hsz36 hsize
    obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
      (code := cureBytecode) (decoded := ⟨508⟩) (ret := ⟨484⟩) (routine := ⟨1348⟩)
      (R := [sel]) hdecoded
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
    by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨0⟩
    · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨0⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ = ⟨0⟩ := by
        simpa [cureSlotWord] using hliveEvm
      obtain ⟨_, _, hafterLive⟩ := RD.cureLoadLiveZeroOk
        (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, loadKey] using hroutine)
        hliveSolc (by simp)
      by_cases hposEvm : cureSlotWord (loadPosSlotFor I) σ_evm I = ⟨0⟩
      · have hposSolm : cureSlotWord (loadPosSlotFor I) σ_solm I = ⟨0⟩ := by
          rw [← hposWord]
          exact hposEvm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
          simpa [evm0, locals] using
            (cureLoadSourceBodyPosZeroRevert (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hliveSolm hposSolm)
        have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) = ⟨0⟩ := by
          rw [← hposSlotEq]
          simpa [cureSlotWord] using hposEvm
        have hcanonKey : key.toNat < EVM.addressModulus := by
          dsimp [key, loadKey]
          rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
          exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
        have hrev := RD.cureLoadPosZeroRevert
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
          hafterLive hcanonKey hposSolc solcFreePtrMem_size solcFreePtrMem_read64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hposSolm : cureSlotWord (loadPosSlotFor I) σ_solm I ≠ ⟨0⟩ := by
          intro hsolm
          exact hposEvm (by rw [hposWord, hsolm])
        have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
          rw [← hposSlotEq]
          simpa [cureSlotWord] using hposEvm
        have hcanonKey : key.toNat < EVM.addressModulus := by
          dsimp [key, loadKey]
          rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
          exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
        obtain ⟨_, _, hafterPos⟩ := RD.cureLoadPosNonzeroOk
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
          hafterLive hcanonKey hposSolc solcFreePtrMem_size (by simp)
        by_cases hnoCodeEvm : extCodeSizeWord σ_evm key = ⟨0⟩
        · have hnoCodeSolm : extCodeSizeWord σ_solm key = ⟨0⟩ := by
            have hsame :=
              Reasoning.Theory.extCodeSizeWord_accountMapEquiv _hAccounts key
            rw [← hsame]
            exact hnoCodeEvm
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody : ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
            simpa [evm0, locals, key] using
              (cureLoadSourceBodyNoCodeRevert (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hliveSolm hposSolm hnoCodeSolm)
          have hposMem :
              (twoWordHashMem key ⟨5⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 key ⟨5⟩ solcFreePtrMem_size
          have hposRead64 :
              (twoWordHashMem key ⟨5⟩ solcFreePtrMem).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 key ⟨5⟩ solcFreePtrMem_size solcFreePtrMem_read64
          have hrev := RD.cureLoadNoCodeRevert
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hafterPos hcanonKey hnoCodeEvm hposMem hposRead64 (by simp)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hcodeSizeEvm : extCodeSizeWord σ_evm key ≠ ⟨0⟩ := hnoCodeEvm
          have hcodeSizeSolm : extCodeSizeWord σ_solm key ≠ ⟨0⟩ := by
            intro hzero
            apply hcodeSizeEvm
            have hsame :=
              Reasoning.Theory.extCodeSizeWord_accountMapEquiv _hAccounts key
            rw [hsame]
            exact hzero
          have hposMem :
              (twoWordHashMem key ⟨5⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 key ⟨5⟩ solcFreePtrMem_size
          have hposRead64 :
              (twoWordHashMem key ⟨5⟩ solcFreePtrMem).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 key ⟨5⟩ solcFreePtrMem_size solcFreePtrMem_read64
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σCallEvm, z, out, A', _, _, rd1602, hcallEvm, houtsz⟩ :=
              RD.cureLoadStaticcall
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σCall := σ_evm)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (cA_call := cA) (key := key) (ret := ⟨484⟩) (R := [sel])
                hafterPos hcanonKey hcodeSizeEvm hposMem hposRead64 hdepthLt (by simp)
            cases z
            · have hcallEvmInit :
                  typedCallViaEVM config
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
                    (false,
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σCallEvm
                        substate := A'
                        createdAccounts := cA' },
                      out) false := by
                simpa [initState] using hcallEvm
              obtain ⟨σCallSolm, ACallSolm, hcallSolm, _hAccountsCall⟩ :=
                typedCallViaEVM_initState_accountMapEquiv hcallEvmInit _hAccounts
              have hcallSolmSrc :
                  typedCallViaEVM config
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (loadSrc I)) "cure" 0 []
                    (false,
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σCallSolm
                        substate := ACallSolm
                        createdAccounts := cA' },
                      out) false := by
                simpa [key, loadKey_address_eq I] using hcallSolm
              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
                simpa [evm0, locals, key] using
                  (cureLoadSourceBodyCallFailureRevert (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmCall :=
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σCallSolm
                        substate := ACallSolm
                        createdAccounts := cA' })
                    (out := out) hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc)
              have hrev := RD.cureLoadCallFailure rd1602 houtsz (by simp)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · by_cases hshort : out.size < 32
              · have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
                    out.size :=
                  loadCureMin32_toNat_of_lt hshort
                have rd1602' := rd1602
                rw [hmin] at rd1602'
                obtain ⟨_, _, rd1623⟩ :=
                  RD.cureLoadCallSuccessToReturnDecode rd1602' (by simp)
                have hamtMem :
                    (twoWordHashMem key ⟨6⟩
                      (twoWordHashMem key ⟨5⟩ solcFreePtrMem)).size = 96 :=
                  twoWordHashMem_size_96 key ⟨6⟩ hposMem
                have hamtRead64 :
                    (twoWordHashMem key ⟨6⟩
                      (twoWordHashMem key ⟨5⟩ solcFreePtrMem)).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  twoWordHashMem_read64 key ⟨6⟩ hposMem hposRead64
                have hbaseSize :
                    (loadCureSelectorMem
                      (twoWordHashMem key ⟨6⟩
                        (twoWordHashMem key ⟨5⟩ solcFreePtrMem))).size = 160 :=
                  loadCureSelectorMem_size_of_size96 hamtMem
                have hbaseRead64 :
                    (loadCureSelectorMem
                      (twoWordHashMem key ⟨6⟩
                        (twoWordHashMem key ⟨5⟩ solcFreePtrMem))).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  loadCureSelectorMem_read64_of_size96 hamtMem hamtRead64
                have hmemWrite :
                    (out.write 0
                      (loadCureSelectorMem
                        (twoWordHashMem key ⟨6⟩
                          (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 out.size).size =
                      160 :=
                  loadCureReturnWrite_size hbaseSize (Nat.le_of_lt hshort) (by rfl)
                have hread64Write :
                    (out.write 0
                      (loadCureSelectorMem
                        (twoWordHashMem key ⟨6⟩
                          (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 out.size).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  loadCureReturnWrite_read64 hbaseSize hbaseRead64 (Nat.le_of_lt hshort) (by rfl)
                have hmload64 :
                    (if (⟨64⟩ : UInt256).toNat ≥
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 out.size).size
                        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
                     else UInt256.ofNat
                       (fromByteArrayBigEndian
                        ((out.write 0
                          (loadCureSelectorMem
                            (twoWordHashMem key ⟨6⟩
                              (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 out.size).readWithPadding
                          (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ :=
                  mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
                have hrev := RD.cureLoadReturnDecodeShortReverts rd1623 hshort houtsz
                  hmload64 (by simp)
                have hcallEvmInit :
                    typedCallViaEVM config
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
                      (true,
                        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σCallEvm
                          substate := A'
                          createdAccounts := cA' },
                        out) false := by
                  simpa [initState] using hcallEvm
                obtain ⟨σCallSolm, ACallSolm, hcallSolm, _hAccountsCall⟩ :=
                  typedCallViaEVM_initState_accountMapEquiv hcallEvmInit _hAccounts
                have hcallSolmSrc :
                    typedCallViaEVM config
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (EVM.address (loadSrc I)) "cure" 0 []
                      (true,
                        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σCallSolm
                          substate := ACallSolm
                          createdAccounts := cA' },
                        out) false := by
                  simpa [key, loadKey_address_eq I] using hcallSolm
                have hdecOut : config.externalABI.decode? "cure" out = none :=
                  loadCureDecode_none_short hshort
                let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
                  simpa [evm0, locals, key] using
                    (cureLoadSourceBodyReturnDecodeRevert (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmCall :=
                        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σCallSolm
                          substate := ACallSolm
                          createdAccounts := cA' })
                      (out := out) hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc
                      hdecOut)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have ho32 : 32 ≤ out.size := Nat.le_of_not_lt hshort
                have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
                  loadCureMin32_toNat_of_ge ho32 houtsz
                have rd1602' := rd1602
                rw [hmin] at rd1602'
                obtain ⟨_, _, rd1623⟩ :=
                  RD.cureLoadCallSuccessToReturnDecode rd1602' (by simp)
                have hamtMem :
                    (twoWordHashMem key ⟨6⟩
                      (twoWordHashMem key ⟨5⟩ solcFreePtrMem)).size = 96 :=
                  twoWordHashMem_size_96 key ⟨6⟩ hposMem
                have hamtRead64 :
                    (twoWordHashMem key ⟨6⟩
                      (twoWordHashMem key ⟨5⟩ solcFreePtrMem)).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  twoWordHashMem_read64 key ⟨6⟩ hposMem hposRead64
                have hbaseSize :
                    (loadCureSelectorMem
                      (twoWordHashMem key ⟨6⟩
                        (twoWordHashMem key ⟨5⟩ solcFreePtrMem))).size = 160 :=
                  loadCureSelectorMem_size_of_size96 hamtMem
                have hbaseRead64 :
                    (loadCureSelectorMem
                      (twoWordHashMem key ⟨6⟩
                        (twoWordHashMem key ⟨5⟩ solcFreePtrMem))).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  loadCureSelectorMem_read64_of_size96 hamtMem hamtRead64
                have hmemWrite :
                    (out.write 0
                      (loadCureSelectorMem
                        (twoWordHashMem key ⟨6⟩
                          (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).size =
                      160 :=
                  loadCureReturnWrite_size hbaseSize (by omega) ho32
                have hread64Write :
                    (out.write 0
                      (loadCureSelectorMem
                        (twoWordHashMem key ⟨6⟩
                          (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  loadCureReturnWrite_read64 hbaseSize hbaseRead64 (by omega) ho32
                have hmload64 :
                    (if (⟨64⟩ : UInt256).toNat ≥
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).size
                        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
                     else UInt256.ofNat
                       (fromByteArrayBigEndian
                        ((out.write 0
                          (loadCureSelectorMem
                            (twoWordHashMem key ⟨6⟩
                              (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).readWithPadding
                          (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ :=
                  mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
                let newAmt : UInt256 :=
                  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
                have hread128Write :
                    (out.write 0
                      (loadCureSelectorMem
                        (twoWordHashMem key ⟨6⟩
                          (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).readWithPadding 128 32 =
                      out.extract 0 32 :=
                  loadCureReturnWrite_read128_32 hbaseSize ho32
                have hmload128 :
                    (if (⟨128⟩ : UInt256).toNat ≥
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).size
                        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
                     else UInt256.ofNat
                       (fromByteArrayBigEndian
                        ((out.write 0
                          (loadCureSelectorMem
                            (twoWordHashMem key ⟨6⟩
                              (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).readWithPadding
                          (⟨128⟩ : UInt256).toNat 32))) =
                      newAmt := by
                  have hnot :
                      ¬ ((⟨128⟩ : UInt256).toNat ≥
                            (out.write 0
                              (loadCureSelectorMem
                                (twoWordHashMem key ⟨6⟩
                                  (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32).size
                          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩) := by
                    rw [hmemWrite]
                    native_decide
                  rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
                    hread128Write]
                obtain ⟨_, _, rd1643⟩ :=
                  RD.cureLoadReturnDecodeOk (retWord := newAmt) rd1623 ho32 houtsz
                    hmload64 hmload128 (by simp)
                obtain ⟨_, _, rd1670⟩ :=
                  RD.cureLoadStoreAmt
                    (key := key) (ret := ⟨484⟩) (newAmt := newAmt)
                    (oldAmt := solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key))
                    (R := [sel]) rd1643 hcanonKey hmemWrite
                    (by simpa using _hperm) (by simp)
                obtain ⟨k3666, C3666, rd3666⟩ :=
                  RD.cureLoadToSubRoutine
                    (key := key) (ret := ⟨484⟩) (newAmt := newAmt)
                    (oldAmt := solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key))
                    (R := [sel]) rd1670 (by simp)
                by_cases hsubOk :
                    (solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key)).toNat ≤
                      (solcSlotWord
                        (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                        I ⟨9⟩).toNat
                · obtain ⟨k1689, C1689, rd1689⟩ :=
                    RD.solcCheckedSubSuccess
                      (code := cureBytecode) (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (pc := ⟨3666⟩) (okPc := ⟨3743⟩)
                      (a :=
                        solcSlotWord
                          (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                          I ⟨9⟩)
                      (b := solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key))
                      (ret := ⟨1689⟩)
                      (R := [⟨1695⟩, newAmt,
                        solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key), key, ⟨484⟩, sel])
                      rd3666
                      (by
                        unfold solcCheckedSubSuccessWf
                        repeat' first | apply And.intro | native_decide)
                      hsubOk (by jump_dest) (by jump_dest) (by simp)
                  let oldAmtEvm := solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key)
                  let sayAfterEvm :=
                    solcSlotWord
                      (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                      I ⟨9⟩
                  let withoutOld := UInt256.sub sayAfterEvm oldAmtEvm
                  by_cases haddOk : withoutOld.toNat + newAmt.toNat < UInt256.size
                  · have hcallEvmInit :
                        typedCallViaEVM config
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
                          (true,
                            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σCallEvm
                              substate := A'
                              createdAccounts := cA' },
                            out) false := by
                      simpa [initState] using hcallEvm
                    obtain ⟨σCallSolm, ACallSolm, hcallSolm, hAccountsCall⟩ :=
                      typedCallViaEVM_initState_accountMapEquiv hcallEvmInit _hAccounts
                    let evmCallSolm :=
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σCallSolm
                        substate := ACallSolm
                        createdAccounts := cA' }
                    have hcallSolmSrc :
                        typedCallViaEVM config
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (EVM.address (loadSrc I)) "cure" 0 []
                          (true, evmCallSolm, out) false := by
                      simpa [evmCallSolm, key, loadKey_address_eq I] using hcallSolm
                    have hdecOut :
                        config.externalABI.decode? "cure" out =
                          some [.int (Int.ofNat newAmt.toNat)] := by
                      simpa [newAmt] using loadCureDecode_ok ho32
                    let σAmtEvm :=
                      sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt
                    let σSayEvm := sstoreAccountMap I.codeOwner σAmtEvm ⟨9⟩
                      (withoutOld + newAmt)
                    have hAccountsStored :
                        accountMapEquiv σAmtEvm
                          (sstoreAccountMap I.codeOwner σCallSolm (solcMappingSlot ⟨6⟩ key) newAmt) := by
                      simpa [σAmtEvm] using
                        accountMapEquiv_sstoreAccountMap I.codeOwner (solcMappingSlot ⟨6⟩ key)
                          newAmt hAccountsCall
                    have hsayeq :
                        Solm.EVM.storageLoad
                          (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                            (loadAmtSlotFor I) newAmt)
                          evmCallSolm.executionEnv.codeOwner ⟨9⟩ =
                          sayAfterEvm := by
                      have hs :=
                        accountMapEquiv_storage_findD hAccountsStored I.codeOwner ⟨9⟩ ⟨0⟩
                      simpa [evmCallSolm, loadAmtSlotFor_eq I, storageStore_accountMap,
                        Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord, sayAfterEvm,
                        σAmtEvm] using hs.symm
                    have holdeq :
                        Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner (loadAmtSlotFor I) =
                          oldAmtEvm := by
                      have hs :=
                        accountMapEquiv_storage_findD _hAccounts I.codeOwner (loadAmtSlotFor I) ⟨0⟩
                      simpa [loadAmtSlotFor_eq I, Solm.EVM.storageLoad, initState,
                        State.lookupAccount, solcSlotWord, oldAmtEvm] using hs.symm
                    have hsubOkSolm :
                        (Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner (loadAmtSlotFor I)).toNat ≤
                          (Solm.EVM.storageLoad
                            (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                              (loadAmtSlotFor I) newAmt)
                            evmCallSolm.executionEnv.codeOwner ⟨9⟩).toNat := by
                      simpa [oldAmtEvm, sayAfterEvm, hsayeq, holdeq] using hsubOk
                    have haddOkSolm :
                        (UInt256.sub
                          (Solm.EVM.storageLoad
                            (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                              (loadAmtSlotFor I) newAmt)
                            evmCallSolm.executionEnv.codeOwner ⟨9⟩)
                          (Solm.EVM.storageLoad
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            I.codeOwner (loadAmtSlotFor I))).toNat + newAmt.toNat <
                          UInt256.size := by
                      simpa [withoutOld, oldAmtEvm, sayAfterEvm, hsayeq, holdeq] using haddOk
                    have hstoreMemSize :
                        (twoWordHashMem key ⟨6⟩
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).size = 160 :=
                      twoWordHashMem_size_160 key ⟨6⟩ hmemWrite
                    have hstoreRead64 :
                        (twoWordHashMem key ⟨6⟩
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).readWithPadding
                            64 32 =
                          UInt256.toByteArray ⟨128⟩ :=
                      twoWordHashMem_read64_160 key ⟨6⟩ hmemWrite hread64Write
                    have rdToAdd := evm_run rd1689 with [
                      raw jumpdest (by native_decide) (by evm_ov),
                      raw dup3 (by native_decide) (by evm_ov),
                      raw push2 ⟨3749⟩ (by native_decide) (by evm_ov)]
                    have rd3749 := rdToAdd.jump (by native_decide) (by jump_dest) (by evm_ov)
                    obtain ⟨k1695, C1695, rd1695⟩ := RD.solcCheckedAddSuccess
                      (code := cureBytecode) (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (pc := ⟨3749⟩) (okPc := ⟨3743⟩)
                      (a := withoutOld) (b := newAmt) (ret := ⟨1695⟩)
                      (R := [newAmt, oldAmtEvm, key, ⟨484⟩, sel])
                      rd3749
                      (by
                        unfold solcCheckedAddSuccessWf
                        repeat' first | apply And.intro | native_decide)
                      haddOk (by jump_dest) (by jump_dest) (by simp)
                    have hretPc : (D_J cureBytecode 0).contains (⟨484⟩ : UInt256) = true := by
                      jump_dest
                    by_cases hloadedEvm :
                        solcSlotWord σSayEvm I (solcMappingSlot ⟨7⟩ key) = ⟨0⟩
                    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                      let oldAmtSolm :=
                        Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
                      let evmAmtSolm := Solm.EVM.storageStore evmCallSolm
                        evmCallSolm.executionEnv.codeOwner (loadAmtSlotFor I) newAmt
                      let sayAfterSolm :=
                        Solm.EVM.storageLoad evmAmtSolm evmAmtSolm.executionEnv.codeOwner ⟨9⟩
                      let withoutOldSolm := UInt256.sub sayAfterSolm oldAmtSolm
                      let evmSaySolm := Solm.EVM.storageStore evmAmtSolm
                        evmAmtSolm.executionEnv.codeOwner ⟨9⟩ (withoutOldSolm + newAmt)
                      let evmLoadedSolm := Solm.EVM.storageStore evmSaySolm
                        evmSaySolm.executionEnv.codeOwner (loadLoadedSlotFor I) ⟨1⟩
                      let countSolm :=
                        Solm.EVM.storageLoad evmLoadedSolm evmLoadedSolm.executionEnv.codeOwner ⟨8⟩
                      let evmCountSolm := Solm.EVM.storageStore evmLoadedSolm
                        evmLoadedSolm.executionEnv.codeOwner ⟨8⟩ (countSolm + ⟨1⟩)
                      let localsSaySolm : Store :=
                        (((locals.insert "oldAmt_" (.int (Int.ofNat oldAmtEvm.toNat))).insert
                          "newAmt_" (.int (Int.ofNat newAmt.toNat))).insert
                            "withoutOld" (.int (Int.ofNat withoutOldSolm.toNat))).insert
                            "sayNew" (.int (Int.ofNat (withoutOldSolm + newAmt).toNat))
                      have hwithoutSolmEq : withoutOldSolm = withoutOld := by
                        have hold' :
                            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                              (loadAmtSlotFor I) = oldAmtEvm := by
                          simpa [evm0] using holdeq
                        have hsay' :
                            Solm.EVM.storageLoad evmAmtSolm evmAmtSolm.executionEnv.codeOwner
                              ⟨9⟩ = sayAfterEvm := by
                          simpa [evmAmtSolm, storageStore_executionEnv] using hsayeq
                        simp [withoutOldSolm, sayAfterSolm, oldAmtSolm, withoutOld,
                          sayAfterEvm, oldAmtEvm, hsay', hold']
                      have hAccountsSay :
                          accountMapEquiv σSayEvm evmSaySolm.accountMap := by
                          simpa [σSayEvm, evmSaySolm, evmAmtSolm, evmCallSolm,
                            storageStore_accountMap, storageStore_executionEnv, key,
                            loadAmtSlotFor_eq I, hwithoutSolmEq] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩
                            (withoutOld + newAmt) hAccountsStored
                      have hloadedSolm :
                          Solm.EVM.storageLoad evmSaySolm evmSaySolm.executionEnv.codeOwner
                            (loadLoadedSlotFor I) = ⟨0⟩ := by
                        have hslot :
                            Solm.EVM.storageLoad evmSaySolm evmSaySolm.executionEnv.codeOwner
                                (loadLoadedSlotFor I) =
                              solcSlotWord σSayEvm I (solcMappingSlot ⟨7⟩ key) := by
                          have hs :=
                            accountMapEquiv_storage_findD hAccountsSay I.codeOwner
                              (loadLoadedSlotFor I) ⟨0⟩
                          simpa [evmSaySolm, evmAmtSolm, evmCallSolm,
                            Solm.EVM.storageLoad, State.lookupAccount,
                            Account.lookupStorage, solcSlotWord, loadLoadedSlotFor_eq I,
                            storageStore_executionEnv, key] using hs.symm
                        exact hslot.trans hloadedEvm
                      have hbody :=
                        (cureLoadSourceBodyOkLoadedZero (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmCall := evmCallSolm) (out := out) (newAmt := newAmt)
                          hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc hdecOut
                            hsubOkSolm haddOkSolm hloadedSolm)
                      obtain ⟨_, _, hretPcRd⟩ :=
                        RD.cureLoadSuccessLoadedZero
                          (ee := I) (k := k1695) (C := C1695)
                          (key := key) (ret := ⟨484⟩) (newAmt := newAmt)
                          (oldAmt := oldAmtEvm) (sayNew := withoutOld + newAmt)
                          (R := [sel])
                          (mem :=
                            twoWordHashMem key ⟨6⟩
                              (out.write 0
                                (loadCureSelectorMem
                                  (twoWordHashMem key ⟨6⟩
                                    (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32))
                          (rdata := out)
                          (cA := cA')
                          (σ := σAmtEvm)
                          rd1695 hretPc (by simpa using _hperm) hstoreMemSize hstoreRead64
                          hcanonKey (by simpa [σSayEvm] using hloadedEvm) (by simp)
                      have hretPc' := hretPcRd.jumpdest (by native_decide) (by evm_ov)
                      have hret :
                          RDret cureBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            (cA',
                              sstoreAccountMap I.codeOwner
                                (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                                ⟨8⟩
                                (solcSlotWord
                                  (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                                  I ⟨8⟩ + ⟨1⟩))
                            ByteArray.empty := by
                        simpa [σSayEvm] using RD.stop hretPc' (by native_decide) (by simp)
                      have hAccountsLoaded :
                          accountMapEquiv
                            (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                            evmLoadedSolm.accountMap := by
                        simpa [evmLoadedSolm, evmSaySolm, evmAmtSolm, evmCallSolm,
                          storageStore_accountMap,
                          storageStore_executionEnv, loadLoadedSlotFor_eq I, key] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner (loadLoadedSlotFor I)
                            ⟨1⟩ hAccountsSay
                      have hcountEq :
                          countSolm =
                            solcSlotWord
                              (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                              I ⟨8⟩ := by
                        have hs :=
                          accountMapEquiv_storage_findD hAccountsLoaded I.codeOwner ⟨8⟩ ⟨0⟩
                        simpa [countSolm, evmLoadedSolm, evmSaySolm, evmAmtSolm, evmCallSolm,
                          Solm.EVM.storageLoad,
                          State.lookupAccount, Account.lookupStorage, solcSlotWord,
                          storageStore_executionEnv] using hs.symm
                      have hcreated :
                          (cA',
                            sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                              ⟨8⟩
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                                I ⟨8⟩ + ⟨1⟩)).1 = evmCountSolm.createdAccounts := by
                        simp [evmCountSolm, evmLoadedSolm, evmSaySolm, evmAmtSolm, evmCallSolm,
                          storageStore_createdAccounts]
                      have haccounts :
                          accountMapEquiv
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                              ⟨8⟩
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                                I ⟨8⟩ + ⟨1⟩))
                            evmCountSolm.accountMap := by
                        simpa [evmCountSolm, evmLoadedSolm, evmSaySolm, evmAmtSolm, evmCallSolm,
                          storageStore_accountMap,
                          storageStore_executionEnv, hcountEq] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σSayEvm (solcMappingSlot ⟨7⟩ key) ⟨1⟩)
                              I ⟨8⟩ + ⟨1⟩) hAccountsLoaded
                      have henc : returnEquiv ByteArray.empty none loadTransition.returnType := by
                        rw [show loadTransition.returnType = [] by rfl]
                        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
                      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                        hcreated haccounts henc
                    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                      let oldAmtSolm :=
                        Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
                      let evmAmtSolm := Solm.EVM.storageStore evmCallSolm
                        evmCallSolm.executionEnv.codeOwner (loadAmtSlotFor I) newAmt
                      let sayAfterSolm :=
                        Solm.EVM.storageLoad evmAmtSolm evmAmtSolm.executionEnv.codeOwner ⟨9⟩
                      let withoutOldSolm := UInt256.sub sayAfterSolm oldAmtSolm
                      let evmSaySolm := Solm.EVM.storageStore evmAmtSolm
                        evmAmtSolm.executionEnv.codeOwner ⟨9⟩ (withoutOldSolm + newAmt)
                      let localsSaySolm : Store :=
                        (((locals.insert "oldAmt_" (.int (Int.ofNat oldAmtEvm.toNat))).insert
                          "newAmt_" (.int (Int.ofNat newAmt.toNat))).insert
                          "withoutOld" (.int (Int.ofNat withoutOldSolm.toNat))).insert
                          "sayNew" (.int (Int.ofNat (withoutOldSolm + newAmt).toNat))
                      have hwithoutSolmEq : withoutOldSolm = withoutOld := by
                        have hold' :
                            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
                              (loadAmtSlotFor I) = oldAmtEvm := by
                          simpa [evm0] using holdeq
                        have hsay' :
                            Solm.EVM.storageLoad evmAmtSolm evmAmtSolm.executionEnv.codeOwner
                              ⟨9⟩ = sayAfterEvm := by
                          simpa [evmAmtSolm, storageStore_executionEnv] using hsayeq
                        simp [withoutOldSolm, sayAfterSolm, oldAmtSolm, withoutOld,
                          sayAfterEvm, oldAmtEvm, hsay', hold']
                      have hAccountsSay :
                          accountMapEquiv σSayEvm evmSaySolm.accountMap := by
                          simpa [σSayEvm, evmSaySolm, evmAmtSolm, evmCallSolm,
                            storageStore_accountMap, storageStore_executionEnv, key,
                            loadAmtSlotFor_eq I, hwithoutSolmEq] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩
                            (withoutOld + newAmt) hAccountsStored
                      have hloadedSolm :
                          Solm.EVM.storageLoad evmSaySolm evmSaySolm.executionEnv.codeOwner
                            (loadLoadedSlotFor I) ≠ ⟨0⟩ := by
                        intro hz
                        apply hloadedEvm
                        have hslot :
                            Solm.EVM.storageLoad evmSaySolm evmSaySolm.executionEnv.codeOwner
                                (loadLoadedSlotFor I) =
                              solcSlotWord σSayEvm I (solcMappingSlot ⟨7⟩ key) := by
                          have hs :=
                            accountMapEquiv_storage_findD hAccountsSay I.codeOwner
                              (loadLoadedSlotFor I) ⟨0⟩
                          simpa [evmSaySolm, evmAmtSolm, evmCallSolm,
                            Solm.EVM.storageLoad, State.lookupAccount,
                            Account.lookupStorage, solcSlotWord, loadLoadedSlotFor_eq I,
                            storageStore_executionEnv, key] using hs.symm
                        exact hslot.symm.trans hz
                      have hbody :=
                        (cureLoadSourceBodyOkLoadedNonzero (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmCall := evmCallSolm) (out := out) (newAmt := newAmt)
                          hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc hdecOut
                            hsubOkSolm haddOkSolm hloadedSolm)
                      obtain ⟨_, _, hretPcRd⟩ :=
                        RD.cureLoadSuccessLoadedNonzero
                          (ee := I) (k := k1695) (C := C1695)
                          (key := key) (ret := ⟨484⟩) (newAmt := newAmt)
                          (oldAmt := oldAmtEvm) (sayNew := withoutOld + newAmt)
                          (R := [sel])
                          (mem :=
                            twoWordHashMem key ⟨6⟩
                              (out.write 0
                                (loadCureSelectorMem
                                  (twoWordHashMem key ⟨6⟩
                                    (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32))
                          (rdata := out)
                          (cA := cA')
                          (σ := σAmtEvm)
                          rd1695 hretPc (by simpa using _hperm) hstoreMemSize hstoreRead64
                          hcanonKey (by simpa [σSayEvm] using hloadedEvm) (by simp)
                      have hretPc' := hretPcRd.jumpdest (by native_decide) (by evm_ov)
                      have hret :
                          RDret cureBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            (cA', σSayEvm) ByteArray.empty := by
                        simpa [σSayEvm] using RD.stop hretPc' (by native_decide) (by simp)
                      have hcreated : (cA', σSayEvm).1 = evmSaySolm.createdAccounts := by
                        simp [evmSaySolm, evmAmtSolm, evmCallSolm, storageStore_createdAccounts]
                      have haccounts : accountMapEquiv σSayEvm evmSaySolm.accountMap := hAccountsSay
                      have henc : returnEquiv ByteArray.empty none loadTransition.returnType := by
                        rw [show loadTransition.returnType = [] by rfl]
                        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
                      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                        hcreated haccounts henc
                  · have hoverEvm : UInt256.size ≤ withoutOld.toNat + newAmt.toNat :=
                        Nat.le_of_not_lt haddOk
                    have hcallEvmInit :
                        typedCallViaEVM config
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
                          (true,
                            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σCallEvm
                              substate := A'
                              createdAccounts := cA' },
                            out) false := by
                      simpa [initState] using hcallEvm
                    obtain ⟨σCallSolm, ACallSolm, hcallSolm, hAccountsCall⟩ :=
                      typedCallViaEVM_initState_accountMapEquiv hcallEvmInit _hAccounts
                    let evmCallSolm :=
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σCallSolm
                        substate := ACallSolm
                        createdAccounts := cA' }
                    have hcallSolmSrc :
                        typedCallViaEVM config
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (EVM.address (loadSrc I)) "cure" 0 []
                          (true, evmCallSolm, out) false := by
                      simpa [evmCallSolm, key, loadKey_address_eq I] using hcallSolm
                    have hdecOut :
                        config.externalABI.decode? "cure" out =
                          some [.int (Int.ofNat newAmt.toNat)] := by
                      simpa [newAmt] using loadCureDecode_ok ho32
                    have hAccountsStored :
                        accountMapEquiv
                          (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                          (sstoreAccountMap I.codeOwner σCallSolm (solcMappingSlot ⟨6⟩ key) newAmt) :=
                      accountMapEquiv_sstoreAccountMap I.codeOwner (solcMappingSlot ⟨6⟩ key)
                        newAmt hAccountsCall
                    have hsayeq :
                        Solm.EVM.storageLoad
                          (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                            (loadAmtSlotFor I) newAmt)
                          evmCallSolm.executionEnv.codeOwner ⟨9⟩ =
                          solcSlotWord
                            (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                            I ⟨9⟩ := by
                      have hs :=
                        accountMapEquiv_storage_findD hAccountsStored I.codeOwner ⟨9⟩ ⟨0⟩
                      simpa [evmCallSolm, loadAmtSlotFor_eq I, storageStore_accountMap,
                        Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord] using hs.symm
                    have holdeq :
                        Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner (loadAmtSlotFor I) =
                          solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key) := by
                      have hs :=
                        accountMapEquiv_storage_findD _hAccounts I.codeOwner (loadAmtSlotFor I) ⟨0⟩
                      simpa [loadAmtSlotFor_eq I, Solm.EVM.storageLoad, initState,
                        State.lookupAccount, solcSlotWord] using hs.symm
                    have hsubOkSolm :
                        (Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner (loadAmtSlotFor I)).toNat ≤
                          (Solm.EVM.storageLoad
                            (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                              (loadAmtSlotFor I) newAmt)
                            evmCallSolm.executionEnv.codeOwner ⟨9⟩).toNat := by
                      simpa [oldAmtEvm, sayAfterEvm, hsayeq, holdeq] using hsubOk
                    have hoverSolm :
                        UInt256.size ≤
                          (UInt256.sub
                            (Solm.EVM.storageLoad
                              (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                                (loadAmtSlotFor I) newAmt)
                              evmCallSolm.executionEnv.codeOwner ⟨9⟩)
                            (Solm.EVM.storageLoad
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              I.codeOwner (loadAmtSlotFor I))).toNat + newAmt.toNat := by
                      simpa [withoutOld, oldAmtEvm, sayAfterEvm, hsayeq, holdeq] using hoverEvm
                    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    have hbody :
                        ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
                      simpa [evm0, locals, key] using
                        (cureLoadSourceBodyAddRevert (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmCall := evmCallSolm) (out := out) (newAmt := newAmt)
                          hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc hdecOut
                          hsubOkSolm hoverSolm)
                    have hstoreMemSize :
                        (twoWordHashMem key ⟨6⟩
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).size = 160 :=
                      twoWordHashMem_size_160 key ⟨6⟩ hmemWrite
                    have hstoreRead64 :
                        (twoWordHashMem key ⟨6⟩
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).readWithPadding
                            64 32 =
                          UInt256.toByteArray ⟨128⟩ :=
                      twoWordHashMem_read64_160 key ⟨6⟩ hmemWrite hread64Write
                    have hrev :
                        RDrev cureBytecode (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                      refine RD.cureLoadAddOverflowRevert
                        (ee := I) (k := k1689) (C := C1689)
                        (key := key) (ret := ⟨484⟩)
                        (newAmt := newAmt) (oldAmt := oldAmtEvm)
                        (withoutOld := withoutOld) (R := [sel])
                        (mem :=
                          twoWordHashMem key ⟨6⟩
                            (out.write 0
                              (loadCureSelectorMem
                                (twoWordHashMem key ⟨6⟩
                                  (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32))
                        (rdata := out)
                        (acc :=
                          (cA',
                            sstoreAccountMap I.codeOwner σCallEvm
                              (solcMappingSlot ⟨6⟩ key) newAmt))
                        ?_ ?_ ?_ ?_ ?_
                      · simpa [withoutOld, oldAmtEvm, sayAfterEvm] using rd1689
                      · exact hoverEvm
                      · exact hstoreMemSize
                      · exact hstoreRead64
                      · simp
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hcallEvmInit :
                      typedCallViaEVM config
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
                        (true,
                          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σCallEvm
                            substate := A'
                            createdAccounts := cA' },
                          out) false := by
                    simpa [initState] using hcallEvm
                  obtain ⟨σCallSolm, ACallSolm, hcallSolm, hAccountsCall⟩ :=
                    typedCallViaEVM_initState_accountMapEquiv hcallEvmInit _hAccounts
                  let evmCallSolm :=
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σCallSolm
                      substate := ACallSolm
                      createdAccounts := cA' }
                  have hcallSolmSrc :
                      typedCallViaEVM config
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (EVM.address (loadSrc I)) "cure" 0 []
                        (true, evmCallSolm, out) false := by
                    simpa [evmCallSolm, key, loadKey_address_eq I] using hcallSolm
                  have hdecOut :
                      config.externalABI.decode? "cure" out =
                        some [.int (Int.ofNat newAmt.toNat)] := by
                    simpa [newAmt] using loadCureDecode_ok ho32
                  have hAccountsStored :
                      accountMapEquiv
                        (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                        (sstoreAccountMap I.codeOwner σCallSolm (solcMappingSlot ⟨6⟩ key) newAmt) :=
                    accountMapEquiv_sstoreAccountMap I.codeOwner (solcMappingSlot ⟨6⟩ key)
                      newAmt hAccountsCall
                  have hsayeq :
                      Solm.EVM.storageLoad
                        (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                          (loadAmtSlotFor I) newAmt)
                        evmCallSolm.executionEnv.codeOwner ⟨9⟩ =
                        solcSlotWord
                          (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                          I ⟨9⟩ := by
                    have hs :=
                      accountMapEquiv_storage_findD hAccountsStored I.codeOwner ⟨9⟩ ⟨0⟩
                    simpa [evmCallSolm, loadAmtSlotFor_eq I, storageStore_accountMap,
                      Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord] using hs.symm
                  have holdeq :
                      Solm.EVM.storageLoad
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        I.codeOwner (loadAmtSlotFor I) =
                        solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key) := by
                    have hs :=
                      accountMapEquiv_storage_findD _hAccounts I.codeOwner (loadAmtSlotFor I) ⟨0⟩
                    simpa [loadAmtSlotFor_eq I, Solm.EVM.storageLoad, initState,
                      State.lookupAccount, solcSlotWord] using hs.symm
                  have hunderSolm :
                      (Solm.EVM.storageLoad
                        (Solm.EVM.storageStore evmCallSolm evmCallSolm.executionEnv.codeOwner
                          (loadAmtSlotFor I) newAmt)
                        evmCallSolm.executionEnv.codeOwner ⟨9⟩).toNat <
                        (Solm.EVM.storageLoad
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner (loadAmtSlotFor I)).toNat := by
                    have hlt :
                        (solcSlotWord
                          (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                          I ⟨9⟩).toNat <
                          (solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key)).toNat :=
                      Nat.lt_of_not_ge hsubOk
                    simpa [hsayeq, holdeq] using hlt
                  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
                    simpa [evm0, locals, key, evmCallSolm] using
                      (cureLoadSourceBodySubRevert (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmCall := evmCallSolm) (out := out) (newAmt := newAmt)
                        hwv hliveSolm hposSolm hcodeSizeSolm hcallSolmSrc hdecOut hunderSolm)
                  have hsubLt :
                      (solcSlotWord
                        (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                        I ⟨9⟩).toNat <
                        (solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key)).toNat :=
                    Nat.lt_of_not_ge hsubOk
                  have hstoreMemSize :
                      (twoWordHashMem key ⟨6⟩
                        (out.write 0
                          (loadCureSelectorMem
                            (twoWordHashMem key ⟨6⟩
                              (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).size = 160 :=
                    twoWordHashMem_size_160 key ⟨6⟩ hmemWrite
                  have hstoreRead64 :
                      (twoWordHashMem key ⟨6⟩
                        (out.write 0
                          (loadCureSelectorMem
                            (twoWordHashMem key ⟨6⟩
                              (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32)).readWithPadding
                          64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    twoWordHashMem_read64_160 key ⟨6⟩ hmemWrite hread64Write
                  have hrev :
                      RDrev cureBytecode (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                    refine RD.cureLoadSubUnderflowRevert
                      (ee := I) (k := k3666) (C := C3666)
                      (key := key) (ret := ⟨484⟩) (newAmt := newAmt)
                      (oldAmt := solcSlotWord σ_evm I (solcMappingSlot ⟨6⟩ key))
                      (sayAfter :=
                        solcSlotWord
                          (sstoreAccountMap I.codeOwner σCallEvm (solcMappingSlot ⟨6⟩ key) newAmt)
                          I ⟨9⟩)
                      (R := [sel])
                      (mem :=
                        twoWordHashMem key ⟨6⟩
                          (out.write 0
                            (loadCureSelectorMem
                              (twoWordHashMem key ⟨6⟩
                                (twoWordHashMem key ⟨5⟩ solcFreePtrMem))) 128 32))
                      (rdata := out)
                      (acc :=
                        (cA',
                          sstoreAccountMap I.codeOwner σCallEvm
                            (solcMappingSlot ⟨6⟩ key) newAmt))
                      ?_ ?_ ?_ ?_ ?_
                    · exact rd3666
                    · exact hsubLt
                    · exact hstoreMemSize
                    · exact hstoreRead64
                    · simp
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hdepthEq : I.depth = 1024 := by
              apply Fin.ext
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              omega
            obtain ⟨_, _, rd1602⟩ :=
              RD.cureLoadStaticcallDepthLimit
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (key := key) (ret := ⟨484⟩) (R := [sel])
                hafterPos hcanonKey hcodeSizeEvm hposMem hposRead64 hdepthEq (by simp)
            let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            let A_call := (evm0.addAccessedAccount (EVM.address (loadSrc I))).substate
            have hcallDepth :
                typedCallViaEVM config evm0
                  (EVM.address (loadSrc I)) "cure" 0 []
                  (false, { evm0 with substate := A_call }, ByteArray.empty) false := by
              simpa [evm0, A_call, initState] using
                (callNotMade_depthLimit (cfg := config) (evm := evm0)
                  (tgt := EVM.address (loadSrc I)) (name := "cure")
                  (args := []) (callPerm := false)
                  (by rfl : config.externalABI.encode? "cure" [] = some sourceCureSelector)
                  (by simpa [evm0, initState] using hdepthEq))
            have hbody :
                ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
              simpa [evm0, locals, key] using
                (cureLoadSourceBodyCallFailureRevert (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmCall := { evm0 with substate := A_call }) (out := ByteArray.empty)
                  hwv hliveSolm hposSolm hcodeSizeSolm hcallDepth)
            have hrev := RD.cureLoadCallFailure rd1602 (by native_decide) (by simp)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨0⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals loadTransition.body .reverted := by
        simpa [evm0, locals] using
          (cureLoadSourceBodyStillLiveRevert (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hliveSolm)
      have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨0⟩ := by
        simpa [cureSlotWord] using hliveEvm
      have hrev := RD.cureLoadStillLiveRevert
        (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, loadKey] using hroutine)
        hliveSolc solcFreePtrMem_size solcFreePtrMem_read64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 32
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := cureBytecode) (sel := sel) (entry := ⟨486⟩) (ret := ⟨484⟩)
      (decoded := ⟨508⟩) (need := ⟨32⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_load_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure
