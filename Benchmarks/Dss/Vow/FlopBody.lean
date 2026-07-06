import Benchmarks.Dss.Vow.FlopKick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` top-level runtime body wrapper -/

theorem vowSlotWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    vowSlotWord slot σ I = vowSlotWord slot τ I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

theorem kissDaiTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    kissDaiTargetWord σ I = kissDaiTargetWord τ I := by
  simp [kissDaiTargetWord, vowSlotWord_accountMapEquiv hAccounts ⟨1⟩]

theorem kissVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    kissVatAddress σ I = kissVatAddress τ I := by
  apply Fin.ext
  simp [kissVatAddress, vowAddressReturnWord,
    vowSlotWord_accountMapEquiv hAccounts ⟨1⟩]

theorem kissDaiCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (kissDaiTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (kissDaiTargetWord σ I)
  have htarget : kissDaiTargetWord σ I = kissDaiTargetWord τ I :=
    kissDaiTargetWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem kissDaiCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (kissDaiTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (kissDaiTargetWord σ I)
  have htarget : kissDaiTargetWord σ I = kissDaiTargetWord τ I :=
    kissDaiTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem kissVatCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := kissDaiTargetWord σ I) (addr := kissVatAddress σ I)
      (kissVatAddress_eq_daiTarget_account σ I) hne

theorem kissVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := kissDaiTargetWord σ I) (addr := kissVatAddress σ I)
      (kissVatAddress_eq_daiTarget_account σ I) hzero

theorem storageLoad_codeOwner_eq_vowSlotWord (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      vowSlotWord slot evm.accountMap I := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, vowSlotWord,
    solcSlotWord, howner]

theorem flopFlopperAddressOf_eq_vowAddressReturnWord (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    flopFlopperAddressOf evm =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ evm.accountMap I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [flopFlopperAddressOf, vowAddressReturnWord,
    storageLoad_codeOwner_eq_vowSlotWord evm I ⟨3⟩ howner]

theorem flopFlopperCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨3⟩ evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (flopFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hne

theorem flopFlopperCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (vowAddressReturnWord ⟨3⟩ evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := vowAddressReturnWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (flopFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hzero

theorem RD.vowFlopSin0CallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd1276⟩ := RD.vowFlopToSin0Staticcall hreach hcodeSize
  obtain ⟨k1277, C1277, rd1277raw⟩ :=
    RD.uniswapStaticcallDepthLimit rd1276 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        healSinOutPtr.toNat healSinInSize.toNat)
        healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    rw [healSinInSize_eq]
    native_decide
  have hoff : healSinOutPtr.toNat = 128 := by
    native_decide
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (ByteArray.empty.write 0 (healSinCalldataMem I solcFreePtrMem) healSinOutPtr.toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k1277 C1277 :=
    haw ▸ rd1277raw
  rw [hoff, hmin, byteArray_write_len_zero] at rd1277
  exact ⟨k1277, C1277, rd1277⟩

set_option maxHeartbeats 0 in
theorem vowFlopBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some flopTransition :=
    vowDispatch_flop hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flop hsz4
  have hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C :=
    vowReachFlopBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  by_cases hcodeSizeSin :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩
  · exact vowFlopVatSin0NoCodeBodyCore hcode hwv hdispatch hdecode hreach hAccounts
      hcodeSizeSin
  have hcodeSizeSinNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) ≠ ⟨0⟩ :=
    hcodeSizeSin
  have hcodeSizeSinSolmNE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) ≠ ⟨0⟩ :=
    kissDaiCodeSize_ne_accountMapEquiv hAccounts hcodeSizeSinNE
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    kissVatCode_pos_of_codeSize_ne (cA := cA) (gh := gh) (bl := bl)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSinSolmNE
  have hVatAddrOrig : kissVatAddress σ_evm I = kissVatAddress σ_solm I :=
    kissVatAddress_accountMapEquiv hAccounts
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨cA_sin, σ_sin, zSin, outSin, A_sin, k1277, C1277,
        rd1277, hcallSinEvmRaw, hoszSin⟩ :=
      RD.vowFlopSin0PostCall hreach hcodeSizeSinNE hdepthLt
    cases zSin
    · have hcallSinEvm :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "sin" 0 [.address I.codeOwner]
            (false,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_sin
                  substate := A_sin
                  createdAccounts := cA_sin },
              outSin) false := by
        simpa using hcallSinEvmRaw
      obtain ⟨σ_sin_solm, A_sin_solm, hcallSinSolmRaw, _hStateSin⟩ :=
        typedCallViaEVM_initState_EVMStateEquiv hcallSinEvm
          (by simp [initState]) hAccounts
      let evmSinSolm :=
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin_solm
            substate := A_sin_solm
            createdAccounts := cA_sin }
      have hcallSinSolm :
          typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
            (false, evmSinSolm, outSin) false := by
        simpa [evmSinSolm, hVatAddrOrig] using hcallSinSolmRaw
      exact vowFlopSin0CallFailureBodyCore (acc := (cA_sin, σ_sin))
        hcode hwv hdispatch hdecode (by simpa using rd1277) hoszSin hvatCodeSolm
        hcallSinSolm
    · have rd1277True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
          (⟨1⟩ :: healSinEndPtr :: healSinSelector ::
            kissDaiTargetWord σ_evm I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ ::
              vowSelWord I :: [])
          (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
          (UInt256.ofNat 6) outSin (cA_sin, σ_sin) k1277 C1277 := by
        simpa using rd1277
      have hcallSinEvm :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "sin" 0 [.address I.codeOwner]
            (true,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_sin
                  substate := A_sin
                  createdAccounts := cA_sin },
              outSin) false := by
        simpa using hcallSinEvmRaw
      obtain ⟨σ_sin_solm, A_sin_solm, hcallSinSolmRaw, hStateSinRaw⟩ :=
        typedCallViaEVM_initState_EVMStateEquiv hcallSinEvm
          (by simp [initState]) hAccounts
      let evmSinEvm :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin
            substate := A_sin
            createdAccounts := cA_sin }
      let evmSinSolm :=
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin_solm
            substate := A_sin_solm
            createdAccounts := cA_sin }
      have hcallSinSolm :
          typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
            (true, evmSinSolm, outSin) false := by
        simpa [evmSinSolm, hVatAddrOrig] using hcallSinSolmRaw
      have hStateSin : EVMStateEquiv evmSinEvm evmSinSolm := by
        simpa [evmSinEvm, evmSinSolm] using hStateSinRaw
      by_cases ho32Sin : 32 ≤ outSin.size
      · let vatSin : UInt256 :=
          UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
        have hdecSin :
            config.externalABI.decode? "sin" outSin =
              some [.int (Int.ofNat vatSin.toNat)] := by
          simpa [vatSin] using vatSinDecode_ok (o := outSin) ho32Sin
        have hslotLoad : ∀ slot : UInt256,
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner slot =
              vowSlotWord slot σ_sin I := by
          intro slot
          have h := hStateSin.storageLoad_codeOwner slot
          rw [← h]
          simp [evmSinEvm, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, vowSlotWord, solcSlotWord]
        let SinVal : UInt256 := vowSlotWord ⟨5⟩ σ_sin I
        let AshVal : UInt256 := vowSlotWord ⟨6⟩ σ_sin I
        let SumpVal : UInt256 := vowSlotWord ⟨9⟩ σ_sin I
        have hSinLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨5⟩ =
              SinVal := by
          simpa [SinVal] using hslotLoad ⟨5⟩
        by_cases hfreeUnder : vatSin.toNat < SinVal.toNat
        · exact vowFlopFreeSinUnderflowBodyCore
            (cA' := cA_sin) (σ'_evm := σ_sin) (evmSin := evmSinSolm)
            hcode hwv hdispatch hdecode rd1277True hcallSinSolm hoszSin ho32Sin
            hvatCodeSolm hSinLoad (by simp [SinVal]) hfreeUnder (by simp [vatSin])
        have hfreeOk : SinVal.toNat ≤ vatSin.toNat := by omega
        have hminSin :
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
          kissDaiMin32_toNat_of_ge ho32Sin hoszSin
        have rd1277Write := rd1277True
        rw [hminSin] at rd1277Write
        obtain ⟨_, _, rd1295⟩ :=
          RD.vowHealSinCallSuccessToDecode rd1277Write (by simp)
        have hmemSin :
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size = 164 :=
          initialHealSinWrite_size I outSin 32 (by omega) ho32Sin
        have hread64Sin :
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
              64 32 = UInt256.toByteArray ⟨128⟩ :=
          initialHealSinWrite_read64 I outSin 32 (by omega) ho32Sin
        have hmload64Sin :
            (if (⟨64⟩ : UInt256).toNat ≥
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
               ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemSin]; decide) (by decide) hread64Sin
        have hmload128Sin :
            (if (⟨128⟩ : UInt256).toNat ≥
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
               ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
                  (⟨128⟩ : UInt256).toNat 32))) =
              UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)) := by
          have hnot :
              ¬ ((⟨128⟩ : UInt256).toNat ≥
                    (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
                  ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
            rw [hmemSin]
            native_decide
          rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            initialHealSinWrite_read128_32 I outSin ho32Sin]
        obtain ⟨_, _, rd1318⟩ :=
          RD.vowFlopSin0ReturnDecodeOk
            (retWord := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)))
            rd1295 ho32Sin hoszSin hmload64Sin hmload128Sin
        let freeSin : UInt256 := UInt256.sub vatSin SinVal
        obtain ⟨_, _, rd1325⟩ :=
          RD.vowFlopFreeSinSubSuccess (vatSin := vatSin)
            (by simpa [vatSin] using rd1318) (by simpa [SinVal] using hfreeOk)
        have hAshLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨6⟩ =
              AshVal := by
          simpa [AshVal] using hslotLoad ⟨6⟩
        by_cases hdebtUnder : freeSin.toNat < AshVal.toNat
        · exact vowFlopDebtUnderflowBodyCore (acc := (cA_sin, σ_sin))
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode rd1325
            (by simpa [AshVal] using hdebtUnder)
            hvatCodeSolm hcallSinSolm hdecSin hSinLoad
            rfl hfreeOk hAshLoad
        have hdebtOk : AshVal.toNat ≤ freeSin.toNat := by omega
        let flopDebt : UInt256 := UInt256.sub freeSin AshVal
        obtain ⟨_, _, rd3675⟩ :=
          RD.vowFlopDebtSubSuccess (freeSin := freeSin)
            rd1325 (by simpa [AshVal] using hdebtOk)
        have hSumpLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨9⟩ =
              SumpVal := by
          simpa [SumpVal] using hslotLoad ⟨9⟩
        by_cases hinsuff : flopDebt.toNat < SumpVal.toNat
        · exact vowFlopInsufficientDebtBodyCore (acc := (cA_sin, σ_sin))
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode rd3675
            (by simpa [SumpVal] using hinsuff)
            hmemSin hread64Sin hvatCodeSolm hcallSinSolm hdecSin hSinLoad
            (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            rfl hdebtOk hSumpLoad
        have henough : SumpVal.toNat ≤ flopDebt.toNat := by omega
        have hAccountsSin : accountMapEquiv σ_sin evmSinSolm.accountMap := by
          simpa [evmSinEvm] using hStateSin.accountMap
        have hSlotSinSolm : ∀ slot : UInt256,
            vowSlotWord slot σ_sin I = vowSlotWord slot σ_sin_solm I := by
          intro slot
          simpa [evmSinSolm] using vowSlotWord_accountMapEquiv hAccountsSin slot
        have hSlotSolmStatic : ∀ slot : UInt256,
            vowSlotWord slot σ_sin_solm I = vowSlotWord slot σ_solm I := by
          intro slot
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_solm)
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (evm' := evmSinSolm) (slot := slot) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_solm)
            hcallSinSolm
          simpa [evmSinSolm, initState, vowSlotWord, solcSlotWord] using h
        have hvatLoadSin :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
              vowSlotWord ⟨1⟩ σ_solm I := by
          rw [hslotLoad, hSlotSinSolm, hSlotSolmStatic]
        have hVatAddrSin : kissVatAddress σ_sin I = kissVatAddress σ_solm I := by
          apply Fin.ext
          have hslot : vowSlotWord ⟨1⟩ σ_sin I = vowSlotWord ⟨1⟩ σ_solm I := by
            rw [hSlotSinSolm, hSlotSolmStatic]
          simp [kissVatAddress, vowAddressReturnWord, hslot]
        have hTargetSinSolm :
            kissDaiTargetWord evmSinSolm.accountMap I = kissDaiTargetWord σ_solm I := by
          have hslot :
              vowSlotWord ⟨1⟩ evmSinSolm.accountMap I = vowSlotWord ⟨1⟩ σ_solm I := by
            simpa [evmSinSolm] using hSlotSolmStatic ⟨1⟩
          simp [kissDaiTargetWord, hslot]
        have haddrDai :
            kissVatAddress σ_solm I =
              AccountAddress.ofUInt256 (kissDaiTargetWord evmSinSolm.accountMap I) := by
          rw [hTargetSinSolm]
          exact kissVatAddress_eq_daiTarget_account σ_solm I
        have henoughEvm :
            (vowSlotWord ⟨9⟩ (cA_sin, σ_sin).2 I).toNat ≤ flopDebt.toNat := by
          simpa [SumpVal] using henough
        by_cases hcodeSizeDai :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) =
              ⟨0⟩
        · have hcodeSizeDaiSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord evmSinSolm.accountMap
                  (kissDaiTargetWord evmSinSolm.accountMap I) = ⟨0⟩ :=
            kissDaiCodeSize_zero_accountMapEquiv hAccountsSin hcodeSizeDai
          have hvatNoCodeDai :
              (UInt256.ofNat
                ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                  (fun acc => acc.code.size))).toNat = 0 := by
            simpa [State.lookupAccount] using
              uniswapExtCodeSizeWord_zero_lookup_code_zero
                (σ := evmSinSolm.accountMap)
                (target := kissDaiTargetWord evmSinSolm.accountMap I)
                (addr := kissVatAddress σ_solm I) haddrDai hcodeSizeDaiSolm
          exact vowFlopDai1NoCodeBodyCore (acc := (cA_sin, σ_sin))
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode
            (by simpa [flopDebt, freeSin, AshVal] using rd3675)
            henoughEvm hmemSin hread64Sin hcodeSizeDai hvatCodeSolm hcallSinSolm
            hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad
            (by simp [SumpVal]) hvatLoadSin hvatNoCodeDai
        have hcodeSizeDaiNE :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) ≠
              ⟨0⟩ :=
          hcodeSizeDai
        have hcodeSizeDaiSolmNE :
            Reasoning.Theory.uniswapExtCodeSizeWord evmSinSolm.accountMap
                (kissDaiTargetWord evmSinSolm.accountMap I) ≠ ⟨0⟩ :=
          kissDaiCodeSize_ne_accountMapEquiv hAccountsSin hcodeSizeDaiNE
        have hvatCodeDai :
            0 < (UInt256.ofNat
              ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
                (fun acc => acc.code.size))).toNat := by
          simpa [State.lookupAccount] using
            uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
              (σ := evmSinSolm.accountMap)
              (target := kissDaiTargetWord evmSinSolm.accountMap I)
              (addr := kissVatAddress σ_solm I) haddrDai hcodeSizeDaiSolmNE
        obtain ⟨cA_dai, σ_dai, zDai, outDai, A_dai, k3832, C3832,
            rd3832, hcallDaiEvmRaw, hoszDai⟩ :=
          RD.vowFlopDai1PostCall (by simpa [flopDebt, freeSin, AshVal] using rd3675)
            henoughEvm hmemSin hread64Sin hcodeSizeDaiNE hdepthLt
        let evmDaiEvmIn :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_sin
              createdAccounts := cA_sin }
        let evmDaiEvmOut :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai
              substate := A_dai
              createdAccounts := cA_dai }
        have hcallDaiEvm :
            typedCallViaEVM config evmDaiEvmIn
              (EVM.address (kissVatAddress σ_sin I)) "dai" 0 [.address I.codeOwner]
              (zDai, evmDaiEvmOut, outDai) false := by
          simpa [evmDaiEvmIn, evmDaiEvmOut] using hcallDaiEvmRaw
        let evmDaiSolmBase := { evmSinSolm with substate := evmDaiEvmIn.substate }
        have hcallCreated :
            evmDaiSolmBase.createdAccounts = evmDaiEvmIn.createdAccounts := by
          simp [evmDaiSolmBase, evmDaiEvmIn, evmSinSolm]
        have hcallEnv : evmDaiSolmBase.executionEnv = evmDaiEvmIn.executionEnv := by
          simp [evmDaiSolmBase, evmDaiEvmIn, evmSinSolm, initState]
        obtain ⟨σ_dai_solm, A_dai_solm0, hcallDaiSolmBase, hAccountsDai⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evmDaiSolmBase)
            hcallDaiEvm hAccountsSin
            (by simp [evmDaiEvmIn, evmDaiSolmBase, evmSinSolm, initState])
            hcallCreated
            (by simp [evmDaiEvmIn, evmDaiSolmBase, evmSinSolm, initState])
            (by simp [evmDaiEvmIn, evmDaiSolmBase, evmSinSolm, initState])
            (by simp [evmDaiSolmBase])
            hcallEnv
        have hdepthNeI : I.depth ≠ 1024 := by
          intro hdepthEq
          rw [hdepthEq] at hdepthLt
          norm_num at hdepthLt
        have hdepthNeBase : evmDaiSolmBase.executionEnv.depth ≠ 1024 := by
          simpa [evmDaiSolmBase, evmSinSolm, initState] using hdepthNeI
        obtain ⟨A_dai_solm, hcallDaiSolmRaw⟩ :=
          typedCallViaEVM_zero_setSubstate hcallDaiSolmBase hdepthNeBase
            evmSinSolm.substate
        let evmDaiSolm :=
          { evmSinSolm with
              accountMap := σ_dai_solm
              substate := A_dai_solm
              createdAccounts := cA_dai }
        have hcallDaiSolm :
            typedCallViaEVM config evmSinSolm
              (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
              (zDai, evmDaiSolm, outDai) false := by
          simpa [evmDaiSolm, evmDaiSolmBase, hVatAddrSin] using hcallDaiSolmRaw
        cases zDai
        · exact vowFlopDai1CallFailureBodyCore (acc := (cA_dai, σ_dai))
            (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
            hcode hwv hdispatch hdecode (by simpa using rd3832) hoszDai
            hvatCodeSolm hcallSinSolm hdecSin hSinLoad
            (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough
            hvatLoadSin hvatCodeDai (by simpa using hcallDaiSolm)
        · have rd3832True : RD vowBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
                kissDaiTargetWord (cA_sin, σ_sin).2 I :: ⟨0⟩ :: ⟨357⟩ ::
                  vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMem I
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k3832 C3832 := by
            simpa using rd3832
          have hcallDaiSolmTrue :
              typedCallViaEVM config evmSinSolm
                (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
                (true, evmDaiSolm, outDai) false := by
            simpa using hcallDaiSolm
          by_cases ho32Dai : 32 ≤ outDai.size
          · let vatDai : UInt256 :=
              UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
            have hdecDai :
                config.externalABI.decode? "dai" outDai =
                  some [.int (Int.ofNat vatDai.toNat)] := by
              simpa [vatDai] using kissDaiDecode_ok (o := outDai) ho32Dai
            by_cases hvatDaiNonzero : vatDai.toNat ≠ 0
            · exact vowFlopDai1SurplusNotZeroBodyCore (acc := (cA_dai, σ_dai))
                (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                hcode hwv hdispatch hdecode rd3832True hmemSin hread64Sin ho32Dai
                hoszDai (by simp [vatDai]) hvatDaiNonzero hvatCodeSolm
                hcallSinSolm hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk
                hAshLoad (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad
                henough hvatLoadSin hvatCodeDai hcallDaiSolmTrue
            have hvatDaiZero : vatDai = ⟨0⟩ := by
              apply u256_inj
              have hzeroNat : vatDai.toNat = 0 := not_not.mp hvatDaiNonzero
              simpa using hzeroNat
            have hStateDai : EVMStateEquiv evmDaiEvmOut evmDaiSolm := by
              refine ⟨?_, ?_, ?_⟩
              · simp [evmDaiEvmOut, evmDaiSolm, evmSinSolm, initState]
              · simp [evmDaiEvmOut, evmDaiSolm]
              · simpa [evmDaiEvmOut, evmDaiSolm] using hAccountsDai
            have hslotDaiLoad : ∀ slot : UInt256,
                Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner slot =
                  vowSlotWord slot σ_dai I := by
              intro slot
              have h := hStateDai.storageLoad_codeOwner slot
              rw [← h]
              simp [evmDaiEvmOut, initState, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, vowSlotWord, solcSlotWord]
            let AshValDai : UInt256 := vowSlotWord ⟨6⟩ σ_dai I
            let SumpValDai : UInt256 := vowSlotWord ⟨9⟩ σ_dai I
            have hAshLoadDai :
                Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨6⟩ =
                  AshValDai := by
              simpa [AshValDai] using hslotDaiLoad ⟨6⟩
            have hSumpLoadDai :
                Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨9⟩ =
                  SumpValDai := by
              simpa [SumpValDai] using hslotDaiLoad ⟨9⟩
            by_cases hover :
                UInt256.size ≤ AshValDai.toNat + SumpValDai.toNat
            · exact vowFlopAshAddOverflowBodyCore (acc := (cA_dai, σ_dai))
                (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                hcode hwv hdispatch hdecode rd3832True hmemSin hread64Sin ho32Dai
                hoszDai (by simp [vatDai]) hvatDaiZero hvatCodeSolm hcallSinSolm
                hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk hAshLoad
                (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough
                hvatLoadSin hvatCodeDai hcallDaiSolmTrue hAshLoadDai hSumpLoadDai
                (by simp [AshValDai]) (by simp [SumpValDai]) hover
            have hfit : AshValDai.toNat + SumpValDai.toNat < UInt256.size := by
              omega
            let AshNew : UInt256 := AshValDai + SumpValDai
            let σAshEvm : AccountMap := sstoreAccountMap I.codeOwner σ_dai ⟨6⟩ AshNew
            let evmAshEvm :=
              Solm.EVM.storageStore evmDaiEvmOut evmDaiEvmOut.executionEnv.codeOwner
                ⟨6⟩ AshNew
            let evmAshSolm :=
              Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                ⟨6⟩ AshNew
            have hStateAsh : EVMStateEquiv evmAshEvm evmAshSolm := by
              simpa [evmAshEvm, evmAshSolm] using
                hStateDai.storageStore_codeOwner ⟨6⟩ (show AshNew = AshNew from rfl)
            have hAccountsAsh : accountMapEquiv σAshEvm evmAshSolm.accountMap := by
              simpa [σAshEvm, evmAshEvm, evmDaiEvmOut, evmAshSolm,
                storageStore_accountMap, initState] using hStateAsh.accountMap
            have hslotAshLoad : ∀ slot : UInt256,
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner slot =
                  vowSlotWord slot σAshEvm I := by
              intro slot
              have h := hStateAsh.storageLoad_codeOwner slot
              rw [← h]
              have howner : evmAshEvm.executionEnv.codeOwner = I.codeOwner := by
                simp [evmAshEvm, evmDaiEvmOut, initState, storageStore_executionEnv]
              simpa [evmAshEvm, σAshEvm, storageStore_accountMap] using
                storageLoad_codeOwner_eq_vowSlotWord evmAshEvm I slot howner
            let DumpVal : UInt256 := vowSlotWord ⟨8⟩ σAshEvm I
            let SumpValKick : UInt256 := vowSlotWord ⟨9⟩ σAshEvm I
            have hDumpLoadAsh :
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner ⟨8⟩ =
                  DumpVal := by
              simpa [DumpVal] using hslotAshLoad ⟨8⟩
            have hSumpLoadAsh :
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner ⟨9⟩ =
                  SumpValKick := by
              simpa [SumpValKick] using hslotAshLoad ⟨9⟩
            have hTargetAshEq :
                vowAddressReturnWord ⟨3⟩ σAshEvm I =
                  vowAddressReturnWord ⟨3⟩ evmAshSolm.accountMap I := by
              have hslot := vowSlotWord_accountMapEquiv (I := I) hAccountsAsh ⟨3⟩
              simp [vowAddressReturnWord, hslot]
            by_cases hcodeSizeKick :
                Reasoning.Theory.uniswapExtCodeSizeWord σAshEvm
                  (vowAddressReturnWord ⟨3⟩ σAshEvm I) = ⟨0⟩
            · have hcodeSizeKickSolm :
                  Reasoning.Theory.uniswapExtCodeSizeWord evmAshSolm.accountMap
                    (vowAddressReturnWord ⟨3⟩ evmAshSolm.accountMap I) = ⟨0⟩ := by
                have hsame :=
                  Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccountsAsh
                    (vowAddressReturnWord ⟨3⟩ σAshEvm I)
                have hzeroAtEvmTarget :
                    Reasoning.Theory.uniswapExtCodeSizeWord evmAshSolm.accountMap
                      (vowAddressReturnWord ⟨3⟩ σAshEvm I) = ⟨0⟩ := by
                  rw [← hsame]
                  exact hcodeSizeKick
                simpa [hTargetAshEq] using hzeroAtEvmTarget
              have hownerAshSolm : evmAshSolm.executionEnv.codeOwner = I.codeOwner := by
                simp [evmAshSolm, evmDaiSolm, evmSinSolm, initState, storageStore_executionEnv]
              have hflopperNoCode :
                  (UInt256.ofNat
                    ((evmAshSolm.lookupAccount (flopFlopperAddressOf evmAshSolm)).option 0
                      (fun acc => acc.code.size))).toNat = 0 :=
                flopFlopperCode_zero_of_codeSize_zero evmAshSolm I hownerAshSolm
                  hcodeSizeKickSolm
              exact vowFlopKickNoCodeBodyCore (acc := (cA_dai, σ_dai))
                (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                hcode hwv hperm hdispatch hdecode rd3832True hmemSin hread64Sin
                ho32Dai hoszDai (by simp [vatDai]) hvatDaiZero hvatCodeSolm
                hcallSinSolm hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk
                hAshLoad (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad
                henough hvatLoadSin hvatCodeDai hcallDaiSolmTrue
                hAshLoadDai hSumpLoadDai (by simp [AshValDai]) (by simp [SumpValDai])
                rfl hfit (by simpa [evmAshSolm] using hflopperNoCode)
                (by simpa [σAshEvm, AshNew] using hcodeSizeKick)
            have hcodeSizeKickNE :
                Reasoning.Theory.uniswapExtCodeSizeWord σAshEvm
                  (vowAddressReturnWord ⟨3⟩ σAshEvm I) ≠ ⟨0⟩ :=
              hcodeSizeKick
            let memDai :=
              outDai.write 0
                (vatDaiCalldataMem I
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32))
                128 32
            have hmemDai : memDai.size = 164 := by
              simpa [memDai] using
                vatDaiWrite_size I outDai 32 hmemSin (by omega) ho32Dai
            have hread64Dai :
                memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
              simpa [memDai] using
                vatDaiWrite_read64 I outDai 32 hmemSin hread64Sin (by omega) ho32Dai
            have hfitEvm :
                (vowSlotWord ⟨6⟩ (cA_dai, σ_dai).2 I).toNat +
                    (vowSlotWord ⟨9⟩ (cA_dai, σ_dai).2 I).toNat <
                  UInt256.size := by
              simpa [AshValDai, SumpValDai] using hfit
            obtain ⟨k3959, C3959, rd3959Raw⟩ :=
              RD.vowFlopToKickStart rd3832True hmemSin hread64Sin ho32Dai
                hoszDai (by simp [vatDai]) hvatDaiZero hfitEvm
            have rd3959 : RD vowBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
                (AshNew :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
                memDai (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k3959 C3959 := by
              simpa [memDai, AshNew, AshValDai, SumpValDai] using rd3959Raw
            have hcodeSizeKickSolmNE :
                Reasoning.Theory.uniswapExtCodeSizeWord evmAshSolm.accountMap
                  (vowAddressReturnWord ⟨3⟩ evmAshSolm.accountMap I) ≠ ⟨0⟩ := by
              intro hzero
              apply hcodeSizeKickNE
              have hsame :=
                Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccountsAsh
                  (vowAddressReturnWord ⟨3⟩ σAshEvm I)
              have hzeroAtEvmTarget :
                  Reasoning.Theory.uniswapExtCodeSizeWord evmAshSolm.accountMap
                    (vowAddressReturnWord ⟨3⟩ σAshEvm I) = ⟨0⟩ := by
                simpa [hTargetAshEq] using hzero
              rw [hsame]
              exact hzeroAtEvmTarget
            have hownerAshSolm : evmAshSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmAshSolm, evmDaiSolm, evmSinSolm, initState, storageStore_executionEnv]
            have hflopperCode :
                0 < (UInt256.ofNat
                  ((evmAshSolm.lookupAccount (flopFlopperAddressOf evmAshSolm)).option 0
                    (fun acc => acc.code.size))).toNat :=
              flopFlopperCode_pos_of_codeSize_ne evmAshSolm I hownerAshSolm
                hcodeSizeKickSolmNE
            obtain ⟨cA_kick, σ_kick, zKick, outKick, A_kick, k1498, C1498,
                rd1498, hcallKickEvmRaw, houtKickSize⟩ :=
              RD.vowFlopKickPostCall rd3959 hperm hmemDai hread64Dai
                (by simpa [σAshEvm, AshNew] using hcodeSizeKickNE) hdepthLt
            let evmKickEvmIn :=
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σAshEvm
                  createdAccounts := cA_dai }
            let evmKickEvmOut :=
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_kick
                  substate := A_kick
                  createdAccounts := cA_kick }
            have hFlopperAddrAsh :
                flopFlopperAddressOf evmAshSolm =
                  AccountAddress.ofUInt256
                    (vowAddressReturnWord ⟨3⟩ evmAshSolm.accountMap I) :=
              flopFlopperAddressOf_eq_vowAddressReturnWord evmAshSolm I hownerAshSolm
            have hKickTargetAddr :
                EVM.address (AccountAddress.ofNat
                    (vowAddressReturnWord ⟨3⟩ σAshEvm I).toNat) =
                  EVM.address (flopFlopperAddressOf evmAshSolm) := by
              calc
                EVM.address (AccountAddress.ofNat
                    (vowAddressReturnWord ⟨3⟩ σAshEvm I).toNat)
                    = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨3⟩ σAshEvm I) :=
                      flopKickAddress_eq_target σAshEvm I
                _ = AccountAddress.ofUInt256
                    (vowAddressReturnWord ⟨3⟩ evmAshSolm.accountMap I) := by
                      rw [hTargetAshEq]
                _ = EVM.address (flopFlopperAddressOf evmAshSolm) := by
                      rw [← hFlopperAddrAsh]
                      apply Eq.symm
                      apply Fin.ext
                      simp [EVM.address, EVM.uintN]
                      exact Nat.mod_eq_of_lt
                        (by simp [EVM.twoPow, AccountAddress.size])
            have hcallKickEvm :
                typedCallViaEVM config evmKickEvmIn
                  (EVM.address (flopFlopperAddressOf evmAshSolm)) "kick" 0
                  [.address I.codeOwner, .int (Int.ofNat DumpVal.toNat),
                    .int (Int.ofNat SumpValKick.toNat)]
                  (zKick, evmKickEvmOut, outKick) true := by
              simpa [evmKickEvmIn, evmKickEvmOut, σAshEvm, AshNew, DumpVal,
                SumpValKick, hKickTargetAddr] using hcallKickEvmRaw
            let evmKickSolmBase := { evmAshSolm with substate := evmKickEvmIn.substate }
            have hcallCreatedKick :
                evmKickSolmBase.createdAccounts = evmKickEvmIn.createdAccounts := by
              simp [evmKickSolmBase, evmKickEvmIn, evmAshSolm, evmDaiSolm,
                evmSinSolm, initState, storageStore_createdAccounts]
            have hcallEnvKick :
                evmKickSolmBase.executionEnv = evmKickEvmIn.executionEnv := by
              simp [evmKickSolmBase, evmKickEvmIn, evmAshSolm, evmDaiSolm,
                evmSinSolm, initState, storageStore_executionEnv]
            obtain ⟨σ_kick_solm, A_kick_solm0, hcallKickSolmBase,
                hAccountsKick⟩ :=
              typedCallViaEVM_accountMapEquiv (evm_solm := evmKickSolmBase)
                hcallKickEvm hAccountsAsh
                (by
                  simp [evmKickEvmIn, evmKickSolmBase, evmAshSolm, evmDaiSolm,
                    evmSinSolm, initState, storageStore_σ₀])
                hcallCreatedKick
                (by
                  simp [evmKickEvmIn, evmKickSolmBase, evmAshSolm, evmDaiSolm,
                    evmSinSolm, initState, storageStore_genesisBlockHeader])
                (by
                  simp [evmKickEvmIn, evmKickSolmBase, evmAshSolm, evmDaiSolm,
                    evmSinSolm, initState, storageStore_blocks])
                (by simp [evmKickSolmBase])
                hcallEnvKick
            have hdepthNeBaseKick : evmKickSolmBase.executionEnv.depth ≠ 1024 := by
              simpa [evmKickSolmBase, evmAshSolm, evmDaiSolm, evmSinSolm, initState,
                storageStore_executionEnv] using hdepthNeI
            obtain ⟨A_kick_solm, hcallKickSolmRaw⟩ :=
              typedCallViaEVM_zero_setSubstate hcallKickSolmBase hdepthNeBaseKick
                evmAshSolm.substate
            let evmKickSolm :=
              { evmAshSolm with
                  accountMap := σ_kick_solm
                  substate := A_kick_solm
                  createdAccounts := cA_kick }
            have hcallKickSolm :
                typedCallViaEVM config evmAshSolm
                  (EVM.address (flopFlopperAddressOf evmAshSolm)) "kick" 0
                  [.address evmAshSolm.executionEnv.codeOwner,
                    .int (Int.ofNat DumpVal.toNat), .int (Int.ofNat SumpValKick.toNat)]
                  (zKick, evmKickSolm, outKick) true := by
              simpa [evmKickSolm, evmKickSolmBase, hownerAshSolm] using hcallKickSolmRaw
            cases zKick
            · exact vowFlopKickCallFailureBodyCore (acc := (cA_kick, σ_kick))
                (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                (evmKick := evmKickSolm)
                hcode hwv hdispatch hdecode (by simpa using rd1498) houtKickSize
                hvatCodeSolm hcallSinSolm hdecSin hSinLoad (by simp [freeSin, SinVal])
                hfreeOk hAshLoad (by simp [flopDebt, freeSin, AshVal]) hdebtOk
                hSumpLoad henough hvatLoadSin hvatCodeDai hcallDaiSolmTrue hdecDai
                hvatDaiZero hAshLoadDai hSumpLoadDai rfl hfit
                (by simpa [evmAshSolm] using hDumpLoadAsh)
                (by simpa [evmAshSolm] using hSumpLoadAsh)
                (by simpa [evmAshSolm] using hflopperCode)
                (by simpa [evmAshSolm] using hcallKickSolm)
            · have rd1498True : RD vowBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
                  (⟨1⟩ :: flopKickEndPtr :: flopKickSelectorWord ::
                    vowAddressReturnWord ⟨3⟩ σAshEvm I :: ⟨0⟩ :: ⟨357⟩ ::
                      vowSelWord I :: [])
                  (outKick.write 0
                    (flopKickCalldataMem I DumpVal SumpValKick memDai)
                    flopKickOutPtr.toNat
                    (min flopKickOutSize (UInt256.ofNat outKick.size)).toNat)
                  (UInt256.ofNat 8) outKick (cA_kick, σ_kick) k1498 C1498 := by
                simpa [σAshEvm, AshNew, DumpVal, SumpValKick] using rd1498
              have hcallKickSolmTrue :
                  typedCallViaEVM config evmAshSolm
                    (EVM.address (flopFlopperAddressOf evmAshSolm)) "kick" 0
                    [.address evmAshSolm.executionEnv.codeOwner,
                      .int (Int.ofNat DumpVal.toNat), .int (Int.ofNat SumpValKick.toNat)]
                    (true, evmKickSolm, outKick) true := by
                simpa using hcallKickSolm
              by_cases ho32Kick : 32 ≤ outKick.size
              · let id : UInt256 :=
                  UInt256.ofNat (fromByteArrayBigEndian (outKick.extract 0 32))
                have hcreatedFinal : (cA_kick, σ_kick).1 = evmKickSolm.createdAccounts := by
                  rfl
                have hAccountsFinal : accountMapEquiv (cA_kick, σ_kick).2
                    evmKickSolm.accountMap := by
                  simpa [evmKickEvmOut, evmKickSolm] using hAccountsKick
                exact vowFlopKickSuccessBodyCore (acc := (cA_kick, σ_kick))
                  (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                  (evmKick := evmKickSolm) (id := id)
                  hcode hwv hdispatch hdecode (by simpa using rd1498True)
                  hmemDai hread64Dai ho32Kick houtKickSize rfl hvatCodeSolm
                  hcallSinSolm hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk
                  hAshLoad (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad
                  henough hvatLoadSin hvatCodeDai hcallDaiSolmTrue hdecDai hvatDaiZero
                  hAshLoadDai hSumpLoadDai rfl hfit
                  (by simpa [evmAshSolm] using hDumpLoadAsh)
                  (by simpa [evmAshSolm] using hSumpLoadAsh)
                  (by simpa [evmAshSolm] using hflopperCode)
                  (by simpa [evmAshSolm] using hcallKickSolmTrue)
                  hcreatedFinal hAccountsFinal
              · have hshortKick : outKick.size < 32 := Nat.lt_of_not_ge ho32Kick
                have hminKick :
                    (min flopKickOutSize (UInt256.ofNat outKick.size)).toNat =
                      outKick.size := by
                  simpa [flopKickOutSize] using kissDaiMin32_toNat_of_lt hshortKick
                have rd1498Short := rd1498True
                rw [hminKick, show flopKickOutPtr.toNat = 128 from by native_decide] at rd1498Short
                obtain ⟨k1516, C1516, rd1516⟩ :=
                  RD.vowFlopKickCallSuccessToDecode rd1498Short (by simp)
                have hmemKickShort :
                    (outKick.write 0 (flopKickCalldataMem I DumpVal SumpValKick memDai)
                        128 outKick.size).size = 228 :=
                  flopKickWrite_size I DumpVal SumpValKick outKick outKick.size hmemDai
                    (by omega) (by omega)
                have hread64KickShort :
                    (outKick.write 0 (flopKickCalldataMem I DumpVal SumpValKick memDai)
                        128 outKick.size).readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ :=
                  flopKickWrite_read64 I DumpVal SumpValKick outKick outKick.size hmemDai
                    hread64Dai (by omega) (by omega)
                have hmload64KickShort :
                    (if (⟨64⟩ : UInt256).toNat ≥
                          (outKick.write 0 (flopKickCalldataMem I DumpVal SumpValKick memDai)
                            128 outKick.size).size
                        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
                     else UInt256.ofNat
                       (fromByteArrayBigEndian
                        ((outKick.write 0
                          (flopKickCalldataMem I DumpVal SumpValKick memDai)
                          128 outKick.size).readWithPadding
                          (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ :=
                  mloadFreePtrValue (by rw [hmemKickShort]; decide) (by decide)
                    hread64KickShort
                exact vowFlopKickDecodeShortBodyCore (acc := (cA_kick, σ_kick))
                  (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
                  (evmKick := evmKickSolm)
                  hcode hwv hdispatch hdecode (by simpa using rd1516)
                  hshortKick houtKickSize hmload64KickShort hvatCodeSolm hcallSinSolm
                  hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk hAshLoad
                  (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough
                  hvatLoadSin hvatCodeDai hcallDaiSolmTrue hdecDai hvatDaiZero
                  hAshLoadDai hSumpLoadDai rfl hfit
                  (by simpa [evmAshSolm] using hDumpLoadAsh)
                  (by simpa [evmAshSolm] using hSumpLoadAsh)
                  (by simpa [evmAshSolm] using hflopperCode)
                  (by simpa [evmAshSolm] using hcallKickSolmTrue)
          · have hshortDai : outDai.size < 32 := Nat.lt_of_not_ge ho32Dai
            exact vowFlopDai1DecodeShortBodyCore (acc := (cA_dai, σ_dai))
              (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
              hcode hwv hdispatch hdecode rd3832True hmemSin hread64Sin hshortDai
              hoszDai hvatCodeSolm hcallSinSolm hdecSin hSinLoad
              (by simp [freeSin, SinVal]) hfreeOk hAshLoad
              (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough
              hvatLoadSin hvatCodeDai hcallDaiSolmTrue
      · have hshortRet : outSin.size < 32 := Nat.lt_of_not_ge ho32Sin
        have hminShort :
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat =
              outSin.size :=
          kissDaiMin32_toNat_of_lt hshortRet
        have rd1277Short := rd1277True
        rw [hminShort] at rd1277Short
        obtain ⟨_, _, rd1295⟩ :=
          RD.vowHealSinCallSuccessToDecode rd1277Short (by simp)
        have hmemShort :
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size =
              164 :=
          initialHealSinWrite_size I outSin outSin.size (by omega) (by omega)
        have hread64Short :
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
                64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          initialHealSinWrite_read64 I outSin outSin.size (by omega) (by omega)
        have hmload64Short :
            (if (⟨64⟩ : UInt256).toNat ≥
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size
                ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemShort]; decide) (by decide) hread64Short
        have hrev :=
          RD.vowFlopSin0ReturnDecodeShortReverts rd1295 hshortRet hoszSin hmload64Short
        have hdecSin : config.externalABI.decode? "sin" outSin = none :=
          vatSinDecode_none_short hshortRet
        have hbody := vowFlopSourceVatSin0DecodeRevert (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmSin := evmSinSolm) (outSin := outSin)
          hwv hvatCodeSolm hcallSinSolm hdecSin
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    obtain ⟨_, _, rd1277⟩ :=
      RD.vowFlopSin0CallDepthLimit hreach hcodeSizeSinNE hdepthEq
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let A_sin := (evm0.addAccessedAccount (EVM.address (kissVatAddress σ_solm I))).substate
    have hcallSinDepth :
        typedCallViaEVM config evm0
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (false, { evm0 with accountMap := σ_solm, substate := A_sin, createdAccounts := cA },
            ByteArray.empty) false := by
      simpa [evm0, A_sin, initState] using
        (callNotMade_depthLimit (cfg := config) (evm := evm0)
          (tgt := EVM.address (kissVatAddress σ_solm I)) (name := "sin")
          (args := [.address I.codeOwner]) (callPerm := false)
          (initialHealSinEncode_eq I) (by simpa [evm0, initState] using hdepthEq))
    exact vowFlopSin0CallFailureBodyCore (acc := (cA, σ_evm))
      (evmSin := { evm0 with accountMap := σ_solm, substate := A_sin, createdAccounts := cA })
      (outSin := ByteArray.empty) hcode hwv hdispatch hdecode rd1277
      (by native_decide) hvatCodeSolm hcallSinDepth

end Benchmarks.Dss.Vow
