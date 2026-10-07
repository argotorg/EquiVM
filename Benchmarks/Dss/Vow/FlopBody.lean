import Benchmarks.Dss.Vow.FlopKick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` top-level runtime body wrapper -/

theorem kissVatCode_pos_of_codeSize_ne {σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := kissDaiTargetWord σ I) (addr := kissVatAddress σ I)
      (kissVatAddress_eq_daiTarget_account σ I) hne

theorem kissVatCode_zero_of_codeSize_zero {σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := kissDaiTargetWord σ I) (addr := kissVatAddress σ I)
      (kissVatAddress_eq_daiTarget_account σ I) hzero


theorem flopFlopperAddressOf_eq_vowAddressReturnWord (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    flopFlopperAddressOf evm =
      AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ evm.accountMap I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [flopFlopperAddressOf, solcAddressSlotWord,
    storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨3⟩ howner]

theorem flopFlopperCode_pos_of_codeSize_ne (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (solcAddressSlotWord ⟨3⟩ evm.accountMap I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := solcAddressSlotWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (flopFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hne

theorem flopFlopperCode_zero_of_codeSize_zero (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (solcAddressSlotWord ⟨3⟩ evm.accountMap I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (flopFlopperAddressOf evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := solcAddressSlotWord ⟨3⟩ evm.accountMap I)
      (addr := flopFlopperAddressOf evm)
      (flopFlopperAddressOf_eq_vowAddressReturnWord evm I howner) hzero

theorem RD.vowFlopSin0CallDepthLimit
    {σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty
      σ k' C' := by
  obtain ⟨_, _, _, rd1276⟩ := RD.vowFlopToSin0Staticcall hreach hcodeSize
  obtain ⟨k1277, C1277, rd1277raw⟩ :=
    RD.solcStaticcallDepthLimit rd1276 (by native_decide) hdepth (by evm_ov)
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
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (ByteArray.empty.write 0 (healSinCalldataMem I solcFreePtrMem) healSinOutPtr.toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty σ k1277 C1277 :=
    haw ▸ rd1277raw
  rw [hoff, hmin, byteArray_write_len_zero] at rd1277
  exact ⟨k1277, C1277, rd1277⟩

set_option maxHeartbeats 0 in
theorem vowFlopBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some flopTransition :=
    vowDispatch_flop hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flop hsz4
  have hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C :=
    vowReachFlopBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  by_cases hcodeSizeSin :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩
  · exact vowFlopVatSin0NoCodeBodyCore hcode hwv hdispatch hdecode hreach
      hcodeSizeSin
  have hcodeSizeSinNE :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩ :=
    hcodeSizeSin
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
    kissVatCode_pos_of_codeSize_ne
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSinNE
  by_cases hdepthLt : I.depth.val < 1024
  · have hdepthNeI : I.depth ≠ 1024 := by
      intro hdepthEq
      rw [hdepthEq] at hdepthLt
      norm_num at hdepthLt
    obtain ⟨σ_sin, zSin, outSin, A_sin, k1277, C1277,
        rd1277, hcallSinEvmRaw, hoszSin⟩ :=
      RD.vowFlopSin0PostCall hreach hcodeSizeSinNE hdepthLt
    cases zSin
    · let evmSinSolm :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin
            substate := A_sin
        }
      have hcallSinSolm :
          typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
            (false, evmSinSolm, outSin) false := by
        simpa [evmSinSolm] using hcallSinEvmRaw
      exact vowFlopSin0CallFailureBodyCore (acc := σ_sin)
        hcode hwv hdispatch hdecode (by simpa using rd1277) hoszSin hvatCodeSolm
        hcallSinSolm
    · have rd1277True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
          (⟨1⟩ :: healSinEndPtr :: healSinSelector ::
            kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ ::
              vowSelWord I :: [])
          (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
          (UInt256.ofNat 6) outSin σ_sin k1277 C1277 := by
        simpa using rd1277
      let evmSinEvm :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin
            substate := A_sin
        }
      let evmSinSolm := evmSinEvm
      have hcallSinSolm :
          typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
            (true, evmSinSolm, outSin) false := by
        simpa [evmSinSolm, evmSinEvm] using hcallSinEvmRaw
      by_cases ho32Sin : 32 ≤ outSin.size
      · let vatSin : UInt256 :=
          UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
        have hdecSin :
            config.externalABI.decode? "sin" outSin =
              some [.int (Int.ofNat vatSin.toNat)] := by
          simpa [vatSin] using vatSinDecode_ok (o := outSin) ho32Sin
        have hslotLoad : ∀ slot : UInt256,
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner slot =
              solcSlotWordAt slot σ_sin I := by
          intro slot
          simp [evmSinSolm, evmSinEvm, initState, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage, solcSlotWordAt, solcSlotWord]
        let SinVal : UInt256 := solcSlotWordAt ⟨5⟩ σ_sin I
        let AshVal : UInt256 := solcSlotWordAt ⟨6⟩ σ_sin I
        let SumpVal : UInt256 := solcSlotWordAt ⟨9⟩ σ_sin I
        have hSinLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨5⟩ =
              SinVal := by
          simpa [SinVal] using hslotLoad ⟨5⟩
        by_cases hfreeUnder : vatSin.toNat < SinVal.toNat
        · exact vowFlopFreeSinUnderflowBodyCore
            (σ'_evm := σ_sin) (evmSin := evmSinSolm)
            hcode hwv hdispatch hdecode rd1277True hcallSinSolm hoszSin ho32Sin
            hvatCodeSolm hSinLoad (by simp [SinVal]) hfreeUnder (by simp [vatSin])
        have hfreeOk : SinVal.toNat ≤ vatSin.toNat := by omega
        have hminSin :
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
          ctorMin32_toNat_of_ge ho32Sin hoszSin
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
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemSin]; decide) hread64Sin
        have hmload128Sin :
            (if (⟨128⟩ : UInt256).toNat ≥
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
                  (⟨128⟩ : UInt256).toNat 32))) =
              UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)) := by
          have hnot :
              ¬ ((⟨128⟩ : UInt256).toNat ≥
                    (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size) := by
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
        · exact vowFlopDebtUnderflowBodyCore (acc := σ_sin)
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
        · exact vowFlopInsufficientDebtBodyCore (acc := σ_sin)
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode rd3675
            (by simpa [SumpVal] using hinsuff)
            hmemSin hread64Sin hvatCodeSolm hcallSinSolm hdecSin hSinLoad
            (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            rfl hdebtOk hSumpLoad
        have henough : SumpVal.toNat ≤ flopDebt.toNat := by omega
        have rflSin : Eq σ_sin evmSinSolm.accountMap := rfl
        have hSlotSolmStatic : ∀ slot : UInt256,
            solcSlotWordAt slot σ_sin I = solcSlotWordAt slot σ I := by
          intro slot
          have h := typedCallViaEVM_static_storage_getD_of_accounts_eq
            (cfg := config) (σ := σ)
            (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (evm' := evmSinSolm) (slot := slot) (default := ⟨0⟩)
            (hAccounts := by simp [initState])
            hcallSinSolm
          simpa [evmSinSolm, initState, solcSlotWordAt, solcSlotWord] using h
        have hvatLoadSin :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
              solcSlotWordAt ⟨1⟩ σ I := by
          rw [hslotLoad, hSlotSolmStatic]
        have hVatAddrSin : kissVatAddress σ_sin I = kissVatAddress σ I := by
          apply Fin.ext
          have hslot : solcSlotWordAt ⟨1⟩ σ_sin I = solcSlotWordAt ⟨1⟩ σ I := by
            rw [hSlotSolmStatic]
          simp [kissVatAddress, solcAddressSlotWord, hslot]
        have hTargetSinSolm :
            kissDaiTargetWord evmSinSolm.accountMap I = kissDaiTargetWord σ I := by
          have hslot :
              solcSlotWordAt ⟨1⟩ evmSinSolm.accountMap I = solcSlotWordAt ⟨1⟩ σ I := by
            simpa [evmSinSolm] using hSlotSolmStatic ⟨1⟩
          simp [kissDaiTargetWord, hslot]
        have haddrDai :
            kissVatAddress σ I =
              AccountAddress.ofUInt256 (kissDaiTargetWord evmSinSolm.accountMap I) := by
          rw [hTargetSinSolm]
          exact kissVatAddress_eq_daiTarget_account σ I
        have henoughEvm :
            (solcSlotWordAt ⟨9⟩ σ_sin I).toNat ≤ flopDebt.toNat := by
          simpa [SumpVal] using henough
        by_cases hcodeSizeDai :
            Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) =
              ⟨0⟩
        · have hcodeSizeDaiSolm :
              Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                  (kissDaiTargetWord evmSinSolm.accountMap I) = ⟨0⟩ := by
            simpa only [← rflSin] using hcodeSizeDai
          have hvatNoCodeDai :
              (UInt256.ofNat
                ((evmSinSolm.lookupAccount (kissVatAddress σ I)).option 0
                  (fun acc => acc.code.size))).toNat = 0 := by
            simpa [State.lookupAccount] using
              extCodeSizeWord_zero_lookup_code_zero
                (σ := evmSinSolm.accountMap)
                (target := kissDaiTargetWord evmSinSolm.accountMap I)
                (addr := kissVatAddress σ I) haddrDai hcodeSizeDaiSolm
          exact vowFlopDai1NoCodeBodyCore (acc := σ_sin)
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode
            (by simpa [flopDebt, freeSin, AshVal] using rd3675)
            henoughEvm hmemSin hread64Sin hcodeSizeDai hvatCodeSolm hcallSinSolm
            hdecSin hSinLoad (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad
            (by simp [SumpVal]) hvatLoadSin hvatNoCodeDai
        have hcodeSizeDaiNE :
            Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) ≠
              ⟨0⟩ :=
          hcodeSizeDai
        have hcodeSizeDaiSolmNE :
            Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
                (kissDaiTargetWord evmSinSolm.accountMap I) ≠ ⟨0⟩ := by
          simpa only [← rflSin] using hcodeSizeDaiNE
        have hvatCodeDai :
            0 < (UInt256.ofNat
              ((evmSinSolm.lookupAccount (kissVatAddress σ I)).option 0
                (fun acc => acc.code.size))).toNat := by
          simpa [State.lookupAccount] using
            extCodeSizeWord_ne_zero_lookup_code_pos
              (σ := evmSinSolm.accountMap)
              (target := kissDaiTargetWord evmSinSolm.accountMap I)
              (addr := kissVatAddress σ I) haddrDai hcodeSizeDaiSolmNE
        obtain ⟨σ_dai, zDai, outDai, A_dai, k3832, C3832,
            rd3832, hcallDaiEvmRaw, hoszDai⟩ :=
          RD.vowFlopDai1PostCall (by simpa [flopDebt, freeSin, AshVal] using rd3675)
            henoughEvm hmemSin hread64Sin hcodeSizeDaiNE hdepthLt
        let evmDaiEvmIn :=
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_sin
          }
        let evmDaiEvmOut :=
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai
              substate := A_dai
          }
        have hcallDaiEvm :
            typedCallViaEVM config evmDaiEvmIn
              (EVM.address (kissVatAddress σ_sin I)) "dai" 0 [.address I.codeOwner]
              (zDai, evmDaiEvmOut, outDai) false := by
          simpa [evmDaiEvmIn, evmDaiEvmOut] using hcallDaiEvmRaw
        have hdepthNeDai : evmDaiEvmIn.executionEnv.depth ≠ 1024 := by
          simpa [evmDaiEvmIn, initState] using hdepthNeI
        obtain ⟨A_dai_solm, hcallDaiSolmRaw⟩ :=
          typedCallViaEVM_zero_setSubstate hcallDaiEvm hdepthNeDai evmSinSolm.substate
        let evmDaiSolm :=
          { evmSinSolm with
              accountMap := σ_dai
              substate := A_dai_solm
          }
        have hcallDaiSolm :
            typedCallViaEVM config evmSinSolm
              (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
              (zDai, evmDaiSolm, outDai) false := by
          simpa [evmDaiSolm, evmDaiEvmIn, evmDaiEvmOut, evmSinSolm, evmSinEvm,
            hVatAddrSin] using hcallDaiSolmRaw
        cases zDai
        · exact vowFlopDai1CallFailureBodyCore (acc := σ_dai)
            (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
            hcode hwv hdispatch hdecode (by simpa using rd3832) hoszDai
            hvatCodeSolm hcallSinSolm hdecSin hSinLoad
            (by simp [freeSin, SinVal]) hfreeOk hAshLoad
            (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough
            hvatLoadSin hvatCodeDai (by simpa using hcallDaiSolm)
        · have rd3832True : RD vowBytecode I (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3832⟩
              (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
                kissDaiTargetWord σ_sin I :: ⟨0⟩ :: ⟨357⟩ ::
                  vowSelWord I :: [])
              (outDai.write 0
                (vatDaiCalldataMem I
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32))
                128 (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
              (UInt256.ofNat 6) outDai σ_dai k3832 C3832 := by
            simpa using rd3832
          have hcallDaiSolmTrue :
              typedCallViaEVM config evmSinSolm
                (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
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
            · exact vowFlopDai1SurplusNotZeroBodyCore (acc := σ_dai)
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
            have hslotDaiLoad : ∀ slot : UInt256,
                Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner slot =
                  solcSlotWordAt slot σ_dai I := by
              intro slot
              simp [evmDaiSolm, evmSinSolm, evmSinEvm, initState,
                Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage,
                solcSlotWordAt, solcSlotWord]
            let AshValDai : UInt256 := solcSlotWordAt ⟨6⟩ σ_dai I
            let SumpValDai : UInt256 := solcSlotWordAt ⟨9⟩ σ_dai I
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
            · exact vowFlopAshAddOverflowBodyCore (acc := σ_dai)
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
            let evmAshSolm :=
              Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                ⟨6⟩ AshNew
            have rflAsh : Eq σAshEvm evmAshSolm.accountMap := by
              simp [σAshEvm, evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm,
                initState, storageStore_accountMap]
            have hslotAshLoad : ∀ slot : UInt256,
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner slot =
                  solcSlotWordAt slot σAshEvm I := by
              intro slot
              have howner : evmAshSolm.executionEnv.codeOwner = I.codeOwner := by
                simp [evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm, initState,
                  storageStore_executionEnv]
              simpa [evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm,
                σAshEvm, AshNew, initState, storageStore_accountMap] using
                storageLoad_codeOwner_eq_solcSlotWordAt evmAshSolm I slot howner
            let DumpVal : UInt256 := solcSlotWordAt ⟨8⟩ σAshEvm I
            let SumpValKick : UInt256 := solcSlotWordAt ⟨9⟩ σAshEvm I
            have hDumpLoadAsh :
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner ⟨8⟩ =
                  DumpVal := by
              simpa [DumpVal] using hslotAshLoad ⟨8⟩
            have hSumpLoadAsh :
                Solm.EVM.storageLoad evmAshSolm evmAshSolm.executionEnv.codeOwner ⟨9⟩ =
                  SumpValKick := by
              simpa [SumpValKick] using hslotAshLoad ⟨9⟩
            have hTargetAshEq :
                solcAddressSlotWord ⟨3⟩ σAshEvm I =
                  solcAddressSlotWord ⟨3⟩ evmAshSolm.accountMap I := by
              exact congrArg (fun accounts => solcAddressSlotWord ⟨3⟩ accounts I) rflAsh
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
                (solcSlotWordAt ⟨6⟩ σ_dai I).toNat +
                    (solcSlotWordAt ⟨9⟩ σ_dai I).toNat <
                  UInt256.size := by
              simpa [AshValDai, SumpValDai] using hfit
            obtain ⟨k3959, C3959, rd3959Raw⟩ :=
              RD.vowFlopToKickStart rd3832True hmemSin hread64Sin ho32Dai
                hoszDai (by simp [vatDai]) hvatDaiZero hfitEvm
            have rd3959 : RD vowBytecode I (Sat256.ofUInt256 g)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3959⟩
                (AshNew :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
                memDai (UInt256.ofNat 6) outDai σ_dai k3959 C3959 := by
              simpa [memDai, AshNew, AshValDai, SumpValDai] using rd3959Raw
            rcases RD.vowFlopToKickExtcodesizeGuardSplit rd3959 hmemDai hread64Dai with
              ⟨hperm, -⟩ | ⟨hpf, hstatic⟩
            swap
            · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
                (vowFlopSourceStatic (g := g) hwv hvatCodeSolm hcallSinSolm hdecSin hSinLoad
                  (by simp [freeSin, SinVal]) hfreeOk hAshLoad
                  (by simp [flopDebt, freeSin, AshVal]) hdebtOk hSumpLoad henough hvatLoadSin
                  hvatCodeDai hcallDaiSolmTrue hdecDai hvatDaiZero hAshLoadDai hSumpLoadDai rfl
                  hfit hpf)
            by_cases hcodeSizeKick :
                Reasoning.Theory.extCodeSizeWord σAshEvm
                  (solcAddressSlotWord ⟨3⟩ σAshEvm I) = ⟨0⟩
            · have hcodeSizeKickSolm :
                  Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
                    (solcAddressSlotWord ⟨3⟩ evmAshSolm.accountMap I) = ⟨0⟩ := by
                simpa [rflAsh] using hcodeSizeKick
              have hownerAshSolm : evmAshSolm.executionEnv.codeOwner = I.codeOwner := by
                simp [evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm, initState,
                  storageStore_executionEnv]
              have hflopperNoCode :
                  (UInt256.ofNat
                    ((evmAshSolm.lookupAccount (flopFlopperAddressOf evmAshSolm)).option 0
                      (fun acc => acc.code.size))).toNat = 0 :=
                flopFlopperCode_zero_of_codeSize_zero evmAshSolm I hownerAshSolm
                  hcodeSizeKickSolm
              exact vowFlopKickNoCodeBodyCore (acc := σ_dai)
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
                Reasoning.Theory.extCodeSizeWord σAshEvm
                  (solcAddressSlotWord ⟨3⟩ σAshEvm I) ≠ ⟨0⟩ :=
              hcodeSizeKick
            have hcodeSizeKickSolmNE :
                Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
                  (solcAddressSlotWord ⟨3⟩ evmAshSolm.accountMap I) ≠ ⟨0⟩ := by
              simpa [rflAsh] using hcodeSizeKickNE
            have hownerAshSolm : evmAshSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm, initState,
                storageStore_executionEnv]
            have hflopperCode :
                0 < (UInt256.ofNat
                  ((evmAshSolm.lookupAccount (flopFlopperAddressOf evmAshSolm)).option 0
                    (fun acc => acc.code.size))).toNat :=
              flopFlopperCode_pos_of_codeSize_ne evmAshSolm I hownerAshSolm
                hcodeSizeKickSolmNE
            obtain ⟨σ_kick, zKick, outKick, A_kick, k1498, C1498,
                rd1498, hcallKickEvmRaw, houtKickSize⟩ :=
              RD.vowFlopKickPostCall rd3959 hperm hmemDai hread64Dai
                (by simpa [σAshEvm, AshNew] using hcodeSizeKickNE) hdepthLt
            let evmKickEvmIn :=
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σAshEvm
              }
            let evmKickEvmOut :=
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_kick
                  substate := A_kick
              }
            have hFlopperAddrAsh :
                flopFlopperAddressOf evmAshSolm =
                  AccountAddress.ofUInt256
                    (solcAddressSlotWord ⟨3⟩ evmAshSolm.accountMap I) :=
              flopFlopperAddressOf_eq_vowAddressReturnWord evmAshSolm I hownerAshSolm
            have hKickTargetAddr :
                EVM.address (AccountAddress.ofNat
                    (solcAddressSlotWord ⟨3⟩ σAshEvm I).toNat) =
                  EVM.address (flopFlopperAddressOf evmAshSolm) := by
              calc
                EVM.address (AccountAddress.ofNat
                    (solcAddressSlotWord ⟨3⟩ σAshEvm I).toNat)
                    = AccountAddress.ofUInt256 (solcAddressSlotWord ⟨3⟩ σAshEvm I) :=
                      flopKickAddress_eq_target σAshEvm I
                _ = AccountAddress.ofUInt256
                    (solcAddressSlotWord ⟨3⟩ evmAshSolm.accountMap I) := by
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
            have hKickInput : evmKickSolmBase = evmKickEvmIn := by
              cases hFind : σ_dai.get? I.codeOwner <;>
                simp [-Std.ExtTreeMap.get?_eq_getElem?, evmKickSolmBase, evmKickEvmIn, evmAshSolm, evmDaiSolm,
                  evmSinSolm, evmSinEvm, initState, Solm.EVM.storageStore,
                  State.setAccount, State.lookupAccount, σAshEvm, sstoreAccountMap,
                  Account.updateStorage, Option.option, hFind]
            have hcallKickSolmBase :
                typedCallViaEVM config evmKickSolmBase
                  (EVM.address (flopFlopperAddressOf evmAshSolm)) "kick" 0
                  [.address I.codeOwner, .int (Int.ofNat DumpVal.toNat),
                    .int (Int.ofNat SumpValKick.toNat)]
                  (zKick,
                    { evmKickSolmBase with accountMap := σ_kick, substate := A_kick },
                    outKick) true := by
              simpa [hKickInput, evmKickEvmOut, evmKickEvmIn] using hcallKickEvm
            have hdepthNeBaseKick : evmKickSolmBase.executionEnv.depth ≠ 1024 := by
              simpa [evmKickSolmBase, evmAshSolm, evmDaiSolm, evmSinSolm, evmSinEvm, initState,
                storageStore_executionEnv] using hdepthNeI
            obtain ⟨A_kick_solm, hcallKickSolmRaw⟩ :=
              typedCallViaEVM_zero_setSubstate hcallKickSolmBase hdepthNeBaseKick
                evmAshSolm.substate
            let evmKickSolm :=
              { evmAshSolm with
                  accountMap := σ_kick
                  substate := A_kick_solm
              }
            have hcallKickSolm :
                typedCallViaEVM config evmAshSolm
                  (EVM.address (flopFlopperAddressOf evmAshSolm)) "kick" 0
                  [.address evmAshSolm.executionEnv.codeOwner,
                    .int (Int.ofNat DumpVal.toNat), .int (Int.ofNat SumpValKick.toNat)]
                  (zKick, evmKickSolm, outKick) true := by
              simpa [evmKickSolm, evmKickSolmBase, hownerAshSolm] using hcallKickSolmRaw
            cases zKick
            · exact vowFlopKickCallFailureBodyCore (acc := σ_kick)
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
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
                  (⟨1⟩ :: flopKickEndPtr :: flopKickSelectorWord ::
                    solcAddressSlotWord ⟨3⟩ σAshEvm I :: ⟨0⟩ :: ⟨357⟩ ::
                      vowSelWord I :: [])
                  (outKick.write 0
                    (flopKickCalldataMem I DumpVal SumpValKick memDai)
                    flopKickOutPtr.toNat
                    (min flopKickOutSize (UInt256.ofNat outKick.size)).toNat)
                  (UInt256.ofNat 8) outKick σ_kick k1498 C1498 := by
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
                have rflFinal : Eq σ_kick
                    evmKickSolm.accountMap := by
                  rfl
                exact vowFlopKickSuccessBodyCore (acc := σ_kick)
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
                  rflFinal
              · have hshortKick : outKick.size < 32 := Nat.lt_of_not_ge ho32Kick
                have hminKick :
                    (min flopKickOutSize (UInt256.ofNat outKick.size)).toNat =
                      outKick.size := by
                  simpa [flopKickOutSize] using ctorMin32_toNat_of_lt hshortKick
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
                            128 outKick.size).size then ⟨0⟩
                     else UInt256.ofNat
                       (fromByteArrayBigEndian
                        ((outKick.write 0
                          (flopKickCalldataMem I DumpVal SumpValKick memDai)
                          128 outKick.size).readWithPadding
                          (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ :=
                  mloadFreePtrValue (by rw [hmemKickShort]; decide)
                    hread64KickShort
                exact vowFlopKickDecodeShortBodyCore (acc := σ_kick)
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
            exact vowFlopDai1DecodeShortBodyCore (acc := σ_dai)
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
          ctorMin32_toNat_of_lt hshortRet
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
                  (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemShort]; decide) hread64Short
        have hrev :=
          RD.vowFlopSin0ReturnDecodeShortReverts rd1295 hshortRet hoszSin hmload64Short
        have hdecSin : config.externalABI.decode? "sin" outSin = none :=
          vatSinDecode_none_short hshortRet
        have hbody := vowFlopSourceVatSin0DecodeRevert
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmSin := evmSinSolm) (outSin := outSin)
          hwv hvatCodeSolm hcallSinSolm hdecSin
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    obtain ⟨_, _, rd1277⟩ :=
      RD.vowFlopSin0CallDepthLimit hreach hcodeSizeSinNE hdepthEq
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let A_sin := (evm0.addAccessedAccount (EVM.address (kissVatAddress σ I))).substate
    have hcallSinDepth :
        typedCallViaEVM config evm0
          (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
          (false, { evm0 with accountMap := σ, substate := A_sin },
            ByteArray.empty) false := by
      simpa [evm0, A_sin, initState] using
        (callNotMade_depthLimit (cfg := config) (evm := evm0)
          (tgt := EVM.address (kissVatAddress σ I)) (name := "sin")
          (args := [.address I.codeOwner]) (callPerm := false)
          (initialHealSinEncode_eq I) (by simpa [evm0, initState] using hdepthEq))
    exact vowFlopSin0CallFailureBodyCore (acc := σ)
      (evmSin := { evm0 with accountMap := σ, substate := A_sin })
      (outSin := ByteArray.empty) hcode hwv hdispatch hdecode rd1277
      (by native_decide) hvatCodeSolm hcallSinDepth

end Benchmarks.Dss.Vow
