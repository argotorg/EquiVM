import Benchmarks.Dss.Spot.PokeTraceBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

theorem spotPokeBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 8)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some pokeTransition :=
    spotDispatchPoke hsel
  have hreach := spotReachPokeBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  ·
    have hdecode := spotDecode_poke_ok (I := I) hsz36
    obtain ⟨_, _, rd598⟩ := spotPokeX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    by_cases hcodeSize :
        Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) = ⟨0⟩
    · have hpipNoCodeSolm :
          (UInt256.ofNat
            (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
              (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
        pokePipCode_zero_of_codeSize_zero
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
      have hbody :
          ExecTransitionBody config contract
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (pokeLocals I) pokeTransition.body .reverted := by
        simpa using
          (spotPokeSourceBodyPipNoCode
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hsz36 hpipNoCodeSolm)
      exact (RD.spotPokePeekNoCode hsz36 rd598 hcodeSize)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · obtain ⟨gasWord, _, _, rd679⟩ :=
        RD.spotPokePeekCallReady hsz36 rd598 hcodeSize
      have hpipCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (pokePipAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
        pokePipCode_pos_of_codeSize_ne_zero
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
      by_cases hdepthEq : I.depth = 1024
      · obtain ⟨_, _, rd680⟩ := RD.spotPokePeekCallDepthLimit rd679 hdepthEq
        let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let A_pip := (evmS.addAccessedAccount (EVM.address (pokePipAddress σ I))).substate
        have hdepthInit : evmS.executionEnv.depth = 1024 := by
          simpa [evmS, initState] using hdepthEq
        have hcallSolm :
            typedCallViaEVM config evmS (EVM.address (pokePipAddress σ I)) "peek" 0 []
              (false, { evmS with substate := A_pip }, ByteArray.empty) true := by
          simpa [A_pip] using
            (callNotMade_depthLimit (cfg := config) (evm := evmS)
              (tgt := EVM.address (pokePipAddress σ I)) (name := "peek")
              (args := []) (callPerm := true)
              (calldata := (pokePeekCalldataMem I).readWithPadding
                pokePeekOutPtr.toNat pokePeekInSize.toNat)
              (pokePeekEncode_eq I) hdepthInit)
        have hbody :
            ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (pokeLocals I) pokeTransition.body .reverted := by
          simpa [evmS] using
            (spotPokeSourceBodyPeekCallFailed
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmPip := { evmS with substate := A_pip }) (out := ByteArray.empty)
              hwv hsz36 hpipCodeSolm (by simpa [evmS] using hcallSolm))
        have hrev := RD.spotPokePeekCallFailed rd680 (by native_decide)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hdepthLt : I.depth.val < 1024 := by
          have hlt := I.depth.isLt
          by_contra hn
          have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
          have hval : I.depth.val = 1024 := by omega
          apply hdepthEq
          apply Fin.ext
          exact hval
        obtain ⟨σ', z, out, Ain, callGas, k680, C680, hΘ, rd680, hout⟩ :=
          RD.spotPokePeekPostCall rd679 hdepthLt
        let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
        rcases hΘ with ⟨g'', A', hΘ⟩
        have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
          intro hbad
          simp [evmE, initState] at hbad
          exact hdepthEq hbad
        have hΘE :
            (σ', g'', A', z, out) =
              Ethereum.EVM.Θ evmE.accountMap evmE.σ₀ Ain
                (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
                evmE.executionEnv.sender (AccountAddress.ofUInt256 (pokePipTargetWord σ I))
                (toExecute evmE.accountMap (AccountAddress.ofUInt256 (pokePipTargetWord σ I)))
                callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                ((pokePeekCalldataMem I).readWithPadding
                  pokePeekOutPtr.toNat pokePeekInSize.toNat)
                (evmE.executionEnv.depth + 1) evmE.executionEnv.header evmE.executionEnv.blobVersionedHashes evmE.executionEnv.blocks true := by
          simpa [evmE, initState, _hperm] using hΘ
        obtain ⟨σ'_solm, A'_solm, hcallSolm, hMap'⟩ :=
          typedCallViaEVM_callMade_sameInputs
            (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
            (tgt := EVM.address (pokePipAddress σ I))
            (targetWord := pokePipTargetWord σ I)
            (name := "peek") (args := [])
            (σ' := σ') (A' := A') (A_in := Ain) (z := z)
            (out := out) (g'' := g'') (callGas := callGas)
            (mem := pokePeekCalldataMem I)
            (inOff := pokePeekOutPtr) (inSize := pokePeekInSize) (callPerm := true)
            hdepthNe (by
              rw [pokePipAddress_eq_target]
              exact spotEvmAddress_accountAddress _)
            (pokePeekEncode_eq I) hΘE
            (by simp [evmE, evmS, initState])
            (by simp [evmE, evmS, initState])
            (by simp [evmE, evmS, initState])
        cases z
        · have rd680False : RD spotBytecode I (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨680⟩
              (⟨0⟩ :: pokePeekEndPtr :: pokePeekSelectorPlainWord ::
                pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I ::
                ⟨214⟩ :: spotSelWord I :: [])
              (pokePeekPostCallMem I out) (UInt256.ofNat 6) out σ' k680 C680 := by
            simpa using rd680
          have hbody :
              ExecTransitionBody config contract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (pokeLocals I) pokeTransition.body .reverted := by
            simpa [evmS] using
              (spotPokeSourceBodyPeekCallFailed
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmPip :=
                  { evmS with
                    accountMap := σ'_solm
                    substate := A'_solm })
                (out := out) hwv hsz36 hpipCodeSolm (by simpa [evmS] using hcallSolm))
          have hrev := RD.spotPokePeekCallFailed rd680False hout
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have rd680True : RD spotBytecode I (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨680⟩
              (⟨1⟩ :: pokePeekEndPtr :: pokePeekSelectorPlainWord ::
                pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I ::
                ⟨214⟩ :: spotSelWord I :: [])
              (pokePeekPostCallMem I out) (UInt256.ofNat 6) out σ' k680 C680 := by
            simpa using rd680
          obtain ⟨_, _, rd698⟩ := RD.spotPokePeekCallSucceeded rd680True
          by_cases hshort : out.size < 64
          · have hbody :
                ExecTransitionBody config contract
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (pokeLocals I) pokeTransition.body .reverted := by
              simpa [evmS] using
                (spotPokeSourceBodyPeekReturnDecodeReverts
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmPip :=
                    { evmS with
                      accountMap := σ'_solm
                      substate := A'_solm })
                  (out := out) hwv hsz36 hpipCodeSolm (by simpa [evmS] using hcallSolm)
                  (pokePeekDecode_none_short hshort))
            have hrev := RD.spotPokePeekReturnDecodeShortReverts rd698 hshort hout
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          ·
            have hlo : 64 ≤ out.size := Nat.le_of_not_gt hshort
            have hdecPeek := pokePeekDecode_ok hlo
            obtain ⟨_, _, rd733⟩ := RD.spotPokePeekReturnDecodeOk rd698 hlo hout
            by_cases hhasZero : pokePeekHasWord out = ⟨0⟩
            · obtain ⟨_, _, rd798⟩ := RD.spotPokeHasFalseToVatFileEntry rd733 hhasZero
              have hmem192 : (pokePeekPostCallMem I out).size = 192 :=
                pokePeekPostCallMem_size_long I out hlo hout
              have hread64 :
                  (pokePeekPostCallMem I out).readWithPadding 64 32 =
                    UInt256.toByteArray ⟨128⟩ :=
                pokePeekPostCallMem_read64_long I out hlo hout
              let evmPipS :=
                { evmS with
                  accountMap := σ'_solm
                  substate := A'_solm }
              by_cases hvatCodeSize :
                  Reasoning.Theory.extCodeSizeWord σ' (pokeVatTargetWord σ' I) = ⟨0⟩
              · have hvatCodeSizeSolm :
                    Reasoning.Theory.extCodeSizeWord σ'_solm
                        (pokeVatTargetWord σ'_solm I) = ⟨0⟩ :=
                  by simpa only [← hMap'] using hvatCodeSize
                have hvatNoCodeSolm :
                    (UInt256.ofNat
                      ((evmPipS.lookupAccount
                        (pokeVatAddress evmPipS.accountMap evmPipS.executionEnv)).option 0
                        (fun acc => acc.code.size))).toNat = 0 := by
                  exact pokeVatCode_zero_of_codeSize_zero (evm := evmPipS) (by
                    simpa [evmPipS, evmS, initState] using hvatCodeSizeSolm)
                have hbody :
                    ExecTransitionBody config contract
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (pokeLocals I) pokeTransition.body .reverted := by
                  simpa [evmS, evmPipS] using
                    (spotPokeSourceBodyPeekHasFalseVatNoCode
                      (σ := σ)
                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmPip := evmPipS) (out := out)
                      hwv hsz36 hpipCodeSolm (by simpa [evmS, evmPipS] using hcallSolm)
                      hdecPeek hhasZero hvatNoCodeSolm)
                have hrev := RD.spotPokeVatFileNoCode hmem192 hread64 hvatCodeSize rd798
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨gasWordFile, _, _, rd901⟩ :=
                  RD.spotPokeVatFileCallReady hmem192 hread64 hvatCodeSize rd798
                obtain ⟨σ'', zFile, fileOut, AinFile, callGasFile, k902, C902,
                    hΘFile, rd902, hfileOutSize⟩ :=
                  RD.spotPokeVatFilePostCall rd901 hdepthLt
                rcases hΘFile with ⟨gFile'', AFile', hΘFile⟩
                let evmPipE :=
                  { evmE with accountMap := σ', substate := A' }
                let evmPipSAligned := { evmPipS with substate := A' }
                have hΘFileE :
                    (σ'', gFile'', AFile', zFile, fileOut) =
                    Ethereum.EVM.Θ evmPipE.accountMap evmPipE.σ₀ AinFile
                        (AccountAddress.ofUInt256
                          (UInt256.ofNat evmPipE.executionEnv.codeOwner))
                        evmPipE.executionEnv.sender
                        (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I))
                        (toExecute evmPipE.accountMap
                        (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I)))
                        callGasFile (UInt256.ofNat evmPipE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                        (ByteArray.readWithPadding
                          (pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out))
                          pokeVatFileOutPtr.toNat pokeVatFileInSize.toNat)
                      (evmPipE.executionEnv.depth + 1) evmPipE.executionEnv.header
                      evmPipE.executionEnv.blobVersionedHashes evmPipE.executionEnv.blocks true := by
                  simpa [evmPipE, evmE, initState, _hperm] using hΘFile
                obtain ⟨σ''_solm, A''_solm, hfileCallSolmAligned, hMap''⟩ :=
                  typedCallViaEVM_callMade_sameInputs
                    (cfg := config) (evm_evm := evmPipE) (evm_solm := evmPipSAligned)
                    (tgt := EVM.address (pokeVatAddress σ'_solm I))
                    (targetWord := pokeVatTargetWord σ' I)
                    (name := "file")
                    (args :=
                      [.fixedBytes bytes32Width (pokeIlkBytes I),
                        .fixedBytes bytes32Width pokeSpotParamBytes,
                        .int (Int.ofNat (⟨0⟩ : UInt256).toNat)])
                    (σ' := σ'') (A' := AFile') (A_in := AinFile)
                    (z := zFile) (out := fileOut) (g'' := gFile'')
                    (callGas := callGasFile)
                    (mem := pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out))
                    (inOff := pokeVatFileOutPtr) (inSize := pokeVatFileInSize)
                    (callPerm := true)
                    (by simpa [evmPipE, evmE, initState] using hdepthNe)
                    (by
                      rw [← hMap', pokeVatAddress_eq_target]
                      exact spotEvmAddress_accountAddress _)
                    (pokeVatFileEncode_eq I ⟨0⟩ hsz36 hmem192)
                    hΘFileE
                    (by simpa [evmPipE, evmPipSAligned, evmPipS] using hMap')
                    (by simp [evmPipE, evmPipSAligned, evmPipS, evmE, evmS, initState])
                    (by simp [evmPipE, evmPipSAligned, evmPipS, evmE, evmS, initState])
                have hfileDepth : evmPipS.executionEnv.depth ≠ 1024 := by
                  simpa [evmPipS, evmS, initState] using hdepthNe
                have hfileCallSolm :
                    typedCallViaEVM config evmPipS
                      (EVM.address (pokeVatAddress evmPipS.accountMap evmPipS.executionEnv))
                      "file" 0
                      [.fixedBytes bytes32Width (pokeIlkBytes I),
                        .fixedBytes bytes32Width pokeSpotParamBytes,
                        .int (Int.ofNat (⟨0⟩ : UInt256).toNat)]
                      (zFile,
                        { evmPipS with
                          accountMap := σ''_solm
                          substate := A''_solm },
                        fileOut) true := by
                  simpa [evmPipSAligned, evmPipS] using
                    (typedCallViaEVM_zero_substate_irrel
                      (evm := evmPipS) (A0 := A') hfileCallSolmAligned hfileDepth)
                have hvatCodeSizeSolm :
                    Reasoning.Theory.extCodeSizeWord σ'_solm
                        (pokeVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
                  by simpa only [← hMap'] using hvatCodeSize
                have hvatCodeSolm :
                    0 <
                      (UInt256.ofNat
                        ((evmPipS.lookupAccount
                          (pokeVatAddress evmPipS.accountMap evmPipS.executionEnv)).option 0
                          (fun acc => acc.code.size))).toNat := by
                  exact pokeVatCode_pos_of_codeSize_ne_zero (evm := evmPipS) (by
                    simpa [evmPipS, evmS, initState] using hvatCodeSizeSolm)
                cases zFile
                · have rd902False : RD spotBytecode I (Sat256.ofUInt256 g)
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨902⟩
                      (⟨0⟩ :: pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord ::
                        pokeVatTargetWord σ' I :: ⟨0⟩ :: pokePeekHasWord out ::
                        pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: spotSelWord I :: [])
                      (pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out))
                      (UInt256.ofNat 8) fileOut σ'' k902 C902 := by
                    simpa using rd902
                  have hbody :
                      ExecTransitionBody config contract
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (pokeLocals I) pokeTransition.body .reverted := by
                    simpa [evmS, evmPipS] using
                      (spotPokeSourceBodyPeekHasFalseVatCallFailed
                        (σ := σ)
                        (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmPip := evmPipS)
                        (evmFile :=
                          { evmPipS with
                            accountMap := σ''_solm
                            substate := A''_solm })
                        (out := out) (fileOut := fileOut)
                        hwv hsz36 hpipCodeSolm
                        (by simpa [evmS, evmPipS] using hcallSolm)
                        hdecPeek hhasZero hvatCodeSolm hfileCallSolm)
                  have hrev := RD.spotPokeVatFileCallFailed rd902False hfileOutSize
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have rd902True : RD spotBytecode I (Sat256.ofUInt256 g)
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨902⟩
                      (⟨1⟩ :: pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord ::
                        pokeVatTargetWord σ' I :: ⟨0⟩ :: pokePeekHasWord out ::
                        pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: spotSelWord I :: [])
                      (pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out))
                      (UInt256.ofNat 8) fileOut σ'' k902 C902 := by
                    simpa using rd902
                  obtain ⟨_, _, rd920⟩ := RD.spotPokeVatFileCallSucceeded rd902True
                  have hbody :
                      ExecTransitionBody config contract
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (pokeLocals I) pokeTransition.body
                        (.returned
                          { contract := contract,
                            locals := (pokeSpotLocals I out ⟨0⟩).insert "_fileRet" .unit }
                          { evmPipS with
                            accountMap := σ''_solm
                            substate := A''_solm }
                          none) := by
                    simpa [evmS, evmPipS] using
                      (spotPokeSourceBodyPeekHasFalseVatCallSucceededReturns
                        (σ := σ)
                        (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmPip := evmPipS)
                        (evmFile :=
                          { evmPipS with
                            accountMap := σ''_solm
                            substate := A''_solm })
                        (out := out) (fileOut := fileOut)
                        hwv hsz36 hpipCodeSolm
                        (by simpa [evmS, evmPipS] using hcallSolm)
                        hdecPeek hhasZero hvatCodeSolm hfileCallSolm)
                  have hmem228 :
                      (pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out)).size = 228 :=
                    pokeVatFileCalldataMem_size I ⟨0⟩ hmem192
                  have hread64Final :
                      ByteArray.readWithPadding
                          (pokeVatFileCalldataMem I ⟨0⟩ (pokePeekPostCallMem I out)) 64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    pokeVatFileCalldataMem_read64 I ⟨0⟩ hmem192 hread64
                  have hret :=
                    RD.spotPokeVatFileLogReturns _hperm hmem228 hread64Final rd920
                  have henc : returnEquiv ByteArray.empty none pokeTransition.returnType := by
                    simpa [pokeTransition] using
                      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                        (dvs := []) rfl (by native_decide) (by native_decide))
                  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
                    (by simpa using hMap'') henc
            ·
              have hhasNe : pokePeekHasWord out ≠ ⟨0⟩ := hhasZero
              obtain ⟨_, _, rd2051Val⟩ := RD.spotPokeHasTrueToValScaledMul rd733 hhasNe
              have hmem192 : (pokePeekPostCallMem I out).size = 192 :=
                pokePeekPostCallMem_size_long I out hlo hout
              have hread64 :
                  (pokePeekPostCallMem I out).readWithPadding 64 32 =
                    UInt256.toByteArray ⟨128⟩ :=
                pokePeekPostCallMem_read64_long I out hlo hout
              let evmPipS :=
                { evmS with
                  accountMap := σ'_solm
                  substate := A'_solm }
              let val := pokePeekValWord out
              let valScaled := val * pokeBillion
              have hlo32 : 32 ≤ out.size := by omega
              have hvalScaled : valScaled = pokePeekValWord out * pokeBillion := by
                simp [val, valScaled]
              have hsourceArithmeticReverts
                  (harith :
                    ExecBlock config
                      { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ }
                      evmPipS pokeTrueBranchStmts .reverted) :
                  ExecTransitionBody config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (pokeLocals I) pokeTransition.body .reverted := by
                have htail := spotPokeTrueTailArithmeticReverts hhasNe harith
                simpa [evmS, evmPipS] using
                  (spotPokeSourceBodyPeekHasTrueTailReverts
                    (σ := σ)
                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmPip := evmPipS) (out := out)
                    hwv hsz36 hpipCodeSolm
                    (by simpa [evmS, evmPipS] using hcallSolm)
                    hdecPeek htail)
              by_cases hfitVal : val.toNat * pokeBillion.toNat < UInt256.size
              · obtain ⟨_, _, rd766⟩ :=
                  RD.spotCheckedMulReturns
                    (R := ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ :: pokePeekHasWord out ::
                      pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                      spotSelWord I :: [])
                    (ret := (⟨766⟩ : UInt256))
                    (by simp only [List.length_cons, List.length_nil]; omega)
                    (by native_decide)
                    (by simpa [val] using hfitVal) rd2051Val
                obtain ⟨_, _, rd2093Par⟩ := RD.spotPokeValScaledToRdivPar rd766
                have hparEq :
                    pokeParWord evmPipS.accountMap evmPipS.executionEnv =
                      pokeParWord σ' I := by
                  simp [evmPipS, evmS, initState, ← hMap']
                by_cases hfitPar : valScaled.toNat * pokeRay.toNat < UInt256.size
                · by_cases hparZero : pokeParWord σ' I = ⟨0⟩
                  · have hinvalidOr :=
                      RD.spotRdivDivZeroInvalid
                        (R := ⟨798⟩ :: ⟨0⟩ :: pokePeekHasWord out ::
                          pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                          spotSelWord I :: [])
                        (ret := (⟨774⟩ : UInt256))
                        (by simp only [List.length_cons, List.length_nil]; omega)
                        hfitPar hparZero rd2093Par
                    have hparZeroS :
                        pokeParWord evmPipS.accountMap evmPipS.executionEnv = ⟨0⟩ := by
                      rw [hparEq, hparZero]
                    have harith :=
                      execPokeTrueRdivParDivZeroReverts evmPipS I out hlo32
                        hvalScaled (by simpa [val] using hfitVal) hfitPar hparZeroS
                    have hbody := hsourceArithmeticReverts
                      (by simpa [pokeTrueBranchStmts] using harith)
                    rcases hinvalidOr with hoog | hinvalid
                    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                        rw [← hcode] at hoog
                        simpa [initState, Sat256.ofUInt256] using hoog))
                    · have hxi :
                          Ξ σ σ₀ g A I = .error .InvalidInstruction :=
                        Xi_error_of_X (g := g) (by
                          rw [← hcode] at hinvalid
                          simpa [initState, Sat256.ofUInt256] using hinvalid)
                      exact reEquiv_execution hdispatch hdecode hbody
                        (execResultsEquiv.invalidHalt hxi rfl)
                  · let spot1 :=
                      UInt256.div (valScaled * pokeRay) (pokeParWord σ' I)
                    obtain ⟨_, _, rd774⟩ :=
                      RD.spotRdivReturns
                        (R := ⟨798⟩ :: ⟨0⟩ :: pokePeekHasWord out ::
                          pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                          spotSelWord I :: [])
                        (ret := (⟨774⟩ : UInt256))
                        (by simp only [List.length_cons, List.length_nil]; omega)
                        (by native_decide) hfitPar hparZero rd2093Par
                    obtain ⟨_, _, rd2093Mat⟩ :=
                      RD.spotPokeAfterRdivParToRdivMat hsz36 hmem192 hread64 rd774
                    let memHash := twoWordHashMem (pokeIlkWord I) ⟨1⟩
                      (pokePeekPostCallMem I out)
                    have hmemHash192 : memHash.size = 192 := by
                      dsimp [memHash]
                      rw [poke_twoWordHashMem_size_of_ge64]
                      · exact hmem192
                      · rw [hmem192]; omega
                    have hread64Hash :
                        memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
                      dsimp [memHash]
                      exact poke_twoWordHashMem_read64_of_ge96
                        (pokeIlkWord I) (⟨1⟩ : UInt256)
                        (by rw [hmem192]; omega) hread64
                    have hparNeS :
                        pokeParWord evmPipS.accountMap evmPipS.executionEnv ≠ ⟨0⟩ := by
                      intro hzero
                      exact hparZero (by simpa [hparEq] using hzero)
                    have hspot1S :
                        spot1 = UInt256.div (valScaled * pokeRay)
                          (pokeParWord evmPipS.accountMap evmPipS.executionEnv) := by
                      dsimp [spot1]
                      rw [hparEq]
                    have hmatEq :
                        pokeMatWord evmPipS.accountMap I = pokeMatWord σ' I := by
                      simp [evmPipS, ← hMap']
                    by_cases hfitMat : spot1.toNat * pokeRay.toNat < UInt256.size
                    · by_cases hmatZero : pokeMatWord σ' I = ⟨0⟩
                      · have hinvalidOr :=
                          RD.spotRdivDivZeroInvalid
                            (R := ⟨0⟩ :: pokePeekHasWord out :: pokePeekValWord out ::
                              pokeIlkWord I :: ⟨214⟩ :: spotSelWord I :: [])
                            (ret := (⟨798⟩ : UInt256))
                            (by simp only [List.length_cons, List.length_nil]; omega)
                            hfitMat hmatZero rd2093Mat
                        have hmatZeroS : pokeMatWord evmPipS.accountMap I = ⟨0⟩ := by
                          rw [hmatEq, hmatZero]
                        have harith :=
                          execPokeTrueRdivMatDivZeroReverts evmPipS I out
                            hsz36 hlo32 (by simp [evmPipS, evmS, initState])
                            hvalScaled (by simpa [val] using hfitVal) hfitPar
                            hparNeS hspot1S hfitMat hmatZeroS
                        have hbody := hsourceArithmeticReverts
                          (by simpa [pokeTrueBranchStmts] using harith)
                        rcases hinvalidOr with hoog | hinvalid
                        · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                            rw [← hcode] at hoog
                            simpa [initState, Sat256.ofUInt256] using hoog))
                        · have hxi :
                              Ξ σ σ₀ g A I = .error .InvalidInstruction :=
                            Xi_error_of_X (g := g) (by
                              rw [← hcode] at hinvalid
                              simpa [initState, Sat256.ofUInt256] using hinvalid)
                          exact reEquiv_execution hdispatch hdecode hbody
                            (execResultsEquiv.invalidHalt hxi rfl)
                      · let spot2 := UInt256.div (spot1 * pokeRay) (pokeMatWord σ' I)
                        obtain ⟨_, _, rd798⟩ :=
                          RD.spotRdivReturns
                            (R := ⟨0⟩ :: pokePeekHasWord out ::
                              pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                              spotSelWord I :: [])
                            (ret := (⟨798⟩ : UInt256))
                            (by simp only [List.length_cons, List.length_nil]; omega)
                            (by native_decide) hfitMat hmatZero rd2093Mat
                        have hmatNeS : pokeMatWord evmPipS.accountMap I ≠ ⟨0⟩ := by
                          intro hzero
                          exact hmatZero (by simpa [hmatEq] using hzero)
                        have hspot2S :
                            spot2 = UInt256.div (spot1 * pokeRay)
                              (pokeMatWord evmPipS.accountMap I) := by
                          dsimp [spot2]
                          rw [hmatEq]
                        have harith :=
                          execPokeTrueArithmeticReturns evmPipS I out
                            hsz36 hlo32 (by simp [evmPipS, evmS, initState])
                            hvalScaled (by simpa [val] using hfitVal) hfitPar
                            hparNeS hspot1S hfitMat hmatNeS hspot2S
                        by_cases hvatCodeSize :
                            Reasoning.Theory.extCodeSizeWord σ'
                              (pokeVatTargetWord σ' I) = ⟨0⟩
                        · have hvatCodeSizeSolm :
                              Reasoning.Theory.extCodeSizeWord σ'_solm
                                  (pokeVatTargetWord σ'_solm I) = ⟨0⟩ :=
                            by simpa only [← hMap'] using hvatCodeSize
                          have hvatNoCodeSolm :
                              (UInt256.ofNat
                                ((evmPipS.lookupAccount
                                  (pokeVatAddress evmPipS.accountMap
                                    evmPipS.executionEnv)).option 0
                                  (fun acc => acc.code.size))).toNat = 0 := by
                            exact pokeVatCode_zero_of_codeSize_zero (evm := evmPipS) (by
                              simpa [evmPipS, evmS, initState] using hvatCodeSizeSolm)
                          have htail :=
                            spotPokeTrueTailVatNoCode (evm := evmPipS) (I := I)
                              (out := out) (valScaled := valScaled) (spot1 := spot1)
                              (spot2 := spot2) hhasNe
                              (by simpa [pokeTrueBranchStmts] using harith)
                              hvatNoCodeSolm
                          have hbody :
                              ExecTransitionBody config contract
                                (initState σ σ₀
                                  (Sat256.ofUInt256 g) A I)
                                (pokeLocals I) pokeTransition.body .reverted := by
                            simpa [evmS, evmPipS] using
                              (spotPokeSourceBodyPeekHasTrueTailReverts
                                (σ := σ)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmPip := evmPipS) (out := out)
                                hwv hsz36 hpipCodeSolm
                                (by simpa [evmS, evmPipS] using hcallSolm)
                                hdecPeek htail)
                          have hrev :=
                            RD.spotPokeVatFileNoCode hmemHash192 hread64Hash
                              hvatCodeSize rd798
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · obtain ⟨gasWordFile, _, _, rd901⟩ :=
                            RD.spotPokeVatFileCallReady hmemHash192 hread64Hash
                              hvatCodeSize rd798
                          obtain ⟨σ'', zFile, fileOut, AinFile, callGasFile,
                              k902, C902, hΘFile, rd902, hfileOutSize⟩ :=
                            RD.spotPokeVatFilePostCall rd901 hdepthLt
                          rcases hΘFile with ⟨gFile'', AFile', hΘFile⟩
                          let evmPipE :=
                            { evmE with accountMap := σ', substate := A' }
                          let evmPipSAligned := { evmPipS with substate := A' }
                          have hΘFileE :
                              (σ'', gFile'', AFile', zFile, fileOut) =
                                Ethereum.EVM.Θ evmPipE.accountMap evmPipE.σ₀ AinFile
                                  (AccountAddress.ofUInt256
                                    (UInt256.ofNat evmPipE.executionEnv.codeOwner))
                                  evmPipE.executionEnv.sender
                                  (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I))
                                  (toExecute evmPipE.accountMap
                                    (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I)))
                                  callGasFile
                                  (UInt256.ofNat evmPipE.executionEnv.gasPrice)
                                  ⟨0⟩ ⟨0⟩
                                  (ByteArray.readWithPadding
                                    (pokeVatFileCalldataMem I spot2 memHash)
                                    pokeVatFileOutPtr.toNat pokeVatFileInSize.toNat)
                                  (evmPipE.executionEnv.depth + 1)
                                  evmPipE.executionEnv.header
                                  evmPipE.executionEnv.blobVersionedHashes
                                  evmPipE.executionEnv.blocks true := by
                            simpa [evmPipE, evmE, initState, _hperm] using hΘFile
                          obtain ⟨σ''_solm, A''_solm, hfileCallSolmAligned,
                              hMap''⟩ :=
                            typedCallViaEVM_callMade_sameInputs
                              (cfg := config) (evm_evm := evmPipE)
                              (evm_solm := evmPipSAligned)
                              (tgt := EVM.address (pokeVatAddress σ'_solm I))
                              (targetWord := pokeVatTargetWord σ' I)
                              (name := "file")
                              (args :=
                                [.fixedBytes bytes32Width (pokeIlkBytes I),
                                  .fixedBytes bytes32Width pokeSpotParamBytes,
                                  .int (Int.ofNat spot2.toNat)])
                              (σ' := σ'') (A' := AFile')
                              (A_in := AinFile) (z := zFile) (out := fileOut)
                              (g'' := gFile'') (callGas := callGasFile)
                              (mem := pokeVatFileCalldataMem I spot2 memHash)
                              (inOff := pokeVatFileOutPtr) (inSize := pokeVatFileInSize)
                              (callPerm := true)
                              (by simpa [evmPipE, evmE, initState] using hdepthNe)
                              (by
                                rw [← hMap', pokeVatAddress_eq_target]
                                exact spotEvmAddress_accountAddress _)
                              (pokeVatFileEncode_eq I spot2 hsz36 hmemHash192)
                              hΘFileE
                              (by simpa [evmPipE, evmPipSAligned, evmPipS] using hMap')
                              (by simp [evmPipE, evmPipSAligned, evmPipS,
                                evmE, evmS, initState])
                              (by simp [evmPipE, evmPipSAligned, evmPipS,
                                evmE, evmS, initState])
                          have hfileDepth : evmPipS.executionEnv.depth ≠ 1024 := by
                            simpa [evmPipS, evmS, initState] using hdepthNe
                          have hfileCallSolm :
                              typedCallViaEVM config evmPipS
                                (EVM.address
                                  (pokeVatAddress evmPipS.accountMap
                                    evmPipS.executionEnv))
                                "file" 0
                                [.fixedBytes bytes32Width (pokeIlkBytes I),
                                  .fixedBytes bytes32Width pokeSpotParamBytes,
                                  .int (Int.ofNat spot2.toNat)]
                                (zFile,
                                  { evmPipS with
                                    accountMap := σ''_solm
                                    substate := A''_solm },
                                  fileOut) true := by
                            simpa [evmPipSAligned, evmPipS] using
                              (typedCallViaEVM_zero_substate_irrel
                                (evm := evmPipS) (A0 := A')
                                hfileCallSolmAligned hfileDepth)
                          have hvatCodeSizeSolm :
                              Reasoning.Theory.extCodeSizeWord σ'_solm
                                  (pokeVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
                            by simpa only [← hMap'] using hvatCodeSize
                          have hvatCodeSolm :
                              0 <
                                (UInt256.ofNat
                                  ((evmPipS.lookupAccount
                                    (pokeVatAddress evmPipS.accountMap
                                      evmPipS.executionEnv)).option 0
                                    (fun acc => acc.code.size))).toNat := by
                            exact pokeVatCode_pos_of_codeSize_ne_zero (evm := evmPipS) (by
                              simpa [evmPipS, evmS, initState] using hvatCodeSizeSolm)
                          cases zFile
                          · have rd902False : RD spotBytecode I (Sat256.ofUInt256 g)
                                (initState σ σ₀
                                  (Sat256.ofUInt256 g) A I) ⟨902⟩
                                (⟨0⟩ :: pokeVatFileEndPtr ::
                                  pokeVatFileSelectorPlainWord ::
                                  pokeVatTargetWord σ' I :: spot2 ::
                                  pokePeekHasWord out :: pokePeekValWord out ::
                                  pokeIlkWord I :: ⟨214⟩ :: spotSelWord I :: [])
                                (pokeVatFileCalldataMem I spot2 memHash)
                                (UInt256.ofNat 8) fileOut σ'' k902 C902 := by
                              simpa using rd902
                            have htail :=
                              spotPokeTrueTailVatCallFailed
                                (evm := evmPipS)
                                (evmFile :=
                                  { evmPipS with
                                    accountMap := σ''_solm
                                    substate := A''_solm })
                                (I := I) (out := out) (fileOut := fileOut)
                                (valScaled := valScaled) (spot1 := spot1)
                                (spot2 := spot2) hhasNe
                                (by simpa [pokeTrueBranchStmts] using harith)
                                hvatCodeSolm hfileCallSolm
                            have hbody :
                                ExecTransitionBody config contract
                                  (initState σ σ₀
                                    (Sat256.ofUInt256 g) A I)
                                  (pokeLocals I) pokeTransition.body .reverted := by
                              simpa [evmS, evmPipS] using
                                (spotPokeSourceBodyPeekHasTrueTailReverts
                                  (σ := σ) (σ₀ := σ₀) (A := A)
                                  (I := I) (g := g) (evmPip := evmPipS)
                                  (out := out) hwv hsz36 hpipCodeSolm
                                  (by simpa [evmS, evmPipS] using hcallSolm)
                                  hdecPeek htail)
                            have hrev := RD.spotPokeVatFileCallFailed
                              rd902False hfileOutSize
                            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have rd902True : RD spotBytecode I (Sat256.ofUInt256 g)
                                (initState σ σ₀
                                  (Sat256.ofUInt256 g) A I) ⟨902⟩
                                (⟨1⟩ :: pokeVatFileEndPtr ::
                                  pokeVatFileSelectorPlainWord ::
                                  pokeVatTargetWord σ' I :: spot2 ::
                                  pokePeekHasWord out :: pokePeekValWord out ::
                                  pokeIlkWord I :: ⟨214⟩ :: spotSelWord I :: [])
                                (pokeVatFileCalldataMem I spot2 memHash)
                                (UInt256.ofNat 8) fileOut σ'' k902 C902 := by
                              simpa using rd902
                            obtain ⟨_, _, rd920⟩ :=
                              RD.spotPokeVatFileCallSucceeded rd902True
                            have htail :=
                              spotPokeTrueTailVatCallSucceededReturns
                                (evm := evmPipS)
                                (evmFile :=
                                  { evmPipS with
                                    accountMap := σ''_solm
                                    substate := A''_solm })
                                (I := I) (out := out) (fileOut := fileOut)
                                (valScaled := valScaled) (spot1 := spot1)
                                (spot2 := spot2) hhasNe
                                (by simpa [pokeTrueBranchStmts] using harith)
                                hvatCodeSolm hfileCallSolm
                            have hbody :
                                ExecTransitionBody config contract
                                  (initState σ σ₀
                                    (Sat256.ofUInt256 g) A I)
                                  (pokeLocals I) pokeTransition.body
                                  (.returned
                                    { contract := contract,
                                      locals :=
                                        (pokeSpotAssignedLocals I out valScaled spot1 spot2).insert
                                          "_fileRet" .unit }
                                    { evmPipS with
                                      accountMap := σ''_solm
                                      substate := A''_solm }
                                    none) := by
                              simpa [evmS, evmPipS] using
                                (spotPokeSourceBodyPeekHasTrueTailReturns
                                  (σ := σ) (σ₀ := σ₀) (A := A)
                                  (I := I) (g := g) (evmPip := evmPipS)
                                  (evmFile :=
                                    { evmPipS with
                                      accountMap := σ''_solm
                                      substate := A''_solm })
                                  (out := out)
                                  (fileLocals :=
                                    (pokeSpotAssignedLocals I out valScaled spot1 spot2).insert
                                      "_fileRet" .unit)
                                  hwv hsz36 hpipCodeSolm
                                  (by simpa [evmS, evmPipS] using hcallSolm)
                                  hdecPeek htail)
                            have hmem228 :
                                (pokeVatFileCalldataMem I spot2 memHash).size = 228 :=
                              pokeVatFileCalldataMem_size I spot2 hmemHash192
                            have hread64Final :
                                ByteArray.readWithPadding
                                    (pokeVatFileCalldataMem I spot2 memHash) 64 32 =
                                  UInt256.toByteArray ⟨128⟩ :=
                              pokeVatFileCalldataMem_read64 I spot2
                                hmemHash192 hread64Hash
                            have hret :=
                              RD.spotPokeVatFileLogReturns _hperm hmem228
                                hread64Final rd920
                            have henc :
                                returnEquiv ByteArray.empty none
                                  pokeTransition.returnType := by
                              simpa [pokeTransition] using
                                (returnEquiv.fallthrough
                                  (o := ByteArray.empty) (r := none) (t := [])
                                  (dvs := []) rfl (by native_decide)
                                  (by native_decide))
                            exact hret.reEquivExecutionGen
                              hcode hdispatch hdecode hbody
                              (by simpa using hMap'')
                              henc
                    · have hoverMat :
                        UInt256.size ≤ spot1.toNat * pokeRay.toNat :=
                        Nat.le_of_not_gt hfitMat
                      have hrev :=
                        RD.spotRdivMulOverflowReverts
                          (R := ⟨0⟩ :: pokePeekHasWord out ::
                            pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                            spotSelWord I :: [])
                          (ret := (⟨798⟩ : UInt256))
                          (by simp only [List.length_cons, List.length_nil]; omega)
                          hoverMat rd2093Mat
                      have harith :=
                        execPokeTrueRdivMatMulOverflowReverts evmPipS I out
                          hsz36 hlo32 (by simp [evmPipS, evmS, initState])
                          hvalScaled (by simpa [val] using hfitVal) hfitPar
                          hparNeS hspot1S hoverMat
                      have hbody := hsourceArithmeticReverts
                        (by simpa [pokeTrueBranchStmts] using harith)
                      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hoverPar : UInt256.size ≤ valScaled.toNat * pokeRay.toNat :=
                    Nat.le_of_not_gt hfitPar
                  have hrev :=
                    RD.spotRdivMulOverflowReverts
                      (R := ⟨798⟩ :: ⟨0⟩ :: pokePeekHasWord out ::
                        pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                        spotSelWord I :: [])
                      (ret := (⟨774⟩ : UInt256))
                      (by simp only [List.length_cons, List.length_nil]; omega)
                      hoverPar rd2093Par
                  have harith :=
                    execPokeTrueRdivParMulOverflowReverts evmPipS I out hlo32
                      hvalScaled (by simpa [val] using hfitVal) hoverPar
                  have hbody := hsourceArithmeticReverts
                    (by simpa [pokeTrueBranchStmts] using harith)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hoverVal : UInt256.size ≤ val.toNat * pokeBillion.toNat :=
                  Nat.le_of_not_gt hfitVal
                have hrev :=
                  RD.spotCheckedMulOverflowReverts
                    (R := ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ :: pokePeekHasWord out ::
                      pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ ::
                      spotSelWord I :: [])
                    (ret := (⟨766⟩ : UInt256))
                    (by simp only [List.length_cons, List.length_nil]; omega)
                    (by simpa [val] using hoverVal) rd2051Val
                have harith :=
                  execPokeTrueValScaledOverflowReverts evmPipS I out hlo32
                    (by simpa [val] using hoverVal)
                have hbody := hsourceArithmeticReverts
                  (by simpa [pokeTrueBranchStmts] using harith)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact spotPokeBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach
end Benchmarks.Dss.Spot
