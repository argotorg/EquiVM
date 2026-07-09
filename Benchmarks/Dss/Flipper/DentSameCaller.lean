import Benchmarks.Dss.Flipper.DentTail
import Benchmarks.Dss.Flipper.ExternalCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Same-caller `dent` tail correspondence -/

theorem flipperDentBodyFrom4733SameCaller
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hguySolm : bidGuyWord (dentId I) σ_solm I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ_solm I).toNat * flipperONEWord.toNat <
      UInt256.size)
    (hfitBeg : (dentBegWord σ_solm I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ_solm I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcallerEvm : solcSourceWord I = bidGuyWord (dentId I) σ_evm I)
    (hcallerSolm : solcSourceWord I = bidGuyWord (dentId I) σ_solm I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4733⟩
      [dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd4927⟩ :=
    flipperDentX_skipRefund hmemSize hcallerEvm h
  let memFlux := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hmemFluxSize : memFlux.size = 96 := by
    dsimp [memFlux]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hmemFluxRead64 : memFlux.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memFlux]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  by_cases hfluxZero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (flipperVatTargetWord σ_evm I) = ⟨0⟩
  · have hfluxZeroSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) = ⟨0⟩ :=
      flipperVatCodeSize_zero_accountMapEquiv hAccounts hfluxZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hfluxZeroSolm
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (dentLocals I) dentTransition.body .reverted := by
      simpa using
        (flipperDentSourceBodyFluxNoCodeSameCaller (cA := cA) (gh := gh)
          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
          hfitBeg hdec hcallerSolm hvatNoCode)
    exact (flipperDentX_fluxNoCode hmemFluxSize hmemFluxRead64 hfluxZero rd4927)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hfluxNeSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
      flipperVatCodeSize_ne_zero_accountMapEquiv hAccounts hfluxZero
    have hvatCodeSolm :=
      flipperVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hfluxNeSolm
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmFluxSolm :=
        { evm0Solm with
          substate :=
            (evm0Solm.addAccessedAccount
              (EVM.address
                (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))).substate }
      have hfluxEncode :
          config.externalABI.encode? "flux" (dentFluxArgValsOf evm0Solm I) =
            some ((dentVatFluxCallMem memFlux σ_solm I).readWithPadding 128 132) := by
        simpa [evm0Solm, dentFluxArgValsOf, initState, flipperSlotWord,
          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidUsrWord, bidLotWord, bidSlotOfWord, bidBaseOfWord, flipperAddressReturnWord]
          using dentVatFluxCallMem_encode (mem := memFlux) (σ := σ_solm) (I := I)
            hmemFluxSize
      have hcallFluxSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "flux" 0 (dentFluxArgValsOf evm0Solm I)
            (false, evmFluxSolm, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Solm)
          (tgt := EVM.address
            (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
          (name := "flux") (args := dentFluxArgValsOf evm0Solm I)
          (calldata := (dentVatFluxCallMem memFlux σ_solm I).readWithPadding 128 132)
          (callPerm := true) hfluxEncode (by simpa [evm0Solm, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
            .reverted := by
        simpa [evm0Solm] using
          (flipperDentSourceBodyFluxCallFailureSameCaller
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmFlux := evmFluxSolm)
            (outFlux := ByteArray.empty)
            hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
            hfitBeg hdec hcallerSolm hvatCodeSolm hcallFluxSolm)
      exact (flipperDentX_fluxCallDepthLimit hmemFluxSize hmemFluxRead64 hfluxZero
          hdepthEq rd4927)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdepthLt : I.depth.val < 1024 := by
        by_contra hnot
        have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
        have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
        have hval : I.depth.val = 1024 := by omega
        exact hdepthEq (Fin.ext hval)
      obtain ⟨cA_flux, σ_flux, zFlux, outFlux, A_flux, k5053, C5053, rd5053,
          hcallFluxEvmRaw, houtFlux⟩ :=
        flipperDentX_fluxPostCall (Acur := A) hmemFluxSize hmemFluxRead64 hfluxZero
          hperm hdepthLt rd4927
      let evm0Evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmFluxEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_flux
          substate := A_flux
          createdAccounts := cA_flux }
      have hcallFluxEvm :
          typedCallViaEVM config evm0Evm
            (EVM.address (flipperVatAddress σ_evm I)) "flux" 0
            (dentFluxArgValsOf evm0Evm I) (zFlux, evmFluxEvm, outFlux) true := by
        simpa [evm0Evm, evmFluxEvm] using hcallFluxEvmRaw
      obtain ⟨σ_flux_solm, A_flux_solm, hcallFluxSolmRaw, hFluxStateEquiv⟩ :=
        flipper_typedCallViaEVM_accountMapEquiv_noSubstate
          (evm_solm := evm0Solm) hcallFluxEvm
          (by simpa [evm0Evm, evm0Solm] using hAccounts)
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
      let evmFluxSolm : EVM.State :=
        { evm0Solm with
          accountMap := σ_flux_solm
          substate := A_flux_solm
          createdAccounts := cA_flux }
      have hfluxTargetEq :
          EVM.address (flipperVatAddress σ_evm I) =
            EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv) := by
        rw [flipperVatAddress_accountMapEquiv hAccounts]
        simp [evm0Solm, initState]
      have hfluxArgsEq : dentFluxArgValsOf evm0Evm I = dentFluxArgValsOf evm0Solm I := by
        have hloadIlk :
            Solm.EVM.storageLoad evm0Evm I.codeOwner ⟨3⟩ =
              Solm.EVM.storageLoad evm0Solm I.codeOwner ⟨3⟩ := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner ⟨3⟩
        have hloadUsr :
            Solm.EVM.storageLoad evm0Evm I.codeOwner (bidSlotOfWord (dentId I) ⟨3⟩) =
              Solm.EVM.storageLoad evm0Solm I.codeOwner (bidSlotOfWord (dentId I) ⟨3⟩) := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner
              (bidSlotOfWord (dentId I) ⟨3⟩)
        have hloadLot :
            Solm.EVM.storageLoad evm0Evm I.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) =
              Solm.EVM.storageLoad evm0Solm I.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner
              (bidSlotOfWord (dentId I) ⟨1⟩)
        simp [dentFluxArgValsOf, evm0Evm, evm0Solm, initState]
        constructor
        · simpa [evm0Evm, evm0Solm, initState] using
            congrArg EVM.Word.toBytesBE hloadIlk
        · constructor
          · simpa [evm0Evm, evm0Solm, initState] using
              congrArg (fun w => AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)
                hloadUsr
          · simpa [evm0Evm, evm0Solm, initState] using
              congrArg (fun w => (UInt256.sub w (dentLot I)).toNat) hloadLot
      have hcallFluxSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "flux" 0 (dentFluxArgValsOf evm0Solm I)
            (zFlux, evmFluxSolm, outFlux) true := by
        have hcallFluxSolmRaw' :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress σ_evm I)) "flux" 0
              (dentFluxArgValsOf evm0Evm I) (zFlux, evmFluxSolm, outFlux) true := by
          simpa [evmFluxSolm, evmFluxEvm] using hcallFluxSolmRaw
        rw [hfluxTargetEq, hfluxArgsEq] at hcallFluxSolmRaw'
        exact hcallFluxSolmRaw'
      cases zFlux
      · have hcallFluxSolmFalse :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "flux" 0 (dentFluxArgValsOf evm0Solm I)
              (false, evmFluxSolm, outFlux) true := by
          simpa using hcallFluxSolm
        have hbody :
            ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
              .reverted := by
          simpa [evm0Solm] using
            (flipperDentSourceBodyFluxCallFailureSameCaller
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmFlux := evmFluxSolm) (outFlux := outFlux)
              hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
              hfitBeg hdec hcallerSolm hvatCodeSolm hcallFluxSolmFalse)
        exact (flipperDentX_fluxCallFailure (by simpa using rd5053) houtFlux)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd5053True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
            (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
              flipperVatTargetWord σ_evm I :: dentBid I :: dentLot I :: dentId I ::
              ⟨323⟩ :: sel :: [])
            (dentVatFluxCallMem memFlux σ_evm I) (UInt256.ofNat 9) outFlux
            (cA_flux, σ_flux) k5053 C5053 := by
          simpa using rd5053
        obtain ⟨_, _, rd5073⟩ := flipperDentX_fluxCallSuccessToStoreStart rd5053True
        have hfluxMemGe : 64 ≤ (dentVatFluxCallMem memFlux σ_evm I).size := by
          rw [dentVatFluxCallMem_size hmemFluxSize]
          norm_num
        obtain ⟨_, _, rd6272⟩ := flipperDentX_storeLotToAdd48 hperm hfluxMemGe rd5073
        have hcallFluxSolmTrue :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "flux" 0 (dentFluxArgValsOf evm0Solm I)
              (true, evmFluxSolm, outFlux) true := by
          simpa using hcallFluxSolm
        let evmLotEvm := Solm.EVM.storageStore evmFluxEvm evmFluxEvm.executionEnv.codeOwner
          (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
        let evmLotSolm := Solm.EVM.storageStore evmFluxSolm evmFluxSolm.executionEnv.codeOwner
          (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
        have hFluxStateEquiv' : EVMStateEquiv evmFluxEvm evmFluxSolm := by
          simpa [evmFluxEvm, evmFluxSolm] using hFluxStateEquiv
        have hLotStateEquiv : EVMStateEquiv evmLotEvm evmLotSolm := by
          simpa [evmLotEvm, evmLotSolm] using
            EVMStateEquiv.storageStore_codeOwner hFluxStateEquiv'
              (bidSlotOfWord (dentId I) ⟨1⟩) (by rfl : dentLot I = dentLot I)
        have hmapLotEvm : evmLotEvm.accountMap = dentAfterLotMap σ_flux I := by
          simpa [evmLotEvm, evmFluxEvm, evm0Evm, dentAfterLotMap, storageStore_accountMap,
            initState]
        have httlEq :
            tendTtlWord evmLotEvm.accountMap I = tendTtlWord evmLotSolm.accountMap I := by
          unfold tendTtlWord flipperUint48Offset0Word flipperSlotWord solcSlotWord
          rw [accountMapEquiv_storage_findD hLotStateEquiv.accountMap I.codeOwner ⟨5⟩ ⟨0⟩]
        have httlEvmMap :
            tendTtlWord evmLotEvm.accountMap I = tendTtlWord (dentAfterLotMap σ_flux I) I := by
          simpa [hmapLotEvm]
        by_cases hfitTicEvm :
            (tendNow48 I).toNat +
                (tendTtlWord (dentAfterLotMap σ_flux I) I).toNat <
              2 ^ 48
        · obtain ⟨_, _, rd3859⟩ := flipperDentX_add48Success hfitTicEvm rd6272
          have hticMemGe :
              64 ≤
                (twoWordHashMem (dentId I) ⟨1⟩
                  (dentVatFluxCallMem memFlux σ_evm I)).size := by
            rw [tendTwoWordHashMem_size_of_size_ge]
            · exact hfluxMemGe
            · exact hfluxMemGe
          have hret := flipperDentX_storeTicReturn hperm hticMemGe rd3859
          have hfitTicSolm :
              (tendNow48 I).toNat + (tendTtlWord evmLotSolm.accountMap I).toNat <
                2 ^ 48 := by
            have httlSolmMap :
                tendTtlWord evmLotSolm.accountMap I =
                  tendTtlWord (dentAfterLotMap σ_flux I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSolmMap] using hfitTicEvm
          let evmTicEvm := Solm.EVM.storageStore evmLotEvm evmLotEvm.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I))
            (setUint48Offset20Word
              (Solm.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)))
              (tendTicNewWord evmLotEvm.accountMap I))
          let evmTicSolm := Solm.EVM.storageStore evmLotSolm evmLotSolm.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I))
            (setUint48Offset20Word
              (Solm.EVM.storageLoad evmLotSolm evmLotSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)))
              (tendTicNewWord evmLotSolm.accountMap I))
          have hbody :
              ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
                (.returned
                  { contract := contract,
                    locals := dentLocalsAfterFluxWithTicFrom σ_solm evmLotSolm.accountMap I }
                  evmTicSolm none) := by
            simpa [evm0Solm, evmLotSolm, evmTicSolm] using
              (flipperDentSourceBodySuccessSameCaller
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmFlux := evmFluxSolm)
                (outFlux := outFlux)
                hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                hfitBeg hdec hcallerSolm hvatCodeSolm hcallFluxSolmTrue
                (by simp [evmFluxSolm, evm0Solm, initState])
                (by simp [evmFluxSolm, evm0Solm, initState]) hfitTicSolm)
          have hpackedLoadEq :
              Solm.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)) =
                Solm.EVM.storageLoad evmLotSolm evmLotSolm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)) :=
            hLotStateEquiv.storageLoad_codeOwner (bidPackedSlotOfWord (dentId I))
          have hticNewEq :
              tendTicNewWord evmLotEvm.accountMap I =
                tendTicNewWord evmLotSolm.accountMap I := by
            simp [tendTicNewWord, httlEq]
          have hstoredTicEq :
              setUint48Offset20Word
                  (Solm.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotEvm.accountMap I) =
                setUint48Offset20Word
                  (Solm.EVM.storageLoad evmLotSolm evmLotSolm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotSolm.accountMap I) := by
            rw [hpackedLoadEq, hticNewEq]
          have hTicStateEquiv : EVMStateEquiv evmTicEvm evmTicSolm := by
            simpa [evmTicEvm, evmTicSolm] using
              EVMStateEquiv.storageStore_codeOwner hLotStateEquiv
                (bidPackedSlotOfWord (dentId I)) hstoredTicEq
          have hAccountsRet :
              accountMapEquiv (tendStoreTicMap (dentAfterLotMap σ_flux I) I)
                evmTicEvm.accountMap := by
            have hownerLot : evmLotEvm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmLotEvm, evmFluxEvm, evm0Evm, storageStore_executionEnv, initState]
            simpa [evmTicEvm, hmapLotEvm, hownerLot, tendStoreTicMap, tendStoredTicWord,
              flipperSlotWord, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, storageStore_accountMap, dentId, tendId]
              using accountMapEquiv_refl (tendStoreTicMap (dentAfterLotMap σ_flux I) I)
          have henc : returnEquiv ByteArray.empty none dentTransition.returnType := by
            rw [show dentTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
          exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
            (by simp [evmTicEvm, evmLotEvm, evmFluxEvm, storageStore_createdAccounts])
            hAccountsRet hTicStateEquiv henc
        · have hoverTicEvm :
              2 ^ 48 ≤
                (tendNow48 I).toNat +
                  (tendTtlWord (dentAfterLotMap σ_flux I) I).toNat :=
            Nat.le_of_not_gt hfitTicEvm
          have hoverTicSolm :
              2 ^ 48 ≤ (tendNow48 I).toNat +
                (tendTtlWord evmLotSolm.accountMap I).toNat := by
            have httlSolmMap :
                tendTtlWord evmLotSolm.accountMap I =
                  tendTtlWord (dentAfterLotMap σ_flux I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSolmMap] using hoverTicEvm
          have hbody :
              ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
                .reverted := by
            simpa [evm0Solm, evmLotSolm] using
              (flipperDentSourceBodyAdd48OverflowSameCaller
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmFlux := evmFluxSolm)
                (outFlux := outFlux)
                hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                hfitBeg hdec hcallerSolm hvatCodeSolm hcallFluxSolmTrue
                (by simp [evmFluxSolm, evm0Solm, initState])
                (by simp [evmFluxSolm, evm0Solm, initState]) hoverTicSolm)
          exact (flipperDentX_add48Overflow hoverTicEvm rd6272)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
