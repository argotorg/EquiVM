import Benchmarks.Dss.Flipper.DentRefundEVM

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Caller-changing `dent` branch correspondence -/

theorem flipperDentBodyFrom4733Refund
    {σ σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hwv : I.weiValue = ⟨0⟩)
    (hguyStele : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat <
      UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcallerEvm : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hcallerStele : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4733⟩
      [dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let memHash := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  by_cases hrefundZero :
      Reasoning.Theory.extCodeSizeWord σ
        (flipperVatTargetWord σ I) = ⟨0⟩
  · have hrefundZeroStele :
        Reasoning.Theory.extCodeSizeWord σ
            (flipperVatTargetWord σ I) = ⟨0⟩ := hrefundZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundZeroStele
    have hbody :
        ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (dentLocals I) dentTransition.body .reverted := by
      simpa using
        (flipperDentSourceBodyRefundNoCode
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
          hfitBeg hdec hcallerStele hvatNoCode)
    exact (flipperDentX_refundNoCode hmemSize hmemRead64 hcallerEvm hrefundZero h)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hrefundNeStele :
        Reasoning.Theory.extCodeSizeWord σ
            (flipperVatTargetWord σ I) ≠ ⟨0⟩ := hrefundZero
    have hrefundCodeStele :=
      flipperVatCode_pos_of_codeSize_ne_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundNeStele
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · obtain ⟨_, _, rd4873⟩ :=
        flipperDentX_refundDepthLimit hmemSize hmemRead64 hcallerEvm hrefundZero
          hdepthEq h
      let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundStele :=
        { evm0Stele with
          substate :=
            (Ethereum.EVM.callSubstate evm0Stele.executionEnv.fork evm0Stele.accountMap (EVM.address
                (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv)) evm0Stele.substate)
                  }
      have hrefundEncode :
          config.externalABI.encode? "move" (dentRefundMoveArgValsOf evm0Stele I) =
            some ((dentVatRefundCallMem memHash σ I).readWithPadding 128 100) := by
        simpa [evm0Stele, memHash, dentRefundMoveArgValsOf, initState, solcSlotWordAt,
          solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidGuyWord, bidPackedSlotOfWord, solcAddressSlotWord]
          using dentVatRefundCallMem_encode (mem := memHash) (σ := σ) (I := I)
            hhashSize
      have hcallRefundStele :
          typedCallViaEVM config evm0Stele
            (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
            "move" 0 (dentRefundMoveArgValsOf evm0Stele I)
            (false, evmRefundStele, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Stele)
          (tgt := EVM.address
            (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
          (name := "move") (args := dentRefundMoveArgValsOf evm0Stele I)
          (calldata := (dentVatRefundCallMem memHash σ I).readWithPadding 128 100)
          (callPerm := true) hrefundEncode (by simpa [evm0Stele, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody config contract evm0Stele (dentLocals I) dentTransition.body
            .reverted := by
        simpa [evm0Stele] using
          (flipperDentSourceBodyRefundCallFailure
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
            (outRefund := ByteArray.empty)
            hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
            hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundStele)
      exact (flipperDentX_refundCallFailure (by simpa using rd4873)
          (by norm_num [UInt256.size]))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdepthLt : I.depth.val < 1024 := by
        by_contra hnot
        have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
        have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
        have hval : I.depth.val = 1024 := by omega
        exact hdepthEq (Fin.ext hval)
      obtain ⟨σ_ref, zRefund, outRefund, A_ref, k4873, C4873, rd4873,
          hcallRefundEvmRaw, houtRefund⟩ :=
        flipperDentX_refundPostCall (Acur := A) hmemSize hmemRead64 hcallerEvm
          hrefundZero hdepthLt h
      let evm0Evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_ref
          substate := A_ref
          }
      have hcallRefundEvm :
          typedCallViaEVM config evm0Evm
            (EVM.address (flipperVatAddress σ I)) "move" 0
            (dentRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundEvm, outRefund)
            true := by
        simpa [evm0Evm, evmRefundEvm] using hcallRefundEvmRaw
      obtain ⟨σ_ref_stele, A_ref_stele, hcallRefundSteleRaw, hRefundStateEquiv⟩ :=
        typedCallViaEVM_sameInputs_stateEquiv
          (evm_stele := evm0Stele) hcallRefundEvm
          rfl
          (by simp [evm0Evm, evm0Stele, initState])
          (by simp [evm0Evm, evm0Stele, initState])
      let evmRefundStele : EVM.State :=
        { evm0Stele with
          accountMap := σ_ref_stele
          substate := A_ref_stele
          }
      have hrefundTargetEq :
          EVM.address (flipperVatAddress σ I) =
            EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv) := by
        simp [evm0Stele, initState]
      have hrefundArgsEq :
          dentRefundMoveArgValsOf evm0Evm I = dentRefundMoveArgValsOf evm0Stele I := rfl
      have hcallRefundStele :
          typedCallViaEVM config evm0Stele
            (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
            "move" 0 (dentRefundMoveArgValsOf evm0Stele I)
            (zRefund, evmRefundStele, outRefund) true := by
        have hcallRefundSteleRaw' :
            typedCallViaEVM config evm0Stele
              (EVM.address (flipperVatAddress σ I)) "move" 0
              (dentRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundStele, outRefund)
              true := by
          simpa [evmRefundStele, evmRefundEvm] using hcallRefundSteleRaw
        rw [hrefundTargetEq, hrefundArgsEq] at hcallRefundSteleRaw'
        exact hcallRefundSteleRaw'
      cases zRefund
      · have hcallRefundSteleFalse :
            typedCallViaEVM config evm0Stele
              (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
              "move" 0 (dentRefundMoveArgValsOf evm0Stele I)
              (false, evmRefundStele, outRefund) true := by
          simpa using hcallRefundStele
        have hbody :
            ExecTransitionBody config contract evm0Stele (dentLocals I) dentTransition.body
              .reverted := by
          simpa [evm0Stele] using
            (flipperDentSourceBodyRefundCallFailure
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
              (outRefund := outRefund)
              hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
              hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundSteleFalse)
        exact (flipperDentX_refundCallFailure (by simpa using rd4873) houtRefund)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd4873True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4873⟩
            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
              flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
              ⟨323⟩ :: sel :: [])
            (dentVatRefundCallMem memHash σ I) (UInt256.ofNat 8) outRefund
            σ_ref k4873 C4873 := by
          simpa [memHash] using rd4873
        obtain ⟨_, _, rd4893⟩ := flipperDentX_refundCallSuccessToStoreStart rd4873True
        have hrefundMemSize : (dentVatRefundCallMem memHash σ I).size = 228 :=
          dentVatRefundCallMem_size hhashSize
        have hrefundMemRead64 :
            (dentVatRefundCallMem memHash σ I).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          dentVatRefundCallMem_read64 hhashSize hhashRead64
        have hrefundMemGe : 64 ≤ (dentVatRefundCallMem memHash σ I).size := by
          rw [hrefundMemSize]
          norm_num
        rcases flipperDentX_storeRefundGuyToFluxStartSplit hrefundMemGe rd4893 with
            ⟨hperm, _, _, rd4927⟩ | ⟨hperm, hstatic⟩
        swap
        · have hsource := ExecFuncBody.execBlockStatic
            ((flipperDentSourceBlockAfterRefundSuccessTailSplit
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmRefund := evmRefundStele) (outRefund := outRefund) (r := .staticViolation)
              hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
              hfitBeg hdec hcallerStele hrefundCodeStele
              (by simpa [evm0Stele] using hcallRefundStele)).2 hperm)
          exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
        let evmGuyEvm := Stele.EVM.storageStore evmRefundEvm
          evmRefundEvm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
          (setAddressOffset0Word
            (Stele.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
              (bidPackedSlotOfWord (dentId I)))
            (solcSourceWord evmRefundEvm.executionEnv))
        let evmGuyStele := Stele.EVM.storageStore evmRefundStele
          evmRefundStele.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
          (setAddressOffset0Word
            (Stele.EVM.storageLoad evmRefundStele evmRefundStele.executionEnv.codeOwner
              (bidPackedSlotOfWord (dentId I)))
            (solcSourceWord evmRefundStele.executionEnv))
        have hRefundStateEquiv' : EVMStateEquiv evmRefundEvm evmRefundStele := by
          simpa [evmRefundEvm, evmRefundStele] using hRefundStateEquiv
        have hpackedLoadEq :
            Stele.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)) =
              Stele.EVM.storageLoad evmRefundStele evmRefundStele.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)) :=
          hRefundStateEquiv'.storageLoad_codeOwner (bidPackedSlotOfWord (dentId I))
        have hsourceEq :
            solcSourceWord evmRefundEvm.executionEnv =
              solcSourceWord evmRefundStele.executionEnv := by
          rw [hRefundStateEquiv'.executionEnv]
        have hstoredGuyEq :
            setAddressOffset0Word
                (Stele.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)))
                (solcSourceWord evmRefundEvm.executionEnv) =
              setAddressOffset0Word
                (Stele.EVM.storageLoad evmRefundStele evmRefundStele.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)))
                (solcSourceWord evmRefundStele.executionEnv) := by
          rw [hpackedLoadEq, hsourceEq]
        have hGuyStateEquiv : EVMStateEquiv evmGuyEvm evmGuyStele := by
          simpa [evmGuyEvm, evmGuyStele] using
            EVMStateEquiv.storageStore_codeOwner hRefundStateEquiv'
              (bidPackedSlotOfWord (dentId I)) hstoredGuyEq
        have hmapGuyEvm : evmGuyEvm.accountMap = dentAfterRefundMap σ_ref I := by
          simpa [evmGuyEvm, evmRefundEvm, evm0Evm, dentAfterRefundMap,
            storageStore_accountMap, initState, Stele.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, solcSlotWordAt, solcSlotWord]
        let memFlux := twoWordHashMem (dentId I) ⟨1⟩ (dentVatRefundCallMem memHash σ I)
        have hmemFluxSize : memFlux.size = 228 := by
          dsimp [memFlux]
          calc
            (twoWordHashMem (dentId I) ⟨1⟩
                (dentVatRefundCallMem memHash σ I)).size =
                (dentVatRefundCallMem memHash σ I).size :=
              twoWordHashMem_size_of_size_ge (dentId I) ⟨1⟩ (by
                rw [hrefundMemSize]
                norm_num)
            _ = 228 := hrefundMemSize
        have hmemFluxRead64 :
            memFlux.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          dsimp [memFlux]
          exact dentVatHashMem_read64_228 (I := I) hrefundMemSize hrefundMemRead64
        have hcallRefundSteleTrue :
            typedCallViaEVM config evm0Stele
              (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
              "move" 0 (dentRefundMoveArgValsOf evm0Stele I)
              (true, evmRefundStele, outRefund) true := by
          simpa using hcallRefundStele
        by_cases hfluxZero :
            Reasoning.Theory.extCodeSizeWord (dentAfterRefundMap σ_ref I)
              (flipperVatTargetWord (dentAfterRefundMap σ_ref I) I) = ⟨0⟩
        · have hfluxZeroEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) = ⟨0⟩ := by
            simpa [hmapGuyEvm] using hfluxZero
          have hfluxZeroStele :
              Reasoning.Theory.extCodeSizeWord evmGuyStele.accountMap
                (flipperVatTargetWord evmGuyStele.accountMap I) = ⟨0⟩ :=
            by rw [← hGuyStateEquiv.accountMap]; exact hfluxZeroEvm
          have hfluxNoCodeStele :
              (UInt256.ofNat
                ((evmGuyStele.lookupAccount
                  (flipperVatAddress evmGuyStele.accountMap
                    evmGuyStele.executionEnv)).option
                  0 (fun acc => acc.code.size))).toNat = 0 := by
            simpa [evmGuyStele, evmRefundStele, evm0Stele, initState,
              storageStore_executionEnv, State.lookupAccount] using
              extCodeSizeWord_zero_lookup_code_zero
                (σ := evmGuyStele.accountMap)
                (target := flipperVatTargetWord evmGuyStele.accountMap I)
                (addr := flipperVatAddress evmGuyStele.accountMap I)
                (flipperVatAddress_eq_target evmGuyStele.accountMap I) hfluxZeroStele
          have hbody :
              ExecTransitionBody config contract evm0Stele (dentLocals I) dentTransition.body
                .reverted := by
            simpa [evm0Stele, evmGuyStele] using
              (flipperDentSourceBodyFluxNoCodeAfterRefund (hperm := by assumption)
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
                (outRefund := outRefund)
                hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundSteleTrue
                hfluxNoCodeStele)
          exact (flipperDentX_fluxNoCodeAw8 hmemFluxSize hmemFluxRead64 hfluxZero rd4927)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hfluxNeEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) ≠ ⟨0⟩ := by
            simpa [hmapGuyEvm] using hfluxZero
          have hfluxNeStele :
              Reasoning.Theory.extCodeSizeWord evmGuyStele.accountMap
                (flipperVatTargetWord evmGuyStele.accountMap I) ≠ ⟨0⟩ :=
            by rw [← hGuyStateEquiv.accountMap]; exact hfluxNeEvm
          have hfluxCodeStele :
              0 <
                (UInt256.ofNat
                  ((evmGuyStele.lookupAccount
                    (flipperVatAddress evmGuyStele.accountMap
                      evmGuyStele.executionEnv)).option
                    0 (fun acc => acc.code.size))).toNat := by
            simpa [evmGuyStele, evmRefundStele, evm0Stele, initState,
              storageStore_executionEnv, State.lookupAccount] using
              extCodeSizeWord_ne_zero_lookup_code_pos
                (σ := evmGuyStele.accountMap)
                (target := flipperVatTargetWord evmGuyStele.accountMap I)
                (addr := flipperVatAddress evmGuyStele.accountMap I)
                (flipperVatAddress_eq_target evmGuyStele.accountMap I) hfluxNeStele
          let evmGuyCallEvm : EVM.State :=
            { evm0Evm with
              accountMap := dentAfterRefundMap σ_ref I
              substate := A_ref
              }
          have hGuyCallStateEquiv : EVMStateEquiv evmGuyCallEvm evmGuyStele := by
            refine ⟨?_, ?_⟩
            · simp [evmGuyCallEvm, evmGuyStele, evmRefundStele, evm0Evm, evm0Stele,
                storageStore_executionEnv, initState]
            · simpa [evmGuyCallEvm, hmapGuyEvm] using hGuyStateEquiv.accountMap
          obtain ⟨σ_flux, zFlux, outFlux, A_flux, k5053, C5053, rd5053,
              hcallFluxEvmRaw, houtFlux⟩ :=
            flipperDentX_fluxPostCallAw8 (Acur := A_ref) hmemFluxSize hmemFluxRead64
              hfluxZero hperm hdepthLt rd4927
          let evmFluxEvm : EVM.State :=
            { evmGuyCallEvm with
              accountMap := σ_flux
              substate := A_flux
              }
          have hcallFluxEvm :
              typedCallViaEVM config evmGuyCallEvm
                (EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                "flux" 0 (dentFluxArgValsOf evmGuyCallEvm I)
                (zFlux, evmFluxEvm, outFlux) true := by
            simpa [evmFluxEvm, evmGuyCallEvm, evm0Evm] using hcallFluxEvmRaw
          obtain ⟨σ_flux_stele, A_flux_stele, hcallFluxSteleRaw, hFluxStateEquiv⟩ :=
            typedCallViaEVM_sameInputs_stateEquiv
              (evm_stele := evmGuyStele) hcallFluxEvm hGuyCallStateEquiv.accountMap
              (by simp [evmGuyCallEvm, evmGuyStele, evmRefundStele, evm0Evm, evm0Stele,
                storageStore_σ₀, initState])
              hGuyCallStateEquiv.executionEnv
          let evmFluxStele : EVM.State :=
            { evmGuyStele with
              accountMap := σ_flux_stele
              substate := A_flux_stele
              }
          have hfluxTargetEq :
              EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv) =
                EVM.address
                  (flipperVatAddress evmGuyStele.accountMap evmGuyStele.executionEnv) := by
            rw [hGuyCallStateEquiv.executionEnv, hGuyCallStateEquiv.accountMap]
          have hfluxArgsEq :
              dentFluxArgValsOf evmGuyCallEvm I = dentFluxArgValsOf evmGuyStele I := by
            have hloadIlk :
                Stele.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner ⟨3⟩ =
                  Stele.EVM.storageLoad evmGuyStele evmGuyStele.executionEnv.codeOwner ⟨3⟩ :=
              hGuyCallStateEquiv.storageLoad_codeOwner ⟨3⟩
            have hloadUsr :
                Stele.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨3⟩) =
                  Stele.EVM.storageLoad evmGuyStele evmGuyStele.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨3⟩) :=
              hGuyCallStateEquiv.storageLoad_codeOwner (bidSlotOfWord (dentId I) ⟨3⟩)
            have hloadLot :
                Stele.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨1⟩) =
                  Stele.EVM.storageLoad evmGuyStele evmGuyStele.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨1⟩) :=
              hGuyCallStateEquiv.storageLoad_codeOwner (bidSlotOfWord (dentId I) ⟨1⟩)
            simp [dentFluxArgValsOf]
            constructor
            · simpa using congrArg EVM.Word.toBytesBE hloadIlk
            · constructor
              · rw [hGuyCallStateEquiv.executionEnv]
              · constructor
                · simpa using
                    congrArg (fun w => AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)
                      hloadUsr
                · simpa using congrArg (fun w => (UInt256.sub w (dentLot I)).toNat) hloadLot
          have hcallFluxStele :
              typedCallViaEVM config evmGuyStele
                (EVM.address
                  (flipperVatAddress evmGuyStele.accountMap evmGuyStele.executionEnv))
                "flux" 0 (dentFluxArgValsOf evmGuyStele I)
                (zFlux, evmFluxStele, outFlux) true := by
            have hcallFluxSteleRaw' :
                typedCallViaEVM config evmGuyStele
                  (EVM.address
                    (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuyCallEvm I)
                  (zFlux, evmFluxStele, outFlux) true := by
              simpa [evmFluxStele, evmFluxEvm] using hcallFluxSteleRaw
            rw [hfluxTargetEq, hfluxArgsEq] at hcallFluxSteleRaw'
            exact hcallFluxSteleRaw'
          cases zFlux
          · have hcallFluxSteleFalse :
                typedCallViaEVM config evmGuyStele
                  (EVM.address
                    (flipperVatAddress evmGuyStele.accountMap evmGuyStele.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuyStele I)
                  (false, evmFluxStele, outFlux) true := by
              simpa using hcallFluxStele
            have hbody :
                ExecTransitionBody config contract evm0Stele (dentLocals I) dentTransition.body
                  .reverted := by
              simpa [evm0Stele, evmGuyStele] using
                (flipperDentSourceBodyFluxCallFailureAfterRefund (hperm := by assumption)
                  (σ := σ) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
                  (evmFlux := evmFluxStele) (outRefund := outRefund) (outFlux := outFlux)
                  hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                  hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundSteleTrue
                  hfluxCodeStele hcallFluxSteleFalse)
            exact (flipperDentX_fluxCallFailure (by simpa using rd5053) houtFlux)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have rd5053True : RD flipperBytecode I (Sat256.ofUInt256 g)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
                (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                  flipperVatTargetWord (dentAfterRefundMap σ_ref I) I :: dentBid I ::
                  dentLot I :: dentId I :: ⟨323⟩ :: sel :: [])
                (dentVatFluxCallMem memFlux (dentAfterRefundMap σ_ref I) I)
                (UInt256.ofNat 9) outFlux σ_flux k5053 C5053 := by
              simpa [memFlux] using rd5053
            obtain ⟨_, _, rd5073⟩ := flipperDentX_fluxCallSuccessToStoreStart rd5053True
            have hfluxMemGe :
                64 ≤ (dentVatFluxCallMem memFlux (dentAfterRefundMap σ_ref I) I).size := by
              rw [dentVatFluxCallMem_size_228 (dentAfterRefundMap σ_ref I) I hmemFluxSize]
              norm_num
            obtain ⟨_, _, rd6272⟩ := flipperDentX_storeLotToAdd48 hperm hfluxMemGe rd5073
            have hcallFluxSteleTrue :
                typedCallViaEVM config evmGuyStele
                  (EVM.address
                    (flipperVatAddress evmGuyStele.accountMap evmGuyStele.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuyStele I)
                  (true, evmFluxStele, outFlux) true := by
              simpa using hcallFluxStele
            let evmLotEvm := Stele.EVM.storageStore evmFluxEvm
              evmFluxEvm.executionEnv.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
            let evmLotStele := Stele.EVM.storageStore evmFluxStele
              evmFluxStele.executionEnv.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
            have hFluxStateEquiv' : EVMStateEquiv evmFluxEvm evmFluxStele := by
              simpa [evmFluxEvm, evmFluxStele] using hFluxStateEquiv
            have hLotStateEquiv : EVMStateEquiv evmLotEvm evmLotStele := by
              simpa [evmLotEvm, evmLotStele] using
                EVMStateEquiv.storageStore_codeOwner hFluxStateEquiv'
                  (bidSlotOfWord (dentId I) ⟨1⟩) (by rfl : dentLot I = dentLot I)
            have hmapLotEvm : evmLotEvm.accountMap = dentAfterLotMap σ_flux I := by
              simpa [evmLotEvm, evmFluxEvm, evmGuyCallEvm, evm0Evm, dentAfterLotMap,
                storageStore_accountMap, storageStore_executionEnv, initState]
            have httlEq :
                tendTtlWord evmLotEvm.accountMap I = tendTtlWord evmLotStele.accountMap I := by
              exact congrArg (fun accounts => tendTtlWord accounts I)
                hLotStateEquiv.accountMap
            have httlEvmMap :
                tendTtlWord evmLotEvm.accountMap I =
                  tendTtlWord (dentAfterLotMap σ_flux I) I := by
              simpa [hmapLotEvm]
            by_cases hfitTicEvm :
                (tendNow48 I).toNat +
                    (tendTtlWord (dentAfterLotMap σ_flux I) I).toNat <
                  2 ^ 48
            · obtain ⟨_, _, rd3859⟩ := flipperDentX_add48Success hfitTicEvm rd6272
              have hticMemGe :
                  64 ≤
                    (twoWordHashMem (dentId I) ⟨1⟩
                      (dentVatFluxCallMem memFlux (dentAfterRefundMap σ_ref I) I)).size := by
                rw [twoWordHashMem_size_of_size_ge]
                · exact hfluxMemGe
                · exact hfluxMemGe
              have hret := flipperDentX_storeTicReturn hperm hticMemGe rd3859
              have hfitTicStele :
                  (tendNow48 I).toNat + (tendTtlWord evmLotStele.accountMap I).toNat <
                    2 ^ 48 := by
                have httlSteleMap :
                    tendTtlWord evmLotStele.accountMap I =
                      tendTtlWord (dentAfterLotMap σ_flux I) I := by
                  rw [← httlEq, httlEvmMap]
                simpa [httlSteleMap] using hfitTicEvm
              let evmTicEvm := Stele.EVM.storageStore evmLotEvm
                evmLotEvm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
                (setUint48Offset20Word
                  (Stele.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotEvm.accountMap I))
              let evmTicStele := Stele.EVM.storageStore evmLotStele
                evmLotStele.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
                (setUint48Offset20Word
                  (Stele.EVM.storageLoad evmLotStele evmLotStele.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotStele.accountMap I))
              have hbody :
                  ExecTransitionBody config contract evm0Stele (dentLocals I)
                    dentTransition.body
                    (.returned
                      { contract := contract,
                        locals :=
                          dentLocalsAfterRefundWithTicFrom σ evmLotStele.accountMap I }
                      evmTicStele none) := by
                simpa [evm0Stele, evmGuyStele, evmLotStele, evmTicStele] using
                  (flipperDentSourceBodySuccessAfterRefund (hperm := by assumption)
                    (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
                    (evmFlux := evmFluxStele) (outRefund := outRefund) (outFlux := outFlux)
                    hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                    hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundSteleTrue
                    hfluxCodeStele hcallFluxSteleTrue
                    (by simp [evmFluxStele, evmGuyStele, evmRefundStele, evm0Stele, initState,
                      storageStore_executionEnv])
                    (by simp [evmFluxStele, evmGuyStele, evmRefundStele, evm0Stele, initState,
                      storageStore_executionEnv]) hfitTicStele)
              have hpackedLoadEq :
                  Stele.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                      (bidPackedSlotOfWord (dentId I)) =
                    Stele.EVM.storageLoad evmLotStele evmLotStele.executionEnv.codeOwner
                      (bidPackedSlotOfWord (dentId I)) :=
                hLotStateEquiv.storageLoad_codeOwner (bidPackedSlotOfWord (dentId I))
              have hticNewEq :
                  tendTicNewWord evmLotEvm.accountMap I =
                    tendTicNewWord evmLotStele.accountMap I := by
                simp [tendTicNewWord, httlEq]
              have hstoredTicEq :
                  setUint48Offset20Word
                      (Stele.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                        (bidPackedSlotOfWord (dentId I)))
                      (tendTicNewWord evmLotEvm.accountMap I) =
                    setUint48Offset20Word
                      (Stele.EVM.storageLoad evmLotStele evmLotStele.executionEnv.codeOwner
                        (bidPackedSlotOfWord (dentId I)))
                      (tendTicNewWord evmLotStele.accountMap I) := by
                rw [hpackedLoadEq, hticNewEq]
              have hTicStateEquiv : EVMStateEquiv evmTicEvm evmTicStele := by
                simpa [evmTicEvm, evmTicStele] using
                  EVMStateEquiv.storageStore_codeOwner hLotStateEquiv
                    (bidPackedSlotOfWord (dentId I)) hstoredTicEq
              have hAccountsRet :
                  Eq (tendStoreTicMap (dentAfterLotMap σ_flux I) I)
                    evmTicEvm.accountMap := by
                have hownerLot : evmLotEvm.executionEnv.codeOwner = I.codeOwner := by
                  simp [evmLotEvm, evmFluxEvm, evmGuyCallEvm, evm0Evm,
                    storageStore_executionEnv, initState]
                simpa [evmTicEvm, hmapLotEvm, hownerLot, tendStoreTicMap,
                  tendStoredTicWord, solcSlotWordAt, solcSlotWord, Stele.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, storageStore_accountMap, dentId,
                  tendId] using rfl
              have henc : returnEquiv ByteArray.empty none dentTransition.returnType := by
                rw [show dentTransition.returnType = [] by rfl]
                exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
              exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
                (hAccountsRet.trans hTicStateEquiv.accountMap) henc
            · have hoverTicEvm :
                  2 ^ 48 ≤
                    (tendNow48 I).toNat +
                      (tendTtlWord (dentAfterLotMap σ_flux I) I).toNat :=
                Nat.le_of_not_gt hfitTicEvm
              have hoverTicStele :
                  2 ^ 48 ≤ (tendNow48 I).toNat +
                    (tendTtlWord evmLotStele.accountMap I).toNat := by
                have httlSteleMap :
                    tendTtlWord evmLotStele.accountMap I =
                      tendTtlWord (dentAfterLotMap σ_flux I) I := by
                  rw [← httlEq, httlEvmMap]
                simpa [httlSteleMap] using hoverTicEvm
              have hbody :
                  ExecTransitionBody config contract evm0Stele (dentLocals I)
                    dentTransition.body .reverted := by
                simpa [evm0Stele, evmGuyStele, evmLotStele] using
                  (flipperDentSourceBodyAdd48OverflowAfterRefund (hperm := by assumption)
                    (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundStele)
                    (evmFlux := evmFluxStele) (outRefund := outRefund) (outFlux := outFlux)
                    hwv hguyStele hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                    hfitBeg hdec hcallerStele hrefundCodeStele hcallRefundSteleTrue
                    hfluxCodeStele hcallFluxSteleTrue
                    (by simp [evmFluxStele, evmGuyStele, evmRefundStele, evm0Stele, initState,
                      storageStore_executionEnv])
                    (by simp [evmFluxStele, evmGuyStele, evmRefundStele, evm0Stele, initState,
                      storageStore_executionEnv]) hoverTicStele)
              exact (flipperDentX_add48Overflow hoverTicEvm rd6272)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
