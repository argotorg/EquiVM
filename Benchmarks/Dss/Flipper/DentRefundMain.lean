import Benchmarks.Dss.Flipper.DentRefundEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Caller-changing `dent` branch correspondence -/

theorem flipperDentBodyFrom4733Refund
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
    (hcallerEvm : solcSourceWord I ≠ bidGuyWord (dentId I) σ_evm I)
    (hcallerSolm : solcSourceWord I ≠ bidGuyWord (dentId I) σ_solm I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4733⟩
      [dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let memHash := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  by_cases hrefundZero :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flipperVatTargetWord σ_evm I) = ⟨0⟩
  · have hrefundZeroSolm :
        Reasoning.Theory.extCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) = ⟨0⟩ :=
      flipperVatCodeSize_zero_accountMapEquiv hAccounts hrefundZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundZeroSolm
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (dentLocals I) dentTransition.body .reverted := by
      simpa using
        (flipperDentSourceBodyRefundNoCode (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
          hfitBeg hdec hcallerSolm hvatNoCode)
    exact (flipperDentX_refundNoCode hmemSize hmemRead64 hcallerEvm hrefundZero h)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hrefundNeSolm :
        Reasoning.Theory.extCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
      flipperVatCodeSize_ne_zero_accountMapEquiv hAccounts hrefundZero
    have hrefundCodeSolm :=
      flipperVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundNeSolm
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · obtain ⟨_, _, rd4873⟩ :=
        flipperDentX_refundDepthLimit hmemSize hmemRead64 hcallerEvm hrefundZero
          hdepthEq h
      let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundSolm :=
        { evm0Solm with
          substate :=
            (evm0Solm.addAccessedAccount
              (EVM.address
                (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))).substate }
      have hrefundEncode :
          config.externalABI.encode? "move" (dentRefundMoveArgValsOf evm0Solm I) =
            some ((dentVatRefundCallMem memHash σ_solm I).readWithPadding 128 100) := by
        simpa [evm0Solm, memHash, dentRefundMoveArgValsOf, initState, flipperSlotWord,
          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidGuyWord, bidPackedSlotOfWord, flipperAddressReturnWord]
          using dentVatRefundCallMem_encode (mem := memHash) (σ := σ_solm) (I := I)
            hhashSize
      have hcallRefundSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (dentRefundMoveArgValsOf evm0Solm I)
            (false, evmRefundSolm, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Solm)
          (tgt := EVM.address
            (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
          (name := "move") (args := dentRefundMoveArgValsOf evm0Solm I)
          (calldata := (dentVatRefundCallMem memHash σ_solm I).readWithPadding 128 100)
          (callPerm := true) hrefundEncode (by simpa [evm0Solm, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
            .reverted := by
        simpa [evm0Solm] using
          (flipperDentSourceBodyRefundCallFailure
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
            (outRefund := ByteArray.empty)
            hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
            hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolm)
      exact (flipperDentX_refundCallFailure (by simpa using rd4873)
          (by norm_num [UInt256.size]))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdepthLt : I.depth.val < 1024 := by
        by_contra hnot
        have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
        have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
        have hval : I.depth.val = 1024 := by omega
        exact hdepthEq (Fin.ext hval)
      obtain ⟨cA_ref, σ_ref, zRefund, outRefund, A_ref, k4873, C4873, rd4873,
          hcallRefundEvmRaw, houtRefund⟩ :=
        flipperDentX_refundPostCall (Acur := A) hmemSize hmemRead64 hcallerEvm
          hrefundZero hperm hdepthLt h
      let evm0Evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_ref
          substate := A_ref
          createdAccounts := cA_ref }
      have hcallRefundEvm :
          typedCallViaEVM config evm0Evm
            (EVM.address (flipperVatAddress σ_evm I)) "move" 0
            (dentRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundEvm, outRefund)
            true := by
        simpa [evm0Evm, evmRefundEvm] using hcallRefundEvmRaw
      obtain ⟨σ_ref_solm, A_ref_solm, hcallRefundSolmRaw, hRefundStateEquiv⟩ :=
        flipper_typedCallViaEVM_accountMapEquiv_noSubstate
          (evm_solm := evm0Solm) hcallRefundEvm
          (by simpa [evm0Evm, evm0Solm] using hAccounts)
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
      let evmRefundSolm : EVM.State :=
        { evm0Solm with
          accountMap := σ_ref_solm
          substate := A_ref_solm
          createdAccounts := cA_ref }
      have hrefundTargetEq :
          EVM.address (flipperVatAddress σ_evm I) =
            EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv) := by
        rw [flipperVatAddress_accountMapEquiv hAccounts]
        simp [evm0Solm, initState]
      have hrefundArgsEq :
          dentRefundMoveArgValsOf evm0Evm I = dentRefundMoveArgValsOf evm0Solm I := by
        have hloadPacked :
            Solm.EVM.storageLoad evm0Evm I.codeOwner (bidPackedSlotOfWord (dentId I)) =
              Solm.EVM.storageLoad evm0Solm I.codeOwner (bidPackedSlotOfWord (dentId I)) := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner
              (bidPackedSlotOfWord (dentId I))
        simp [dentRefundMoveArgValsOf]
        constructor
        · simp [evm0Evm, evm0Solm, initState]
        · have hownerEvm : evm0Evm.executionEnv.codeOwner = I.codeOwner := by
            simp [evm0Evm, initState]
          have hownerSolm : evm0Solm.executionEnv.codeOwner = I.codeOwner := by
            simp [evm0Solm, initState]
          rw [hownerEvm, hownerSolm, hloadPacked]
      have hcallRefundSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (dentRefundMoveArgValsOf evm0Solm I)
            (zRefund, evmRefundSolm, outRefund) true := by
        have hcallRefundSolmRaw' :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress σ_evm I)) "move" 0
              (dentRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundSolm, outRefund)
              true := by
          simpa [evmRefundSolm, evmRefundEvm] using hcallRefundSolmRaw
        rw [hrefundTargetEq, hrefundArgsEq] at hcallRefundSolmRaw'
        exact hcallRefundSolmRaw'
      cases zRefund
      · have hcallRefundSolmFalse :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (dentRefundMoveArgValsOf evm0Solm I)
              (false, evmRefundSolm, outRefund) true := by
          simpa using hcallRefundSolm
        have hbody :
            ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
              .reverted := by
          simpa [evm0Solm] using
            (flipperDentSourceBodyRefundCallFailure
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
              (outRefund := outRefund)
              hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
              hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolmFalse)
        exact (flipperDentX_refundCallFailure (by simpa using rd4873) houtRefund)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd4873True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4873⟩
            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
              flipperVatTargetWord σ_evm I :: dentBid I :: dentLot I :: dentId I ::
              ⟨323⟩ :: sel :: [])
            (dentVatRefundCallMem memHash σ_evm I) (UInt256.ofNat 8) outRefund
            (cA_ref, σ_ref) k4873 C4873 := by
          simpa [memHash] using rd4873
        obtain ⟨_, _, rd4893⟩ := flipperDentX_refundCallSuccessToStoreStart rd4873True
        have hrefundMemSize : (dentVatRefundCallMem memHash σ_evm I).size = 228 :=
          dentVatRefundCallMem_size hhashSize
        have hrefundMemRead64 :
            (dentVatRefundCallMem memHash σ_evm I).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          dentVatRefundCallMem_read64 hhashSize hhashRead64
        have hrefundMemGe : 64 ≤ (dentVatRefundCallMem memHash σ_evm I).size := by
          rw [hrefundMemSize]
          norm_num
        obtain ⟨_, _, rd4927⟩ := flipperDentX_storeRefundGuyToFluxStart
          hperm hrefundMemGe rd4893
        let evmGuyEvm := Solm.EVM.storageStore evmRefundEvm
          evmRefundEvm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
              (bidPackedSlotOfWord (dentId I)))
            (solcSourceWord evmRefundEvm.executionEnv))
        let evmGuySolm := Solm.EVM.storageStore evmRefundSolm
          evmRefundSolm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
              (bidPackedSlotOfWord (dentId I)))
            (solcSourceWord evmRefundSolm.executionEnv))
        have hRefundStateEquiv' : EVMStateEquiv evmRefundEvm evmRefundSolm := by
          simpa [evmRefundEvm, evmRefundSolm] using hRefundStateEquiv
        have hpackedLoadEq :
            Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)) =
              Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dentId I)) :=
          hRefundStateEquiv'.storageLoad_codeOwner (bidPackedSlotOfWord (dentId I))
        have hsourceEq :
            solcSourceWord evmRefundEvm.executionEnv =
              solcSourceWord evmRefundSolm.executionEnv := by
          rw [hRefundStateEquiv'.executionEnv]
        have hstoredGuyEq :
            setAddressOffset0Word
                (Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)))
                (solcSourceWord evmRefundEvm.executionEnv) =
              setAddressOffset0Word
                (Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (dentId I)))
                (solcSourceWord evmRefundSolm.executionEnv) := by
          rw [hpackedLoadEq, hsourceEq]
        have hGuyStateEquiv : EVMStateEquiv evmGuyEvm evmGuySolm := by
          simpa [evmGuyEvm, evmGuySolm] using
            EVMStateEquiv.storageStore_codeOwner hRefundStateEquiv'
              (bidPackedSlotOfWord (dentId I)) hstoredGuyEq
        have hmapGuyEvm : evmGuyEvm.accountMap = dentAfterRefundMap σ_ref I := by
          simpa [evmGuyEvm, evmRefundEvm, evm0Evm, dentAfterRefundMap,
            storageStore_accountMap, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, flipperSlotWord, solcSlotWord]
        let memFlux := twoWordHashMem (dentId I) ⟨1⟩ (dentVatRefundCallMem memHash σ_evm I)
        have hmemFluxSize : memFlux.size = 228 := by
          dsimp [memFlux]
          calc
            (twoWordHashMem (dentId I) ⟨1⟩
                (dentVatRefundCallMem memHash σ_evm I)).size =
                (dentVatRefundCallMem memHash σ_evm I).size :=
              tendTwoWordHashMem_size_of_size_ge (dentId I) ⟨1⟩ (by
                rw [hrefundMemSize]
                norm_num)
            _ = 228 := hrefundMemSize
        have hmemFluxRead64 :
            memFlux.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          dsimp [memFlux]
          exact dentVatHashMem_read64_228 (I := I) hrefundMemSize hrefundMemRead64
        have hcallRefundSolmTrue :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (dentRefundMoveArgValsOf evm0Solm I)
              (true, evmRefundSolm, outRefund) true := by
          simpa using hcallRefundSolm
        by_cases hfluxZero :
            Reasoning.Theory.extCodeSizeWord (dentAfterRefundMap σ_ref I)
              (flipperVatTargetWord (dentAfterRefundMap σ_ref I) I) = ⟨0⟩
        · have hfluxZeroEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) = ⟨0⟩ := by
            simpa [hmapGuyEvm] using hfluxZero
          have hfluxZeroSolm :
              Reasoning.Theory.extCodeSizeWord evmGuySolm.accountMap
                (flipperVatTargetWord evmGuySolm.accountMap I) = ⟨0⟩ :=
            flipperVatCodeSize_zero_accountMapEquiv hGuyStateEquiv.accountMap hfluxZeroEvm
          have hfluxNoCodeSolm :
              (UInt256.ofNat
                ((evmGuySolm.lookupAccount
                  (flipperVatAddress evmGuySolm.accountMap
                    evmGuySolm.executionEnv)).option
                  0 (fun acc => acc.code.size))).toNat = 0 := by
            simpa [evmGuySolm, evmRefundSolm, evm0Solm, initState,
              storageStore_executionEnv, State.lookupAccount] using
              flipper_extCodeSizeWord_zero_lookup_code_zero
                (σ := evmGuySolm.accountMap)
                (target := flipperVatTargetWord evmGuySolm.accountMap I)
                (addr := flipperVatAddress evmGuySolm.accountMap I)
                (flipperVatAddress_eq_target evmGuySolm.accountMap I) hfluxZeroSolm
          have hbody :
              ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
                .reverted := by
            simpa [evm0Solm, evmGuySolm] using
              (flipperDentSourceBodyFluxNoCodeAfterRefund
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                (outRefund := outRefund)
                hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                hfluxNoCodeSolm)
          exact (flipperDentX_fluxNoCodeAw8 hmemFluxSize hmemFluxRead64 hfluxZero rd4927)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hfluxNeEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) ≠ ⟨0⟩ := by
            simpa [hmapGuyEvm] using hfluxZero
          have hfluxNeSolm :
              Reasoning.Theory.extCodeSizeWord evmGuySolm.accountMap
                (flipperVatTargetWord evmGuySolm.accountMap I) ≠ ⟨0⟩ :=
            flipperVatCodeSize_ne_zero_accountMapEquiv hGuyStateEquiv.accountMap hfluxNeEvm
          have hfluxCodeSolm :
              0 <
                (UInt256.ofNat
                  ((evmGuySolm.lookupAccount
                    (flipperVatAddress evmGuySolm.accountMap
                      evmGuySolm.executionEnv)).option
                    0 (fun acc => acc.code.size))).toNat := by
            simpa [evmGuySolm, evmRefundSolm, evm0Solm, initState,
              storageStore_executionEnv, State.lookupAccount] using
              flipper_extCodeSizeWord_pos_lookup_code_pos
                (σ := evmGuySolm.accountMap)
                (target := flipperVatTargetWord evmGuySolm.accountMap I)
                (addr := flipperVatAddress evmGuySolm.accountMap I)
                (flipperVatAddress_eq_target evmGuySolm.accountMap I) hfluxNeSolm
          let evmGuyCallEvm : EVM.State :=
            { evm0Evm with
              accountMap := dentAfterRefundMap σ_ref I
              substate := A_ref
              createdAccounts := cA_ref }
          have hGuyCallStateEquiv : EVMStateEquiv evmGuyCallEvm evmGuySolm := by
            refine ⟨?_, ?_, ?_⟩
            · simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                storageStore_executionEnv, initState]
            · simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Solm,
                storageStore_createdAccounts, initState]
            · simpa [evmGuyCallEvm, hmapGuyEvm] using hGuyStateEquiv.accountMap
          obtain ⟨cA_flux, σ_flux, zFlux, outFlux, A_flux, k5053, C5053, rd5053,
              hcallFluxEvmRaw, houtFlux⟩ :=
            flipperDentX_fluxPostCallAw8 (Acur := A_ref) hmemFluxSize hmemFluxRead64
              hfluxZero hperm hdepthLt rd4927
          let evmFluxEvm : EVM.State :=
            { evmGuyCallEvm with
              accountMap := σ_flux
              substate := A_flux
              createdAccounts := cA_flux }
          have hcallFluxEvm :
              typedCallViaEVM config evmGuyCallEvm
                (EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                "flux" 0 (dentFluxArgValsOf evmGuyCallEvm I)
                (zFlux, evmFluxEvm, outFlux) true := by
            simpa [evmFluxEvm, evmGuyCallEvm, evm0Evm] using hcallFluxEvmRaw
          obtain ⟨σ_flux_solm, A_flux_solm, hcallFluxSolmRaw, hFluxStateEquiv⟩ :=
            flipper_typedCallViaEVM_accountMapEquiv_noSubstate
              (evm_solm := evmGuySolm) hcallFluxEvm hGuyCallStateEquiv.accountMap
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_sigma0, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Solm,
                storageStore_createdAccounts, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_genesisBlockHeader, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_blocks, initState])
              (by simpa using hGuyCallStateEquiv.executionEnv.symm)
          let evmFluxSolm : EVM.State :=
            { evmGuySolm with
              accountMap := σ_flux_solm
              substate := A_flux_solm
              createdAccounts := cA_flux }
          have hfluxTargetEq :
              EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv) =
                EVM.address
                  (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv) := by
            rw [hGuyCallStateEquiv.executionEnv]
            rw [flipperVatAddress_accountMapEquiv hGuyCallStateEquiv.accountMap]
          have hfluxArgsEq :
              dentFluxArgValsOf evmGuyCallEvm I = dentFluxArgValsOf evmGuySolm I := by
            have hloadIlk :
                Solm.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner ⟨3⟩ =
                  Solm.EVM.storageLoad evmGuySolm evmGuySolm.executionEnv.codeOwner ⟨3⟩ :=
              hGuyCallStateEquiv.storageLoad_codeOwner ⟨3⟩
            have hloadUsr :
                Solm.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨3⟩) =
                  Solm.EVM.storageLoad evmGuySolm evmGuySolm.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨3⟩) :=
              hGuyCallStateEquiv.storageLoad_codeOwner (bidSlotOfWord (dentId I) ⟨3⟩)
            have hloadLot :
                Solm.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidSlotOfWord (dentId I) ⟨1⟩) =
                  Solm.EVM.storageLoad evmGuySolm evmGuySolm.executionEnv.codeOwner
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
          have hcallFluxSolm :
              typedCallViaEVM config evmGuySolm
                (EVM.address
                  (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                "flux" 0 (dentFluxArgValsOf evmGuySolm I)
                (zFlux, evmFluxSolm, outFlux) true := by
            have hcallFluxSolmRaw' :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuyCallEvm I)
                  (zFlux, evmFluxSolm, outFlux) true := by
              simpa [evmFluxSolm, evmFluxEvm] using hcallFluxSolmRaw
            rw [hfluxTargetEq, hfluxArgsEq] at hcallFluxSolmRaw'
            exact hcallFluxSolmRaw'
          cases zFlux
          · have hcallFluxSolmFalse :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuySolm I)
                  (false, evmFluxSolm, outFlux) true := by
              simpa using hcallFluxSolm
            have hbody :
                ExecTransitionBody config contract evm0Solm (dentLocals I) dentTransition.body
                  .reverted := by
              simpa [evm0Solm, evmGuySolm] using
                (flipperDentSourceBodyFluxCallFailureAfterRefund
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                  (evmFlux := evmFluxSolm) (outRefund := outRefund) (outFlux := outFlux)
                  hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                  hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                  hfluxCodeSolm hcallFluxSolmFalse)
            exact (flipperDentX_fluxCallFailure (by simpa using rd5053) houtFlux)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have rd5053True : RD flipperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
                (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
                  flipperVatTargetWord (dentAfterRefundMap σ_ref I) I :: dentBid I ::
                  dentLot I :: dentId I :: ⟨323⟩ :: sel :: [])
                (dentVatFluxCallMem memFlux (dentAfterRefundMap σ_ref I) I)
                (UInt256.ofNat 9) outFlux (cA_flux, σ_flux) k5053 C5053 := by
              simpa [memFlux] using rd5053
            obtain ⟨_, _, rd5073⟩ := flipperDentX_fluxCallSuccessToStoreStart rd5053True
            have hfluxMemGe :
                64 ≤ (dentVatFluxCallMem memFlux (dentAfterRefundMap σ_ref I) I).size := by
              rw [dentVatFluxCallMem_size_228 (dentAfterRefundMap σ_ref I) I hmemFluxSize]
              norm_num
            obtain ⟨_, _, rd6272⟩ := flipperDentX_storeLotToAdd48 hperm hfluxMemGe rd5073
            have hcallFluxSolmTrue :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                  "flux" 0 (dentFluxArgValsOf evmGuySolm I)
                  (true, evmFluxSolm, outFlux) true := by
              simpa using hcallFluxSolm
            let evmLotEvm := Solm.EVM.storageStore evmFluxEvm
              evmFluxEvm.executionEnv.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
            let evmLotSolm := Solm.EVM.storageStore evmFluxSolm
              evmFluxSolm.executionEnv.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
            have hFluxStateEquiv' : EVMStateEquiv evmFluxEvm evmFluxSolm := by
              simpa [evmFluxEvm, evmFluxSolm] using hFluxStateEquiv
            have hLotStateEquiv : EVMStateEquiv evmLotEvm evmLotSolm := by
              simpa [evmLotEvm, evmLotSolm] using
                EVMStateEquiv.storageStore_codeOwner hFluxStateEquiv'
                  (bidSlotOfWord (dentId I) ⟨1⟩) (by rfl : dentLot I = dentLot I)
            have hmapLotEvm : evmLotEvm.accountMap = dentAfterLotMap σ_flux I := by
              simpa [evmLotEvm, evmFluxEvm, evmGuyCallEvm, evm0Evm, dentAfterLotMap,
                storageStore_accountMap, storageStore_executionEnv, initState]
            have httlEq :
                tendTtlWord evmLotEvm.accountMap I = tendTtlWord evmLotSolm.accountMap I := by
              unfold tendTtlWord flipperUint48Offset0Word flipperSlotWord solcSlotWord
              rw [accountMapEquiv_storage_findD hLotStateEquiv.accountMap I.codeOwner ⟨5⟩ ⟨0⟩]
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
              let evmTicEvm := Solm.EVM.storageStore evmLotEvm
                evmLotEvm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
                (setUint48Offset20Word
                  (Solm.EVM.storageLoad evmLotEvm evmLotEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotEvm.accountMap I))
              let evmTicSolm := Solm.EVM.storageStore evmLotSolm
                evmLotSolm.executionEnv.codeOwner (bidPackedSlotOfWord (dentId I))
                (setUint48Offset20Word
                  (Solm.EVM.storageLoad evmLotSolm evmLotSolm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (dentId I)))
                  (tendTicNewWord evmLotSolm.accountMap I))
              have hbody :
                  ExecTransitionBody config contract evm0Solm (dentLocals I)
                    dentTransition.body
                    (.returned
                      { contract := contract,
                        locals :=
                          dentLocalsAfterRefundWithTicFrom σ_solm evmLotSolm.accountMap I }
                      evmTicSolm none) := by
                simpa [evm0Solm, evmGuySolm, evmLotSolm, evmTicSolm] using
                  (flipperDentSourceBodySuccessAfterRefund
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                    (evmFlux := evmFluxSolm) (outRefund := outRefund) (outFlux := outFlux)
                    hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                    hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                    hfluxCodeSolm hcallFluxSolmTrue
                    (by simp [evmFluxSolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv])
                    (by simp [evmFluxSolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv]) hfitTicSolm)
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
                  simp [evmLotEvm, evmFluxEvm, evmGuyCallEvm, evm0Evm,
                    storageStore_executionEnv, initState]
                simpa [evmTicEvm, hmapLotEvm, hownerLot, tendStoreTicMap,
                  tendStoredTicWord, flipperSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, storageStore_accountMap, dentId,
                  tendId]
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
                  ExecTransitionBody config contract evm0Solm (dentLocals I)
                    dentTransition.body .reverted := by
                simpa [evm0Solm, evmGuySolm, evmLotSolm] using
                  (flipperDentSourceBodyAdd48OverflowAfterRefund
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                    (evmFlux := evmFluxSolm) (outRefund := outRefund) (outFlux := outFlux)
                    hwv hguySolm hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot
                    hfitBeg hdec hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                    hfluxCodeSolm hcallFluxSolmTrue
                    (by simp [evmFluxSolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv])
                    (by simp [evmFluxSolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv]) hoverTicSolm)
              exact (flipperDentX_add48Overflow hoverTicEvm rd6272)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
