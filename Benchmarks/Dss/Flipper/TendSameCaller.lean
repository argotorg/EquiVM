import Benchmarks.Dss.Flipper.TendSourceTail
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Same-caller `tend` tail correspondence -/

theorem flipperTendBodyFrom3486SameCaller
    {σ σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hwv : I.weiValue = ⟨0⟩)
    (hguyStele : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat <
        UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcallerEvm : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hcallerStele : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD fork flipperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨_, _, rd3686⟩ :=
    flipperTendX_skipRefund hmemSize hcallerEvm h
  let memPay := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hmemPaySize : memPay.size = 96 := by
    dsimp [memPay]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hmemPayRead64 : memPay.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memPay]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  by_cases hpayZero :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩
  · have hpayZeroStele := hpayZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hpayZeroStele
    have hbody :
        ExecTransitionBody fork config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (tendLocals I) tendTransition.body .reverted := by
      simpa using
        (flipperTendSourceBodyPayNoCodeSameCaller
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
          hfitBeg hinc hcallerStele hvatNoCode)
    exact (flipperTendX_payNoCode hmemPaySize hmemPayRead64 hpayZero rd3686)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hpayNeStele :
        Reasoning.Theory.extCodeSizeWord σ
            (flipperVatTargetWord σ I) ≠ ⟨0⟩ :=
      hpayZero
    have hvatCodeStele :=
      flipperVatCode_pos_of_codeSize_ne_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hpayNeStele
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · obtain ⟨_, _, rd3800⟩ :=
        flipperTendX_payDepthLimit hmemPaySize hmemPayRead64 hpayZero hdepthEq rd3686
      let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmPayStele :=
        { evm0Stele with
          substate :=
            (Ethereum.EVM.callSubstate fork evm0Stele.accountMap (EVM.address
                (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv)) evm0Stele.substate)
                  }
      have hpayEncode :
          config.externalABI.encode? "move" (tendPayMoveArgValsOf evm0Stele I) =
            some ((tendVatPayCallMem memPay σ I).readWithPadding 128 100) := by
        simpa [evm0Stele, tendPayMoveArgValsOf, initState, solcSlotWordAt,
          solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidGalWord, bidSlotOfWord, bidBidWord, bidBaseOfWord, solcAddressSlotWord]
          using tendVatPayCallMem_encode σ I hmemPaySize
      have hcallPayStele :
          typedCallViaEVM fork config evm0Stele
            (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
            "move" 0 (tendPayMoveArgValsOf evm0Stele I)
            (false, evmPayStele, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Stele)
          (tgt := EVM.address
            (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
          (name := "move") (args := tendPayMoveArgValsOf evm0Stele I)
          (calldata := (tendVatPayCallMem memPay σ I).readWithPadding 128 100)
          (callPerm := true) hpayEncode (by simpa [evm0Stele, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody fork config contract evm0Stele (tendLocals I) tendTransition.body
            .reverted := by
        simpa [evm0Stele] using
          (flipperTendSourceBodyPayCallFailureSameCaller
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmPay := evmPayStele)
            (outPay := ByteArray.empty)
            hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
            hfitBeg hinc hcallerStele hvatCodeStele hcallPayStele)
      exact (flipperTendX_payCallFailure (by simpa using rd3800)
          (by norm_num [UInt256.size]))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdepthLt : I.depth.val < 1024 := by
        by_contra hnot
        have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
        have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
        have hval : I.depth.val = 1024 := by omega
        exact hdepthEq (Fin.ext hval)
      obtain ⟨σ_pay, zPay, outPay, A_pay, k3800, C3800, rd3800,
          hcallPayEvmRaw, houtPay⟩ :=
        flipperTendX_payPostCall (Acur := A) hmemPaySize hmemPayRead64 hpayZero
          hdepthLt rd3686
      let evm0Evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm0Stele := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmPayEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_pay
          substate := A_pay
          }
      have hcallPayEvm :
          typedCallViaEVM fork config evm0Evm
            (EVM.address (flipperVatAddress σ I)) "move" 0
            (tendPayMoveArgValsOf evm0Evm I) (zPay, evmPayEvm, outPay) true := by
        simpa [evm0Evm, evmPayEvm] using hcallPayEvmRaw
      obtain ⟨σ_pay_stele, A_pay_stele, hcallPaySteleRaw, hPayStateEquiv⟩ :=
        typedCallViaEVM_sameInputs_stateEquiv
          (evm_stele := evm0Stele) hcallPayEvm
          rfl
          (by simp [evm0Evm, evm0Stele, initState])
          (by simp [evm0Evm, evm0Stele, initState])
      let evmPayStele : EVM.State :=
        { evm0Stele with
          accountMap := σ_pay_stele
          substate := A_pay_stele
          }
      have hpayTargetEq :
          EVM.address (flipperVatAddress σ I) =
            EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv) := by
        simp [evm0Stele, initState]
      have hpayArgsEq : tendPayMoveArgValsOf evm0Evm I = tendPayMoveArgValsOf evm0Stele I := by
        rfl
      have hcallPayStele :
          typedCallViaEVM fork config evm0Stele
            (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
            "move" 0 (tendPayMoveArgValsOf evm0Stele I)
            (zPay, evmPayStele, outPay) true := by
        have hcallPaySteleRaw' :
            typedCallViaEVM fork config evm0Stele
              (EVM.address (flipperVatAddress σ I)) "move" 0
              (tendPayMoveArgValsOf evm0Evm I) (zPay, evmPayStele, outPay) true := by
          simpa [evmPayStele, evmPayEvm] using hcallPaySteleRaw
        rw [hpayTargetEq, hpayArgsEq] at hcallPaySteleRaw'
        exact hcallPaySteleRaw'
      cases zPay
      · have hcallPaySteleFalse :
            typedCallViaEVM fork config evm0Stele
              (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
              "move" 0 (tendPayMoveArgValsOf evm0Stele I)
              (false, evmPayStele, outPay) true := by
          simpa using hcallPayStele
        have hbody :
            ExecTransitionBody fork config contract evm0Stele (tendLocals I) tendTransition.body
              .reverted := by
          simpa [evm0Stele] using
            (flipperTendSourceBodyPayCallFailureSameCaller
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmPay := evmPayStele) (outPay := outPay)
              hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
              hfitBeg hinc hcallerStele hvatCodeStele hcallPaySteleFalse)
        exact (flipperTendX_payCallFailure (by simpa using rd3800) houtPay)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd3800True : RD fork flipperBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
              flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I ::
              ⟨323⟩ :: sel :: [])
            (tendVatPayCallMem memPay σ I) (UInt256.ofNat 8) outPay
            σ_pay k3800 C3800 := by
          simpa using rd3800
        obtain ⟨_, _, rd3820⟩ := flipperTendX_payCallSuccessToStoreStart rd3800True
        have hpayMemGe : 64 ≤ (tendVatPayCallMem memPay σ I).size := by
          rw [tendVatPayCallMem_size σ I hmemPaySize]
          norm_num
        have hstoreSplit := flipperTendX_storeBidToAdd48Split hpayMemGe rd3820
        have hcallPaySteleTrue :
            typedCallViaEVM fork config evm0Stele
              (EVM.address (flipperVatAddress evm0Stele.accountMap evm0Stele.executionEnv))
              "move" 0 (tendPayMoveArgValsOf evm0Stele I)
              (true, evmPayStele, outPay) true := by
          simpa using hcallPayStele
        rcases hstoreSplit with ⟨hperm, _, _, rd6272⟩ | ⟨hperm, hstatic⟩
        swap
        · have hsource := (flipperTendSourceBodySuccessSameCallerSplit
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmPay := evmPayStele) (outPay := outPay)
            hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
            hfitBeg hinc hcallerStele hvatCodeStele hcallPaySteleTrue
            (by simp [evmPayStele, evm0Stele, initState])
            (by simp [evmPayStele, evm0Stele, initState])).2 hperm
          exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
        let evmBidEvm := Stele.EVM.storageStore evmPayEvm evmPayEvm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)) (tendBid I)
        let evmBidStele := Stele.EVM.storageStore evmPayStele evmPayStele.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)) (tendBid I)
        have hPayStateEquiv' : EVMStateEquiv evmPayEvm evmPayStele := by
          simpa [evmPayEvm, evmPayStele] using hPayStateEquiv
        have hBidStateEquiv : EVMStateEquiv evmBidEvm evmBidStele := by
          simpa [evmBidEvm, evmBidStele] using
            EVMStateEquiv.storageStore_codeOwner hPayStateEquiv'
              (bidBaseOfWord (tendId I)) (by rfl : tendBid I = tendBid I)
        have hmapBidEvm : evmBidEvm.accountMap = tendAfterBidMap σ_pay I := by
          simpa [evmBidEvm, evmPayEvm, evm0Evm, tendAfterBidMap, storageStore_accountMap,
            initState]
        have httlEq :
            tendTtlWord evmBidEvm.accountMap I = tendTtlWord evmBidStele.accountMap I := by
          exact congrArg (fun accounts => tendTtlWord accounts I)
            hBidStateEquiv.accountMap
        have httlEvmMap :
            tendTtlWord evmBidEvm.accountMap I = tendTtlWord (tendAfterBidMap σ_pay I) I := by
          simpa [hmapBidEvm]
        by_cases hfitTicEvm :
            (tendNow48 I).toNat +
                (tendTtlWord (tendAfterBidMap σ_pay I) I).toNat <
              2 ^ 48
        · obtain ⟨_, _, rd3859⟩ := flipperTendX_add48Success hfitTicEvm rd6272
          have hticMemGe :
              64 ≤
                (twoWordHashMem (tendId I) ⟨1⟩
                  (tendVatPayCallMem memPay σ I)).size := by
            rw [twoWordHashMem_size_of_size_ge]
            · exact hpayMemGe
            · exact hpayMemGe
          have hret := flipperTendX_storeTicReturn hperm hticMemGe rd3859
          have hfitTicStele :
              (tendNow48 I).toNat + (tendTtlWord evmBidStele.accountMap I).toNat <
                2 ^ 48 := by
            have httlSteleMap :
                tendTtlWord evmBidStele.accountMap I =
                  tendTtlWord (tendAfterBidMap σ_pay I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSteleMap] using hfitTicEvm
          let evmTicEvm := Stele.EVM.storageStore evmBidEvm evmBidEvm.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I))
            (setUint48Offset20Word
              (Stele.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)))
              (tendTicNewWord evmBidEvm.accountMap I))
          let evmTicStele := Stele.EVM.storageStore evmBidStele evmBidStele.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I))
            (setUint48Offset20Word
              (Stele.EVM.storageLoad evmBidStele evmBidStele.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)))
              (tendTicNewWord evmBidStele.accountMap I))
          have hbody :
              ExecTransitionBody fork config contract evm0Stele (tendLocals I) tendTransition.body
                (.returned
                  { contract := contract,
                    locals := tendLocalsWithTicFrom σ evmBidStele.accountMap I }
                  evmTicStele none) := by
            simpa [evm0Stele, evmBidStele, evmTicStele] using
              (flipperTendSourceBodySuccessSameCaller (fork := fork) (hperm := by assumption)
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmPay := evmPayStele) (outPay := outPay)
                hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                hfitBeg hinc hcallerStele hvatCodeStele hcallPaySteleTrue
                (by simp [evmPayStele, evm0Stele, initState])
                (by simp [evmPayStele, evm0Stele, initState]) hfitTicStele)
          have hpackedLoadEq :
              Stele.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)) =
                Stele.EVM.storageLoad evmBidStele evmBidStele.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)) :=
            hBidStateEquiv.storageLoad_codeOwner (bidPackedSlotOfWord (tendId I))
          have hticNewEq :
              tendTicNewWord evmBidEvm.accountMap I =
                tendTicNewWord evmBidStele.accountMap I := by
            simp [tendTicNewWord, httlEq]
          have hstoredTicEq :
              setUint48Offset20Word
                  (Stele.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidEvm.accountMap I) =
                setUint48Offset20Word
                  (Stele.EVM.storageLoad evmBidStele evmBidStele.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidStele.accountMap I) := by
            rw [hpackedLoadEq, hticNewEq]
          have hTicStateEquiv : EVMStateEquiv evmTicEvm evmTicStele := by
            simpa [evmTicEvm, evmTicStele] using
              EVMStateEquiv.storageStore_codeOwner hBidStateEquiv
                (bidPackedSlotOfWord (tendId I)) hstoredTicEq
          have hAccountsRet :
              Eq (tendStoreTicMap (tendAfterBidMap σ_pay I) I)
                evmTicEvm.accountMap := by
            have hownerBid : evmBidEvm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmBidEvm, evmPayEvm, evm0Evm, storageStore_executionEnv, initState]
            simpa [evmTicEvm, hmapBidEvm, hownerBid, tendStoreTicMap, tendStoredTicWord,
              solcSlotWordAt, solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, storageStore_accountMap] using rfl
          have henc : returnEquiv ByteArray.empty none tendTransition.returnType := by
            rw [show tendTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
          exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
            (hAccountsRet.trans hTicStateEquiv.accountMap) henc
        · have hoverTicEvm :
              2 ^ 48 ≤
                (tendNow48 I).toNat +
                  (tendTtlWord (tendAfterBidMap σ_pay I) I).toNat :=
            Nat.le_of_not_gt hfitTicEvm
          have hoverTicStele :
              2 ^ 48 ≤ (tendNow48 I).toNat +
                (tendTtlWord evmBidStele.accountMap I).toNat := by
            have httlSteleMap :
                tendTtlWord evmBidStele.accountMap I =
                  tendTtlWord (tendAfterBidMap σ_pay I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSteleMap] using hoverTicEvm
          have hbody :
              ExecTransitionBody fork config contract evm0Stele (tendLocals I) tendTransition.body
                .reverted := by
            simpa [evm0Stele, evmBidStele] using
              (flipperTendSourceBodyAdd48OverflowSameCaller (fork := fork) (hperm := by assumption)
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmPay := evmPayStele) (outPay := outPay)
                hwv hguyStele hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                hfitBeg hinc hcallerStele hvatCodeStele hcallPaySteleTrue
                (by simp [evmPayStele, evm0Stele, initState])
                (by simp [evmPayStele, evm0Stele, initState]) hoverTicStele)
          exact (flipperTendX_add48Overflow hoverTicEvm rd6272)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
