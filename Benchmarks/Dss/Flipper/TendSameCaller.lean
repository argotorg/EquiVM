import Benchmarks.Dss.Flipper.TendSourceTail
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Same-caller `tend` tail correspondence -/

theorem flipperTendBodyFrom3486SameCaller
    {σ σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hguySolm : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
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
    (hcallerSolm : solcSourceWord I = bidGuyWord (tendId I) σ I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
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
  · have hpayZeroSolm := hpayZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hpayZeroSolm
    have hbody :
        ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (tendLocals I) tendTransition.body .reverted := by
      simpa using
        (flipperTendSourceBodyPayNoCodeSameCaller
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
          hfitBeg hinc hcallerSolm hvatNoCode)
    exact (flipperTendX_payNoCode hmemPaySize hmemPayRead64 hpayZero rd3686)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hpayNeSolm :
        Reasoning.Theory.extCodeSizeWord σ
            (flipperVatTargetWord σ I) ≠ ⟨0⟩ :=
      hpayZero
    have hvatCodeSolm :=
      flipperVatCode_pos_of_codeSize_ne_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hpayNeSolm
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · obtain ⟨_, _, rd3800⟩ :=
        flipperTendX_payDepthLimit hmemPaySize hmemPayRead64 hpayZero hdepthEq rd3686
      let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmPaySolm :=
        { evm0Solm with
          substate :=
            (evm0Solm.addAccessedAccount
              (EVM.address
                (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))).substate }
      have hpayEncode :
          config.externalABI.encode? "move" (tendPayMoveArgValsOf evm0Solm I) =
            some ((tendVatPayCallMem memPay σ I).readWithPadding 128 100) := by
        simpa [evm0Solm, tendPayMoveArgValsOf, initState, flipperSlotWord,
          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidGalWord, bidSlotOfWord, bidBidWord, bidBaseOfWord, flipperAddressReturnWord]
          using tendVatPayCallMem_encode σ I hmemPaySize
      have hcallPaySolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (tendPayMoveArgValsOf evm0Solm I)
            (false, evmPaySolm, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Solm)
          (tgt := EVM.address
            (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
          (name := "move") (args := tendPayMoveArgValsOf evm0Solm I)
          (calldata := (tendVatPayCallMem memPay σ I).readWithPadding 128 100)
          (callPerm := true) hpayEncode (by simpa [evm0Solm, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
            .reverted := by
        simpa [evm0Solm] using
          (flipperTendSourceBodyPayCallFailureSameCaller
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmPay := evmPaySolm)
            (outPay := ByteArray.empty)
            hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
            hfitBeg hinc hcallerSolm hvatCodeSolm hcallPaySolm)
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
        flipperTendX_payPostCall (Acur := A) hmemPaySize hmemPayRead64 hpayZero hperm
          hdepthLt rd3686
      let evm0Evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmPayEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_pay
          substate := A_pay
          }
      have hcallPayEvm :
          typedCallViaEVM config evm0Evm
            (EVM.address (flipperVatAddress σ I)) "move" 0
            (tendPayMoveArgValsOf evm0Evm I) (zPay, evmPayEvm, outPay) true := by
        simpa [evm0Evm, evmPayEvm] using hcallPayEvmRaw
      obtain ⟨σ_pay_solm, A_pay_solm, hcallPaySolmRaw, hPayStateEquiv⟩ :=
        typedCallViaEVM_sameInputs_stateEquiv
          (evm_solm := evm0Solm) hcallPayEvm
          rfl
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
      let evmPaySolm : EVM.State :=
        { evm0Solm with
          accountMap := σ_pay_solm
          substate := A_pay_solm
          }
      have hpayTargetEq :
          EVM.address (flipperVatAddress σ I) =
            EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv) := by
        simp [evm0Solm, initState]
      have hpayArgsEq : tendPayMoveArgValsOf evm0Evm I = tendPayMoveArgValsOf evm0Solm I := by
        rfl
      have hcallPaySolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (tendPayMoveArgValsOf evm0Solm I)
            (zPay, evmPaySolm, outPay) true := by
        have hcallPaySolmRaw' :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress σ I)) "move" 0
              (tendPayMoveArgValsOf evm0Evm I) (zPay, evmPaySolm, outPay) true := by
          simpa [evmPaySolm, evmPayEvm] using hcallPaySolmRaw
        rw [hpayTargetEq, hpayArgsEq] at hcallPaySolmRaw'
        exact hcallPaySolmRaw'
      cases zPay
      · have hcallPaySolmFalse :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (tendPayMoveArgValsOf evm0Solm I)
              (false, evmPaySolm, outPay) true := by
          simpa using hcallPaySolm
        have hbody :
            ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
              .reverted := by
          simpa [evm0Solm] using
            (flipperTendSourceBodyPayCallFailureSameCaller
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmPay := evmPaySolm) (outPay := outPay)
              hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
              hfitBeg hinc hcallerSolm hvatCodeSolm hcallPaySolmFalse)
        exact (flipperTendX_payCallFailure (by simpa using rd3800) houtPay)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd3800True : RD flipperBytecode I (Sat256.ofUInt256 g)
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
        obtain ⟨_, _, rd6272⟩ := flipperTendX_storeBidToAdd48 hperm hpayMemGe rd3820
        have hcallPaySolmTrue :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (tendPayMoveArgValsOf evm0Solm I)
              (true, evmPaySolm, outPay) true := by
          simpa using hcallPaySolm
        let evmBidEvm := Solm.EVM.storageStore evmPayEvm evmPayEvm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)) (tendBid I)
        let evmBidSolm := Solm.EVM.storageStore evmPaySolm evmPaySolm.executionEnv.codeOwner
          (bidBaseOfWord (tendId I)) (tendBid I)
        have hPayStateEquiv' : EVMStateEquiv evmPayEvm evmPaySolm := by
          simpa [evmPayEvm, evmPaySolm] using hPayStateEquiv
        have hBidStateEquiv : EVMStateEquiv evmBidEvm evmBidSolm := by
          simpa [evmBidEvm, evmBidSolm] using
            EVMStateEquiv.storageStore_codeOwner hPayStateEquiv'
              (bidBaseOfWord (tendId I)) (by rfl : tendBid I = tendBid I)
        have hmapBidEvm : evmBidEvm.accountMap = tendAfterBidMap σ_pay I := by
          simpa [evmBidEvm, evmPayEvm, evm0Evm, tendAfterBidMap, storageStore_accountMap,
            initState]
        have httlEq :
            tendTtlWord evmBidEvm.accountMap I = tendTtlWord evmBidSolm.accountMap I := by
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
            rw [tendTwoWordHashMem_size_of_size_ge]
            · exact hpayMemGe
            · exact hpayMemGe
          have hret := flipperTendX_storeTicReturn hperm hticMemGe rd3859
          have hfitTicSolm :
              (tendNow48 I).toNat + (tendTtlWord evmBidSolm.accountMap I).toNat <
                2 ^ 48 := by
            have httlSolmMap :
                tendTtlWord evmBidSolm.accountMap I =
                  tendTtlWord (tendAfterBidMap σ_pay I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSolmMap] using hfitTicEvm
          let evmTicEvm := Solm.EVM.storageStore evmBidEvm evmBidEvm.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I))
            (setUint48Offset20Word
              (Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)))
              (tendTicNewWord evmBidEvm.accountMap I))
          let evmTicSolm := Solm.EVM.storageStore evmBidSolm evmBidSolm.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I))
            (setUint48Offset20Word
              (Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)))
              (tendTicNewWord evmBidSolm.accountMap I))
          have hbody :
              ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
                (.returned
                  { contract := contract,
                    locals := tendLocalsWithTicFrom σ evmBidSolm.accountMap I }
                  evmTicSolm none) := by
            simpa [evm0Solm, evmBidSolm, evmTicSolm] using
              (flipperTendSourceBodySuccessSameCaller
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmPay := evmPaySolm) (outPay := outPay)
                hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                hfitBeg hinc hcallerSolm hvatCodeSolm hcallPaySolmTrue
                (by simp [evmPaySolm, evm0Solm, initState])
                (by simp [evmPaySolm, evm0Solm, initState]) hfitTicSolm)
          have hpackedLoadEq :
              Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)) =
                Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)) :=
            hBidStateEquiv.storageLoad_codeOwner (bidPackedSlotOfWord (tendId I))
          have hticNewEq :
              tendTicNewWord evmBidEvm.accountMap I =
                tendTicNewWord evmBidSolm.accountMap I := by
            simp [tendTicNewWord, httlEq]
          have hstoredTicEq :
              setUint48Offset20Word
                  (Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidEvm.accountMap I) =
                setUint48Offset20Word
                  (Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidSolm.accountMap I) := by
            rw [hpackedLoadEq, hticNewEq]
          have hTicStateEquiv : EVMStateEquiv evmTicEvm evmTicSolm := by
            simpa [evmTicEvm, evmTicSolm] using
              EVMStateEquiv.storageStore_codeOwner hBidStateEquiv
                (bidPackedSlotOfWord (tendId I)) hstoredTicEq
          have hAccountsRet :
              Eq (tendStoreTicMap (tendAfterBidMap σ_pay I) I)
                evmTicEvm.accountMap := by
            have hownerBid : evmBidEvm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmBidEvm, evmPayEvm, evm0Evm, storageStore_executionEnv, initState]
            simpa [evmTicEvm, hmapBidEvm, hownerBid, tendStoreTicMap, tendStoredTicWord,
              flipperSlotWord, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
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
          have hoverTicSolm :
              2 ^ 48 ≤ (tendNow48 I).toNat +
                (tendTtlWord evmBidSolm.accountMap I).toNat := by
            have httlSolmMap :
                tendTtlWord evmBidSolm.accountMap I =
                  tendTtlWord (tendAfterBidMap σ_pay I) I := by
              rw [← httlEq, httlEvmMap]
            simpa [httlSolmMap] using hoverTicEvm
          have hbody :
              ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
                .reverted := by
            simpa [evm0Solm, evmBidSolm] using
              (flipperTendSourceBodyAdd48OverflowSameCaller
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmPay := evmPaySolm) (outPay := outPay)
                hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                hfitBeg hinc hcallerSolm hvatCodeSolm hcallPaySolmTrue
                (by simp [evmPaySolm, evm0Solm, initState])
                (by simp [evmPaySolm, evm0Solm, initState]) hoverTicSolm)
          exact (flipperTendX_add48Overflow hoverTicEvm rd6272)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
