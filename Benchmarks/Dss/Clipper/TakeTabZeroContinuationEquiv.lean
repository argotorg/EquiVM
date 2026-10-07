import Benchmarks.Dss.Clipper.TakeNonzeroFromFluxEquiv
import Benchmarks.Dss.Clipper.TakeGeneralContinuationEVM
import Benchmarks.Dss.Clipper.TakePostDogContinuationEVM
import Benchmarks.Dss.Clipper.TakeGenericZeroSource
import Benchmarks.Dss.Clipper.TakeRemoveEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- A purchase that clears the tab but leaves collateral first refunds that
   collateral to the sale's saved `usr`, then removes the sale. -/
set_option maxHeartbeats 12000000 in
theorem clipperTakeTabZeroContinuationEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σCont : AccountMap}
    {evmCont : EVM.State} {locals : Store}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (List.map Param.name takeTransition.params)
      (transitionSignature takeTransition).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd4701 : RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata σCont k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccounts : Eq σCont evmCont.accountMap)
    (hevmSigma0 : evmCont.σ₀ = σ₀)
    (hevmEnv : evmCont.executionEnv = I)
    (hdogClean : UInt256.land solcAddrMask dog = dog)
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tabNew.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lotNew.toNat)))
    (hdog : locals.get? "dog_" =
      some (.address (AccountAddress.ofNat dog.toNat)))
    (husr : locals.get? "usr" =
      some (.address (AccountAddress.ofNat packed.toNat)))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hidWord : id = clipperTakeIdWord I)
    (hlocked : locals.get? "locked" = none)
    (hvow : locals.get? "vow" = none)
    (htabZero : tabNew = ⟨0⟩) (hlotNe : lotNew ≠ ⟨0⟩)
    (hsourceReverted :
      ExecBlock config (Frame.mk contract locals (immStore v)) evmCont
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted →
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v))
    (hsourceReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock config (Frame.mk contract locals (immStore v)) evmCont
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) (.ok finalFrame finalEvm) →
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body
        (.returned finalFrame finalEvm none) (immStore v))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeRefinementFor config contract
      σ σ₀ g A I (immStore v) := by
  let evmContEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σCont }
  have hvowWord : clipperTakeVowTarget σCont I = clipperTakeVowEVMWord evmCont := by
    have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccounts
    simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmEnv,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hslot]
  have hdogAddress : AccountAddress.ofNat dog.toNat =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog) := by
    rw [hdogClean, accountAddress_ofUInt256_eq_ofNat_toNat]
  have hmoveArgs := clipperEvalTakeGenericVatMoveArgs
    (v := v) (evm := evmCont) howe hvow
  have closeRevert
      (hrev : RDrev code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      (htail : ExecBlock config (Frame.mk contract locals (immStore v)) evmCont
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted) :
      runtimeRefinementFor config contract
        σ σ₀ g A I (immStore v) :=
    hrev.reEquivExecutionRevert hcode hdispatch hdec (hsourceReverted htail)
  apply RD.clipperTakeGeneralContinuationElim v hpatch rd4701 hmem hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm : (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccounts] using hnoCode)
    exact closeRevert hrev
      (execBlockAppendReverted (clipperTakeGenericVatMoveNoCode hnoCodeSolm))
  · intro σMove outMove AMove hmoveCode hcallMove hrev
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove }
    obtain ⟨evmMove,
      hcallMoveSolm,
      _,
      _,
      _⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [initState, hevmSigma0])

        (by simp [initState, hevmEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccounts] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM config evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (false, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    exact closeRevert hrev
      (execBlockAppendReverted
        (clipperTakeGenericVatMoveFailure hmoveArgs hmoveCodeSolm hcallMoveSolm'))
  · intro _ _ _ hlotZero _ _ _ _
    exact (hlotNe hlotZero).elim
  · intro _ _ _ _ _ _ hlotZero _ _ _ _ _
    exact (hlotNe hlotZero).elim
  · intro _ _ _ _ _ _ _ _ hlotZero _ _ _ _ _ _
    exact (hlotNe hlotZero).elim
  · intro σMove outMove AMove _hlot hmoveCode hcallMove hdogNoCode hrev
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove }
    obtain ⟨evmMove,
      hcallMoveSolm,
      hAccountsMove,
      _,
      _⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [initState, hevmSigma0])

        (by simp [initState, hevmEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccounts] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM config evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogNoCodeSolm : (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_zero_lookup_code_zero
          rfl
          (by simpa only [← hAccountsMove] using hdogNoCode)
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogRev := clipperTakeGenericDogNonzeroNoCode (v := v)
      hdog hlot hlotNe hdogNoCodeSolm
    have hafter : ExecBlock config
        (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
        (clipperTakeAfterMoveStmts) .reverted := by
      simpa [clipperTakeAfterMoveStmts] using execBlockAppendReverted hdogRev
    exact closeRevert hrev (execBlockAppendOk hmove hafter)
  · intro σMove outMove AMove σDog outDog ADog _hlot
      hmoveCode hcallMove hdogCode hcallDog hrev
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove }
    let evmDogEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog }
    obtain ⟨evmMove,
      hcallMoveSolm,
      hAccountsMove,
      hevmMoveSigma0,
      hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [initState, hevmSigma0])

        (by simp [initState, hevmEnv]) hcallMove
    obtain ⟨evmDog,
      hcallDogSolm,
      _,
      _,
      _⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccounts] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM config evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          rfl
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogSolm' : typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)] (false, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogRev := clipperTakeGenericDogNonzeroFailure (v := v)
      hdog howe hlot hlotNe hdogCodeSolm hcallDogSolm'
    have hafter : ExecBlock config
        (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
        (clipperTakeAfterMoveStmts) .reverted := by
      simpa [clipperTakeAfterMoveStmts] using execBlockAppendReverted hdogRev
    exact closeRevert hrev (execBlockAppendOk hmove hafter)
  · intro σMove outMove AMove σDog outDog ADog kDog CDog _hlot
      hmoveCode hcallMove hdogCode hcallDog hmemDog rd5003
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove }
    let evmDogEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog }
    obtain ⟨evmMove,
      hcallMoveSolm,
      hAccountsMove,
      hevmMoveSigma0,
      hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [initState, hevmSigma0])

        (by simp [initState, hevmEnv]) hcallMove
    obtain ⟨evmDog,
      hcallDogSolm,
      hAccountsDog,
      hevmDogSigma0,
      hevmDogEnv⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccounts] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM config evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          rfl
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogSolm' : typedCallViaEVM config evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)] (true, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogOk := clipperTakeGenericDogNonzeroSuccess (v := v)
      hdog howe hlot hlotNe hdogCodeSolm hcallDogSolm'
    let postLocals := clipperTakeGenericDigsRet locals
    have husr' : postLocals.get? "usr" =
        some (.address (AccountAddress.ofNat packed.toNat)) := by
      simpa [postLocals, clipperTakeGenericDigsRet, clipperTakeGenericMoveRet,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using husr
    have htab' : postLocals.get? "tab" =
        some (.int (Int.ofNat tabNew.toNat)) := by
      simpa [postLocals, clipperTakeGenericDigsRet, clipperTakeGenericMoveRet,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using htab
    have hlot' : postLocals.get? "lot" =
        some (.int (Int.ofNat lotNew.toNat)) := by
      simpa [postLocals, clipperTakeGenericDigsRet, clipperTakeGenericMoveRet,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hlot
    have hid' : postLocals.get? "id" = some (clipperTakeIdValue I) := by
      simpa [postLocals, clipperTakeGenericDigsRet, clipperTakeGenericMoveRet,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hid
    have hlocked' : postLocals.get? "locked" = none := by
      simpa [postLocals, clipperTakeGenericDigsRet, clipperTakeGenericMoveRet,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hlocked
    let evmPostDogEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog }
    apply RD.clipperTakePostDogTabZeroContinuationElim v hpatch rd5003 hlotNe
      htabZero hmemDog hdepth hperm
    · intro hfluxNoCode hrev
      have hfluxNoCodeSolm : (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_zero_lookup_code_zero
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hfluxNoCode)
      have hpost := clipperTakeGenericPostDogTabZeroNoCode
        htab' hlot' htabZero hlotNe hfluxNoCodeSolm
      have hafter : ExecBlock config
          (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
          (clipperTakeAfterMoveStmts) .reverted := by
        simpa [clipperTakeAfterMoveStmts, postLocals] using
          execBlockAppendOk hdogOk hpost
      exact closeRevert hrev (execBlockAppendOk hmove hafter)
    · intro σFlux outFlux AFlux hfluxCode hcallFlux hrev
      let evmFluxEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux }
      obtain ⟨evmFlux,
      hcallFluxSolm,
      _,
      _,
      _⟩ :=
        clipperTypedCallSyncFromState
          (cfg := config) (evmEvm := evmPostDogEvm) (evmSolm := evmDog)
          (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmPostDogEvm, initState] using hevmDogSigma0)



          (by simpa [evmDogEvm, evmPostDogEvm, initState] using hevmDogEnv) hcallFlux
      have hfluxCodeSolm : 0 < (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_ne_zero_lookup_code_pos
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hfluxCode)
      have hcallFluxSolm' : typedCallViaEVM config evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat packed.toNat),
            .int (Int.ofNat lotNew.toNat)]
          (false, evmFlux, outFlux) true := by
        simpa [evmPostDogEvm, evmFluxEvm, hevmDogEnv] using hcallFluxSolm
      have hpost := clipperTakeGenericPostDogTabZeroFailure
        husr' htab' hlot' htabZero hlotNe hfluxCodeSolm hcallFluxSolm'
      have hafter : ExecBlock config
          (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
          (clipperTakeAfterMoveStmts) .reverted := by
        simpa [clipperTakeAfterMoveStmts, postLocals] using
          execBlockAppendOk hdogOk hpost
      exact closeRevert hrev (execBlockAppendOk hmove hafter)
    · intro σFlux outFlux AFlux kFlux CFlux hfluxCode hcallFlux
        hmemFlux rd8274
      let evmFluxEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux }
      obtain ⟨evmFlux,
      hcallFluxSolm,
      hAccountsFlux,
      _hevmFluxSigma0,
      hevmFluxEnv⟩ :=
        clipperTypedCallSyncFromState
          (cfg := config) (evmEvm := evmPostDogEvm) (evmSolm := evmDog)
          (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmPostDogEvm, initState] using hevmDogSigma0)



          (by simpa [evmDogEvm, evmPostDogEvm, initState] using hevmDogEnv) hcallFlux
      have hfluxCodeSolm : 0 < (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_ne_zero_lookup_code_pos
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hfluxCode)
      have hcallFluxSolm' : typedCallViaEVM config evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat packed.toNat),
            .int (Int.ofNat lotNew.toNat)]
          (true, evmFlux, outFlux) true := by
        simpa [evmPostDogEvm, evmFluxEvm, hevmDogEnv] using hcallFluxSolm
      apply clipperTakeRemoveEquiv v hpatch hcode hdispatch hdec rd8274
        (by simpa [clipperTakeIdWord, clipperYankArgWord] using hidWord)
        hmemFlux hperm hAccountsFlux hevmFluxEnv
      · intro hremove
        have hpost := clipperTakeGenericPostDogTabZeroRemoveReverts
          husr' htab' hlot' hid' htabZero hlotNe hfluxCodeSolm hcallFluxSolm' hremove
        have hafter : ExecBlock config
            (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
            (clipperTakeAfterMoveStmts) .reverted := by
          simpa [clipperTakeAfterMoveStmts, postLocals] using
            execBlockAppendOk hdogOk hpost
        exact hsourceReverted (execBlockAppendOk hmove hafter)
      · intro callee evmRemove hremove
        let resultLocals :=
          (postLocals.insert "_fluxUsrRet" .unit).insert "_removeRet2" .unit
        have hpost := clipperTakeGenericPostDogTabZeroRemoveOk
          husr' htab' hlot' hid' hlocked' htabZero hlotNe hfluxCodeSolm
            hcallFluxSolm' hremove
        have hafter : ExecBlock config
            (Frame.mk contract (clipperTakeGenericMoveRet locals) (immStore v)) evmMove
            (clipperTakeAfterMoveStmts)
            (.ok (Frame.mk contract resultLocals (immStore v))
              (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner
                ⟨13⟩ ⟨0⟩)) := by
          simpa [clipperTakeAfterMoveStmts, postLocals, resultLocals] using
            execBlockAppendOk hdogOk hpost
        exact ⟨Frame.mk contract resultLocals (immStore v),
          hsourceReturned (execBlockAppendOk hmove hafter)⟩

theorem clipperTakeTabZeroContinuation
    (v : ClipperImmutables) {code : ByteArray}

    {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256}
    {slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt
      id sel : UInt256}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (List.map Param.name takeTransition.params)
      (transitionSignature takeTransition).paramTypes I.calldata =
        some (clipperTakeStore I))
    (hidWord : id = clipperTakeIdWord I)
    (htabZero : tabNew = ⟨0⟩) (hlotNe : lotNew ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ClipperTakeStoreContinuationEquiv v code σ σ₀ A I g
      slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt
      id sel := by
  intro σCont evmCont locals dog mem rdata aw k C rd4701 hmem hAccounts
    hevmSigma0 hevmEnv hdogClean howe htab hlot
    hdog husr hid hlocked hvow _hsales hsourceReverted hsourceReturned
  exact clipperTakeTabZeroContinuationEquiv (locals := locals) v hpatch hcode
    hdispatch hdec rd4701 hmem hAccounts hevmSigma0 hevmEnv hdogClean howe htab hlot hdog husr hid hidWord hlocked hvow
    htabZero hlotNe hsourceReverted hsourceReturned hdepth hperm

end Benchmarks.Dss.Clipper
