import Benchmarks.Dss.Clipper.TakeDynamicRemove
import Benchmarks.Dss.Clipper.TakeCallbackContinuationEquiv
import Benchmarks.Dss.Clipper.TakeGeneralContinuationEVM
import Benchmarks.Dss.Clipper.TakeGenericContinuationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- The chost branches always leave both `tab` and `lot` nonzero.  This theorem is
   deliberately parameterized by the live local bindings, so dead arithmetic scratch
   variables do not leak into the external-call and storage proof. -/
set_option maxHeartbeats 8000000 in
theorem clipperTakeNonzeroStoreContinuationEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σCbEvm : AccountMap}
    {evmCb : EVM.State} {locals : Store}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (rd4701 : RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata σCbEvm k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccountsCb : Eq σCbEvm evmCb.accountMap)
    (hevmCbSigma0 : evmCb.σ₀ = σ₀)
    (hevmCbEnv : evmCb.executionEnv = I)
    (hdogClean : UInt256.land solcAddrMask dog = dog)
    (howe : locals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tabNew.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat lotNew.toNat)))
    (hdog : locals.get? "dog_" =
      some (.address (AccountAddress.ofNat dog.toNat)))
    (hid : locals.get? "id" = some (clipperTakeIdValue I))
    (hidWord : id = clipperTakeIdWord I)
    (hlocked : locals.get? "locked" = none)
    (hvow : locals.get? "vow" = none)
    (hsales : locals.get? "sales" = none)
    (htabNe : tabNew ≠ ⟨0⟩) (hlotNe : lotNew ≠ ⟨0⟩)
    (hsourceReverted :
      ExecBlock (config v) (Frame.mk (contract v) locals) evmCb
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted →
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v) (Frame.mk (contract v) locals) evmCb
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm) →
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned finalFrame finalEvm none))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      σ σ₀ g A I := by
  let evmCbEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σCbEvm }
  have hvowWord : clipperTakeVowTarget σCbEvm I = clipperTakeVowEVMWord evmCb := by
    have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsCb
    simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmCbEnv,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hslot]
  have hdogAddress : AccountAddress.ofNat dog.toNat =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog) := by
    rw [hdogClean, accountAddress_ofUInt256_eq_ofNat_toNat]
  have hmoveArgs := clipperEvalTakeGenericVatMoveArgs
    (v := v) (evm := evmCb) howe hvow
  have closeRevert
      (hrev : RDrev code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      (htail : ExecBlock (config v) (Frame.mk (contract v) locals) evmCb
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted) :
      runtimeEquivalenceFor (config v) (contract v)
        σ σ₀ g A I :=
    hrev.reEquivExecutionRevert hcode hdispatch hdec (hsourceReverted htail)
  apply RD.clipperTakeGeneralContinuationElim v hpatch rd4701 hmem hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm :
        (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hnoCode)
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
      clipperTypedCallSyncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat owe.toNat)] (false, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, hvowWord] using hcallMoveSolm
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
      clipperTypedCallSyncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, hvowWord] using hcallMoveSolm
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
    have hafter : ExecBlock (config v)
        (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
        (clipperTakeAfterMoveStmts v) .reverted := by
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
      clipperTypedCallSyncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    obtain ⟨evmDog,
      hcallDogSolm,
      hAccountsDog,
      _,
      _⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          rfl
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)] (false, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogRev := clipperTakeGenericDogNonzeroFailure (v := v)
      hdog howe hlot hlotNe hdogCodeSolm hcallDogSolm'
    have hafter : ExecBlock (config v)
        (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
        (clipperTakeAfterMoveStmts v) .reverted := by
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
      clipperTypedCallSyncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    obtain ⟨evmDog,
      hcallDogSolm,
      hAccountsDog,
      _hevmDogSigma0,
      hevmDogEnv⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos
          rfl
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)] (true, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogOk := clipperTakeGenericDogNonzeroSuccess (v := v)
      hdog howe hlot hlotNe hdogCodeSolm hcallDogSolm'
    have htab' : (clipperTakeGenericDigsRet locals).get? "tab" =
        some (.int (Int.ofNat tabNew.toNat)) := by
      rw [clipperTakeGenericDigsRet, store_get_ne _ _ (by decide),
        clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), htab]
    have hlot' : (clipperTakeGenericDigsRet locals).get? "lot" =
        some (.int (Int.ofNat lotNew.toNat)) := by
      rw [clipperTakeGenericDigsRet, store_get_ne _ _ (by decide),
        clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hlot]
    have hid' : (clipperTakeGenericDigsRet locals).get? "id" =
        some (clipperTakeIdValue I) := by
      rw [clipperTakeGenericDigsRet, store_get_ne _ _ (by decide),
        clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hid]
    have hlocked' : (clipperTakeGenericDigsRet locals).get? "locked" = none := by
      rw [clipperTakeGenericDigsRet, store_get_ne _ _ (by decide),
        clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hlocked]
    have hsales' : (clipperTakeGenericDigsRet locals).get? "sales" = none := by
      rw [clipperTakeGenericDigsRet, store_get_ne _ _ (by decide),
        clipperTakeGenericMoveRet, store_get_ne _ _ (by decide), hsales]
    let evmTab := Solm.EVM.storageStore evmDog evmDog.executionEnv.codeOwner
      (clipperTakeSalesTabSlot I) tabNew
    let evmLot := Solm.EVM.storageStore evmTab evmTab.executionEnv.codeOwner
      (clipperTakeSalesLotSlot I) lotNew
    have hpost := clipperTakeGenericPostDogNonzeroStore
      (v := v) (evm := evmDog) htab' hlot' hid' hlocked' hsales' htabNe hlotNe
    have hafter : ExecBlock (config v)
        (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
        (clipperTakeAfterMoveStmts v)
        (.ok (Frame.mk (contract v) (clipperTakeGenericDigsRet locals))
          (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
      simpa [clipperTakeAfterMoveStmts, evmTab, evmLot] using
        execBlockAppendOk hdogOk hpost
    have htail : ExecBlock (config v) (Frame.mk (contract v) locals) evmCb
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v)
        (.ok (Frame.mk (contract v) (clipperTakeGenericDigsRet locals))
          (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) :=
      execBlockAppendOk hmove hafter
    obtain ⟨_, _, rd5025⟩ := RD.clipperTakePostDogLotNonzeroToCallbackGuard
      (v := v) (hpatch := hpatch) rd5003 hlotNe (by simp)
    let σFinal := sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σDog
          (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
        (solcMappingSlot ⟨12⟩ id + ⟨2⟩) lotNew) ⟨13⟩ ⟨0⟩
    let evmFinal := Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩
    have hret : RDret code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        σFinal ByteArray.empty := by
      simpa only [σFinal] using
        RD.clipperTakePostDogLotNonzeroTabNonzeroToReturnSuccessWF
          (v := v) (hpatch := hpatch) rd5025 htabNe hmemDog hperm
    have hownerDog : evmDog.executionEnv.codeOwner = I.codeOwner := by
      simpa [evmDogEvm, initState] using congrArg ExecutionEnv.codeOwner hevmDogEnv
    have hAccountsFinal : Eq σFinal evmFinal.accountMap := by
      simp only [σFinal, evmFinal, evmTab, evmLot, storageStore_accountMap,
        storageStore_executionEnv, hownerDog, clipperTakeSalesTabSlot,
        clipperTakeSalesLotSlot, clipperTakeSalesBaseSlot_eq, ← hidWord]
      change σDog = evmDog.accountMap at hAccountsDog
      rw [hAccountsDog]
    have hbody : ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned (Frame.mk (contract v) (clipperTakeGenericDigsRet locals))
          evmFinal none) := by
      simpa [evmFinal] using hsourceReturned htail
    have henc : returnEquiv ByteArray.empty none (takeTransition v).returnType := by
      simpa [takeTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          rfl rfl (by native_decide))
    exact RDret.reEquivExecutionGen
      hcode hret hdispatch hdec hbody hAccountsFinal henc

end Benchmarks.Dss.Clipper
