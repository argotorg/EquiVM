import Benchmarks.Dss.Clipper.TakeNonzeroFromFluxEquiv
import Benchmarks.Dss.Clipper.TakeGeneralContinuationEVM
import Benchmarks.Dss.Clipper.TakeGenericZeroSource
import Benchmarks.Dss.Clipper.TakeRemoveEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- A full-lot purchase calls `dog.digs` with the wrapped old tab plus the
   current owe, then removes the completed sale. -/
set_option maxHeartbeats 10000000 in
theorem clipperTakeLotZeroContinuationEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cACont : Batteries.RBSet AccountAddress compare} {σCont : AccountMap}
    {evmCont : EVM.State} {locals : Store}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd4701 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata (cACont, σCont) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccounts : accountMapEquiv σCont evmCont.accountMap)
    (hevmSigma0 : evmCont.σ₀ = σ₀)
    (hevmCreated : evmCont.createdAccounts = cACont)
    (hevmGenesis : evmCont.genesisBlockHeader = gh)
    (hevmBlocks : evmCont.blocks = bl)
    (hevmEnv : evmCont.executionEnv = I)
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
    (hlotZero : lotNew = ⟨0⟩)
    (hsourceReverted :
      ExecBlock (config v) (Frame.mk (contract v) locals) evmCont
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v) (Frame.mk (contract v) locals) evmCont
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm) →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned finalFrame finalEvm none))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmContEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σCont, createdAccounts := cACont }
  have hvowWord : clipperTakeVowTarget σCont I = clipperTakeVowEVMWord evmCont := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
    simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmEnv,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hslot]
  have hdogAddress : AccountAddress.ofNat dog.toNat =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask dog) := by
    rw [hdogClean, accountAddress_ofUInt256_eq_ofNat_toNat]
  have hmoveArgs := clipperEvalTakeGenericVatMoveArgs
    (v := v) (evm := evmCont) howe hvow
  have closeRevert
      (hrev : RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
      (htail : ExecBlock (config v) (Frame.mk (contract v) locals) evmCont
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted) :
      runtimeEquivalenceFor (config v) (contract v)
        cA gh bl σ_evm σ_solm σ₀ g A I :=
    hrev.reEquivExecutionRevert hcode hdispatch hdec (hsourceReverted htail)
  apply RD.clipperTakeGeneralContinuationElim v hpatch rd4701 hmem hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm : (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccounts (clipperTakeVatTargetAddress v).symm hnoCode
    exact closeRevert hrev
      (execBlockAppendReverted (clipperTakeGenericVatMoveNoCode hnoCodeSolm))
  · intro cAMove σMove outMove AMove hmoveCode hcallMove hrev
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove, createdAccounts := cAMove }
    obtain ⟨evmMove, hcallMoveSolm, _, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [evmContEvm, initState, hevmSigma0])
        (by simp [evmContEvm, hevmCreated])
        (by simp [evmContEvm, initState, hevmGenesis])
        (by simp [evmContEvm, initState, hevmBlocks])
        (by simp [evmContEvm, initState, hevmEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccounts (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (false, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    exact closeRevert hrev
      (execBlockAppendReverted
        (clipperTakeGenericVatMoveFailure hmoveArgs hmoveCodeSolm hcallMoveSolm'))
  · intro cAMove σMove outMove AMove _hlot hmoveCode hcallMove hdogNoCode hrev
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove, createdAccounts := cAMove }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [evmContEvm, initState, hevmSigma0])
        (by simp [evmContEvm, hevmCreated])
        (by simp [evmContEvm, initState, hevmGenesis])
        (by simp [evmContEvm, initState, hevmBlocks])
        (by simp [evmContEvm, initState, hevmEnv]) hcallMove
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccounts (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogNoCodeSolm : (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccountsMove rfl hdogNoCode
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogRev := clipperTakeGenericDogZeroNoCode (v := v)
      hdog htab howe hlot hlotZero hdogNoCodeSolm
    have hafter : ExecBlock (config v)
        (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
        (clipperTakeAfterMoveStmts v) .reverted := by
      simpa [clipperTakeAfterMoveStmts] using execBlockAppendReverted hdogRev
    exact closeRevert hrev (execBlockAppendOk hmove hafter)
  · intro cAMove σMove outMove AMove cADog σDog outDog ADog _hlot
      hmoveCode hcallMove hdogCode hcallDog hrev
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, createdAccounts := cAMove }
    let evmDogEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog, createdAccounts := cADog }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, hevmMoveSigma0,
        hevmMoveCreated, hevmMoveGenesis, hevmMoveBlocks, hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [evmContEvm, initState, hevmSigma0])
        (by simp [evmContEvm, hevmCreated])
        (by simp [evmContEvm, initState, hevmGenesis])
        (by simp [evmContEvm, initState, hevmBlocks])
        (by simp [evmContEvm, initState, hevmEnv]) hcallMove
    obtain ⟨evmDog, hcallDogSolm, _, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])
        (by simp [evmMoveEvm, hevmMoveCreated])
        (by simp [evmMoveEvm, initState, hevmMoveGenesis])
        (by simp [evmMoveEvm, initState, hevmMoveBlocks])
        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccounts (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsMove rfl hdogCode
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat (UInt256.add tabNew owe).toNat)]
        (false, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogRev := clipperTakeGenericDogZeroFailure (v := v)
      hdog htab howe hlot hlotZero hdogCodeSolm hcallDogSolm'
    have hafter : ExecBlock (config v)
        (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
        (clipperTakeAfterMoveStmts v) .reverted := by
      simpa [clipperTakeAfterMoveStmts] using execBlockAppendReverted hdogRev
    exact closeRevert hrev (execBlockAppendOk hmove hafter)
  · intro cAMove σMove outMove AMove cADog σDog outDog ADog kDog CDog _hlot
      hmoveCode hcallMove hdogCode hcallDog hmemDog rd5003
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, createdAccounts := cAMove }
    let evmDogEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog, createdAccounts := cADog }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, hevmMoveSigma0,
        hevmMoveCreated, hevmMoveGenesis, hevmMoveBlocks, hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccounts
        (by simp [evmContEvm, initState, hevmSigma0])
        (by simp [evmContEvm, hevmCreated])
        (by simp [evmContEvm, initState, hevmGenesis])
        (by simp [evmContEvm, initState, hevmBlocks])
        (by simp [evmContEvm, initState, hevmEnv]) hcallMove
    obtain ⟨evmDog, hcallDogSolm, hAccountsDog, hevmDogSigma0,
        hevmDogCreated, hevmDogGenesis, hevmDogBlocks, hevmDogEnv⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm) (evmSolm := evmMove)
        (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])
        (by simp [evmMoveEvm, hevmMoveCreated])
        (by simp [evmMoveEvm, initState, hevmMoveGenesis])
        (by simp [evmMoveEvm, initState, hevmMoveBlocks])
        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hmoveCodeSolm : 0 < (UInt256.ofNat
        ((evmCont.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccounts (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmCont
        (EVM.address v.vat) "move" 0
        [.address evmCont.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCont).toNat),
          .int (Int.ofNat owe.toNat)] (true, evmMove, outMove) true := by
      simpa [evmContEvm, evmMoveEvm, hevmEnv, hvowWord] using hcallMoveSolm
    have hdogCodeSolm : 0 < (UInt256.ofNat
        ((evmMove.lookupAccount (AccountAddress.ofNat dog.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount, hdogAddress] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsMove rfl hdogCode
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat dog.toNat)) "digs" 0
        [v.ilk, .int (Int.ofNat (UInt256.add tabNew owe).toNat)]
        (true, evmDog, outDog) true := by
      rw [← hdogAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv] using hcallDogSolm
    have hmove := clipperTakeGenericVatMoveSuccess hmoveArgs hmoveCodeSolm hcallMoveSolm'
    have hdogOk := clipperTakeGenericDogZeroSuccess (v := v)
      hdog htab howe hlot hlotZero hdogCodeSolm hcallDogSolm'
    have hlot' : (clipperTakeGenericDigsAmtRet locals tabNew owe).get? "lot" =
        some (.int 0) := by
      simpa [clipperTakeGenericDigsAmtRet, clipperTakeGenericDigsAmt,
        clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, hlotZero] using hlot
    have hid' : (clipperTakeGenericDigsAmtRet locals tabNew owe).get? "id" =
        some (clipperTakeIdValue I) := by
      simpa [clipperTakeGenericDigsAmtRet, clipperTakeGenericDigsAmt,
        clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hid
    have hlocked' : (clipperTakeGenericDigsAmtRet locals tabNew owe).get? "locked" =
        none := by
      simpa [clipperTakeGenericDigsAmtRet, clipperTakeGenericDigsAmt,
        clipperTakeGenericMoveRet, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hlocked
    obtain ⟨kRemove, CRemove, rd8274⟩ :=
      RD.clipperTakePostDogLotZeroToRemove v hpatch rd5003 hlotZero (by simp)
    apply clipperTakeRemoveEquiv v hpatch hcode hdispatch hdec rd8274
      (by simpa [clipperTakeIdWord, clipperYankArgWord] using hidWord) hmemDog hperm
      hAccountsDog hevmDogCreated hevmDogEnv
    · intro hremove
      have hpost := clipperTakeGenericPostDogLotZeroReverts hlot' hid' hremove
      have hafter : ExecBlock (config v)
          (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
          (clipperTakeAfterMoveStmts v) .reverted := by
        simpa [clipperTakeAfterMoveStmts] using
          execBlockAppendOk hdogOk hpost
      exact hsourceReverted (execBlockAppendOk hmove hafter)
    · intro callee evmRemove hremove
      let resultLocals :=
        (clipperTakeGenericDigsAmtRet locals tabNew owe).insert "_removeRet" .unit
      have hpost := clipperTakeGenericPostDogLotZeroOk hlot' hid' hlocked' hremove
      have hafter : ExecBlock (config v)
          (Frame.mk (contract v) (clipperTakeGenericMoveRet locals)) evmMove
          (clipperTakeAfterMoveStmts v)
          (.ok (Frame.mk (contract v) resultLocals)
            (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner
              ⟨13⟩ ⟨0⟩)) := by
        simpa [clipperTakeAfterMoveStmts, resultLocals] using
          execBlockAppendOk hdogOk hpost
      exact ⟨Frame.mk (contract v) resultLocals,
        hsourceReturned (execBlockAppendOk hmove hafter)⟩
  · intro _ _ _ _ hlotNe _ _ _ _
    exact (hlotNe hlotZero).elim
  · intro _ _ _ _ _ _ _ _ hlotNe _ _ _ _ _
    exact (hlotNe hlotZero).elim
  · intro _ _ _ _ _ _ _ _ _ _ hlotNe _ _ _ _ _ _
    exact (hlotNe hlotZero).elim

theorem clipperTakeLotZeroContinuation
    (v : ClipperImmutables) {code : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256}
    {slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt
      id sel : UInt256}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (hidWord : id = clipperTakeIdWord I)
    (hlotZero : lotNew = ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm σ_solm σ₀ A I g
      slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt
      id sel := by
  intro cACont σCont evmCont locals dog mem rdata aw k C rd4701 hmem hAccounts
    hevmSigma0 hevmCreated hevmGenesis hevmBlocks hevmEnv hdogClean howe htab hlot
    hdog _husr hid hlocked _hvowIgnored hsales hsourceReverted hsourceReturned
  exact clipperTakeLotZeroContinuationEquiv (locals := locals) v hpatch hcode
    hdispatch hdec rd4701 hmem hAccounts hevmSigma0 hevmCreated hevmGenesis
    hevmBlocks hevmEnv hdogClean howe htab hlot hdog hid hidWord hlocked
    _hvowIgnored hlotZero hsourceReverted hsourceReturned hdepth hperm

end Benchmarks.Dss.Clipper
