import Benchmarks.Dss.Clipper.TakeCallbackContinuationEquiv
import Benchmarks.Dss.Clipper.TakeCallbackSkipContinuationSource
import Benchmarks.Dss.Clipper.TakeContinuationEVM
import Benchmarks.Dss.Clipper.TakePostDogContinuationEVM
import Benchmarks.Dss.Clipper.TakeRemoveContinuationEVM
import Benchmarks.Dss.Clipper.YankSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000 in
theorem clipperTakeOweGtTabCallbackSkipSuccessContinuationEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost σVatEvm : AccountMap}
    {cAVat : Batteries.RBSet AccountAddress compare}
    {evmPrice evmVat : EVM.State} {outVat : ByteArray}
    {price tab lot : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hAccountsInitial : accountMapEquiv σ_evm σ_solm)
    (hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstoppedSolmLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrSolm :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd4701 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask ::
        tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
        clipperTakeSalesTicStackWord
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ::
        UInt256.land
          (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I
            (clipperTakeSalesPackedSlot I)) solcAddrMask ::
        ⟨3⟩ :: clipperTakeDataLenWord I ::
        (⟨32⟩ + (⟨4⟩ + clipperTakeDataOffsetWord I)) ::
        UInt256.land (clipperTakeWhoWord I) solcAddrMask ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        [⟨502⟩, clipperSelWord I])
      mem aw rdata (cAVat, σVatEvm) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccountsVat : accountMapEquiv σVatEvm evmVat.accountMap)
    (hevmVatSigma0 : evmVat.σ₀ = σ₀)
    (hevmVatCreated : evmVat.createdAccounts = cAVat)
    (hevmVatGenesis : evmVat.genesisBlockHeader = gh)
    (hevmVatBlocks : evmVat.blocks = bl)
    (hevmVatEnv : evmVat.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPrice I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPrice I)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCode : 0 < (UInt256.ofNat
      ((evmPrice.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat : typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmPrice.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
        .int (Int.ofNat
          (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
      (true, evmVat, outVat) true)
    (hcallback :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
      let slice := clipperMinWord
        (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I)
        (clipperTakeSalesTabEVMWord evmPrice I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPrice I) slice'
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLock evmPrice evmVat I price slice owe0 owe0
            slice' tabNew lotNew)) evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLock evmPrice evmVat I price slice owe0
              owe0 slice' tabNew lotNew)) evmVat))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v)
        { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v)
          (clipperTakeLocalsSt evmLock I false price)) evmPrice)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Solm.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
  let slice := clipperMinWord
    (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I)
    (clipperTakeSalesTabEVMWord evmPrice I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPrice I) slice'
  let cbFrame := Frame.mk (contract v)
    (clipperTakeLocalsDogLoaded evmLock evmPrice evmVat I price slice owe0 owe0
      slice' tabNew lotNew)
  have hAccountsLock : accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) evmLock.accountMap := by
    simpa [evmLock, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccountsInitial
  have hpackedWord :
      UInt256.land
          (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I
            (clipperTakeSalesPackedSlot I)) solcAddrMask =
        clipperTakeSalesUsrEVMWord evmLock I := by
    have hslot := accountMapEquiv_storage_findD hAccountsLock I.codeOwner
      (clipperTakeSalesPackedSlot I) ⟨0⟩
    simp [clipperTakeSalesUsrEVMWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, evmLock, evm0, initState,
      storageStore_executionEnv, hslot]
  have hsrcMul : slice.toNat * price.toNat < UInt256.size := by
    simpa [slice] using
      (clipperTakeOweGtTabSourceMul_of_post_lot
        (I := I) (evmPrice := evmPrice) (price := price) (lot := lot) hlot hmul)
  have hsrcGt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul slice price).toNat := by
    simpa [slice] using
      (clipperTakeOweGtTabSourceGt_of_post_words
        (I := I) (evmPrice := evmPrice) (price := price)
        (tab := tab) (lot := lot) htab hlot hgt)
  have hsrcSliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words
      (I := I) (evmPrice := evmPrice) (price := price)
      (tab := tab) (lot := lot) htab hlot hmul hgt
  have sourceReverted
      (htail : ExecBlock (config v) cbFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted) :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted := by
    have hafter := clipperTakeOweGtTabCallbackTailSource v evmLock evmPrice
      evmVat evmVat I price slice hsrcMul hsrcGt hsrcSliceLot hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using
        hcallback) htail
    exact clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlockedSolm hstoppedSolmLt husrSolm hmax hstatus
      (by simpa [evm0, evmLock, slice] using hafter)
  have sourceReturned {finalFrame : Frame} {finalEvm : EVM.State}
      (htail : ExecBlock (config v) cbFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm)) :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned finalFrame finalEvm none) := by
    have hafter := clipperTakeOweGtTabCallbackTailSource v evmLock evmPrice
      evmVat evmVat I price slice hsrcMul hsrcGt hsrcSliceLot hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using
        hcallback) htail
    exact clipperTakeSourceOkOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlockedSolm hstoppedSolmLt husrSolm hmax hstatus
      (by simpa [evm0, evmLock, slice] using hafter)
  have hlotNew : lot.sub (tab.div price) ≠ ⟨0⟩ := by
    have hmul' : price.toNat * slice.toNat < UInt256.size := by
      change price.toNat *
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
          (clipperTakeAmtWord I)).toNat < UInt256.size
      rw [← hlot, clipperMinWord_comm]
      exact hmul
    have hmulNat : (UInt256.mul price slice).toNat =
        price.toNat * slice.toNat := by
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hmul']
    have hgt' : tab.toNat < (UInt256.mul price slice).toNat := by
      change tab.toNat < (UInt256.mul price
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
          (clipperTakeAmtWord I))).toNat
      rw [← hlot, clipperMinWord_comm]
      exact hgt
    have hdivLtSlice : (tab.div price).toNat < slice.toNat := by
      rw [udiv_toNat]
      apply Nat.div_lt_of_lt_mul
      simpa [hmulNat, Nat.mul_comm] using hgt'
    have hsliceLeLot : slice.toNat ≤ lot.toNat := by
      change (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
        (clipperTakeAmtWord I)).toNat ≤ lot.toNat
      rw [← hlot, clipperMinWord_comm]
      exact clipperMinWord_le_right (clipperTakeAmtWord I) lot
    apply u256_sub_ne_zero_of_ne
    intro heq
    have hnat := congrArg UInt256.toNat heq
    omega
  have hdogWord : UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask =
      clipperTakeDogEVMWord evmVat := by
    exact clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat
      (by simpa [hevmPriceEnv] using
        (clipperTypedCallViaEVM_preservesBase hcallVat).2.2.2)
  have hdogTargetAddress :
      AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat =
        AccountAddress.ofUInt256
          (UInt256.land solcAddrMask
            (UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask)) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    have hclean :
        UInt256.land solcAddrMask
            (UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask) =
          UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask := by
      rw [u256_land_comm solcAddrMask
        (UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask)]
      exact solcAddrMask_clean
        (solcAddrMask_result_canonical (solcSlotWord σVatEvm I ⟨1⟩))
    exact congrArg AccountAddress.ofNat
      (congrArg UInt256.toNat (hdogWord.symm.trans hclean.symm))
  have closeRevert (hrev : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
      (htail : ExecBlock (config v) cbFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted) :
      runtimeEquivalenceFor (config v) (contract v)
        cA gh bl σ_evm σ_solm σ₀ g A I := by
    exact clipperTakeOweGtTabCallbackTailRevertEquivFromPostWords v
      hcode hwv hdispatch hdec hlockedSolm hstoppedSolmLt husrSolm
      htab hlot hrev hmax hmul hgt hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using hcallback)
      htail hstatus
  apply RD.clipperTakeOweGtTabContinuationElim v hpatch rd4701 hmem hlotNew
    hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm :
        (UInt256.ofNat
          ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccountsVat (clipperTakeVatTargetAddress v).symm hnoCode
    have hmove := clipperTakeVatMoveNoCodeBlockAtDogLoaded v
      evmLock evmPrice evmVat I price slice owe0 owe0 slice' tabNew lotNew
      hnoCodeSolm
    exact closeRevert hrev (by
      simpa [cbFrame] using execBlockAppendReverted hmove)
  · intro cAMove σMove outMove AMove hmoveCode hcallMove hrev
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVatEvm, createdAccounts := cAVat }
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove, createdAccounts := cAMove }
    obtain ⟨evmMove, hcallMoveSolm, _, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState hAccountsVat
        (by simp [evmVatEvm, initState, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, initState, hevmVatGenesis])
        (by simp [evmVatEvm, initState, hevmVatBlocks])
        (by simp [evmVatEvm, initState, hevmVatEnv]) hcallMove
    have hmoveCodeSolm :
        0 < (UInt256.ofNat
          ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (clipperTakeVatTargetAddress v).symm hmoveCode
    have hvow : clipperTakeVowTarget σVatEvm I =
        clipperTakeVowEVMWord evmVat := by
      have hslot := accountMapEquiv_storage_findD
        hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveBlock := clipperTakeVatMoveCallFailureBlockAtDogLoaded v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeSolm (by
        simpa [evmVatEvm, evmMoveEvm, hevmVatEnv, htab, hvow] using hcallMoveSolm)
    exact closeRevert hrev (by
      simpa [cbFrame] using execBlockAppendReverted hmoveBlock)
  · intro cAMove σMove outMove AMove hmoveCode hcallMove hdogNoCode hrev
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVatEvm, createdAccounts := cAVat }
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove, createdAccounts := cAMove }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, _, _, _, _, hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccountsVat
        (by simp [evmVatEvm, initState, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, initState, hevmVatGenesis])
        (by simp [evmVatEvm, initState, hevmVatBlocks])
        (by simp [evmVatEvm, initState, hevmVatEnv]) hcallMove
    have hvow : clipperTakeVowTarget σVatEvm I =
        clipperTakeVowEVMWord evmVat := by
      have hslot := accountMapEquiv_storage_findD
        hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeSolm :
        0 < (UInt256.ofNat
          ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmVat
        (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmVatEvm, evmMoveEvm, hevmVatEnv, htab, hvow] using hcallMoveSolm
    have hnoDogCodeSolm :
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccountsMove hdogTargetAddress hdogNoCode
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtDogLoaded v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeSolm hcallMoveSolm'
    have hdogBlock := clipperTakeDogDigsOweNoCodeBlock v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice' tabNew
      lotNew (by simpa [lotNew, htab, hlot] using hlotNew) hnoDogCodeSolm
    have htail : ExecBlock (config v) cbFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted := by
      simpa [cbFrame, clipperTakeAfterMoveStmts, List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendReverted hdogBlock)
    exact closeRevert hrev htail
  · intro cAMove σMove outMove AMove cADog σDog outDog ADog
      hmoveCode hcallMove hdogCode hcallDog hrev
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVatEvm, createdAccounts := cAVat }
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, createdAccounts := cAMove }
    let evmDogEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog, createdAccounts := cADog }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, hevmMoveSigma0,
        hevmMoveCreated, hevmMoveGenesis, hevmMoveBlocks, hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccountsVat
        (by simp [evmVatEvm, initState, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, initState, hevmVatGenesis])
        (by simp [evmVatEvm, initState, hevmVatBlocks])
        (by simp [evmVatEvm, initState, hevmVatEnv]) hcallMove
    have hvow : clipperTakeVowTarget σVatEvm I =
        clipperTakeVowEVMWord evmVat := by
      have hslot := accountMapEquiv_storage_findD
        hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeSolm :
        0 < (UInt256.ofNat
          ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmVat
        (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmVatEvm, evmMoveEvm, hevmVatEnv, htab, hvow] using hcallMoveSolm
    obtain ⟨evmDog, hcallDogSolm, _hAccountsDog, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm)
        (evmSolm := evmMove) (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])
        (by simp [evmMoveEvm, hevmMoveCreated])
        (by simp [evmMoveEvm, initState, hevmMoveGenesis])
        (by simp [evmMoveEvm, initState, hevmMoveBlocks])
        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hdogCodeSolm :
        0 < (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsMove hdogTargetAddress hdogCode
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat
          (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (false, evmDog, outDog) true := by
      rw [← hdogTargetAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv, htab] using hcallDogSolm
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtDogLoaded v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeSolm hcallMoveSolm'
    have hdogBlock := clipperTakeDogDigsOweCallFailureBlock v
      evmLock evmPrice evmVat evmMove evmDog I price slice owe0 owe0 slice'
      tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
      hdogCodeSolm hcallDogSolm'
    have htail : ExecBlock (config v) cbFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts v) .reverted := by
      simpa [cbFrame, clipperTakeAfterMoveStmts, List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendReverted hdogBlock)
    exact closeRevert hrev htail
  · intro cAMove σMove outMove AMove cADog σDog outDog ADog kDog CDog
      hmoveCode hcallMove hdogCode hcallDog hmemDog rd5003
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVatEvm, createdAccounts := cAVat }
    let evmMoveEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, createdAccounts := cAMove }
    let evmDogOutEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog, createdAccounts := cADog }
    obtain ⟨evmMove, hcallMoveSolm, hAccountsMove, hevmMoveSigma0,
        hevmMoveCreated, hevmMoveGenesis, hevmMoveBlocks, hevmMoveEnv⟩ :=
      clipperTypedCallSyncFromState hAccountsVat
        (by simp [evmVatEvm, initState, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, initState, hevmVatGenesis])
        (by simp [evmVatEvm, initState, hevmVatBlocks])
        (by simp [evmVatEvm, initState, hevmVatEnv]) hcallMove
    have hvow : clipperTakeVowTarget σVatEvm I =
        clipperTakeVowEVMWord evmVat := by
      have hslot := accountMapEquiv_storage_findD
        hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      simp [clipperTakeVowTarget, clipperTakeVowEVMWord, hevmVatEnv,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeSolm :
        0 < (UInt256.ofNat
          ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (clipperTakeVatTargetAddress v).symm hmoveCode
    have hcallMoveSolm' : typedCallViaEVM (config v) evmVat
        (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmVatEvm, evmMoveEvm, hevmVatEnv, htab, hvow] using hcallMoveSolm
    obtain ⟨evmDog, hcallDogSolm, hAccountsDog, hevmDogSigma0,
        hevmDogCreated, hevmDogGenesis, hevmDogBlocks, hevmDogEnv⟩ :=
      clipperTypedCallSyncFromState
        (cfg := config v) (evmEvm := evmMoveEvm)
        (evmSolm := evmMove) (evmEvm' := evmDogOutEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])
        (by simp [evmMoveEvm, hevmMoveCreated])
        (by simp [evmMoveEvm, initState, hevmMoveGenesis])
        (by simp [evmMoveEvm, initState, hevmMoveBlocks])
        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hdogCodeSolm :
        0 < (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsMove hdogTargetAddress hdogCode
    have hcallDogSolm' : typedCallViaEVM (config v) evmMove
        (EVM.address
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat
          (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmDog, outDog) true := by
      rw [← hdogTargetAddress] at hcallDogSolm
      simpa [evmMoveEvm, evmDogOutEvm, hevmMoveEnv, htab] using hcallDogSolm
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtDogLoaded v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeSolm hcallMoveSolm'
    have hdogBlock := clipperTakeDogDigsOweCallSuccessBlock v
      evmLock evmPrice evmVat evmMove evmDog I price slice owe0 owe0 slice'
      tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
      hdogCodeSolm hcallDogSolm'
    let postDogFrame := Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLock evmPrice evmVat I price slice owe0
        owe0 slice' tabNew lotNew)
    have tailOfPostDog {result : ExecResult}
        (hpostDog : ExecBlock (config v) postDogFrame evmDog
          (clipperTakePostDogStmts v) result) :
        ExecBlock (config v) cbFrame evmVat
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) result := by
      simpa [cbFrame, postDogFrame, clipperTakeAfterMoveStmts,
        List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendOk hdogBlock hpostDog)
    apply RD.clipperTakePostDogTabZeroContinuationElim v hpatch rd5003
      (by simpa [lotNew, htab, hlot] using hlotNew)
      (by exact u256_sub_self _) hmemDog hdepth hperm
    · intro hnoCode hrev
      have hnoCodeSolm :
          (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
            0 := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
            hAccountsDog (clipperTakeVatTargetAddress v).symm hnoCode
      have hpostDog := clipperTakePostDogTabZeroFluxNoCodeBlock
        v evmLock evmPrice evmVat evmDog I price slice owe0 owe0 slice' tabNew
        lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
        (by exact u256_sub_self _)
        hnoCodeSolm
      exact closeRevert hrev (tailOfPostDog (by simpa [postDogFrame] using hpostDog))
    · intro cAFlux σFlux outFlux AFlux hfluxCode hcallFlux hrev
      let evmDogEvm : EVM.State :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σDog, createdAccounts := cADog }
      let evmFluxEvm : EVM.State :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux, createdAccounts := cAFlux }
      obtain ⟨evmFlux, hcallFluxSolm, _, _, _, _, _, _⟩ :=
        clipperTypedCallSyncFromState
          (cfg := config v) (evmEvm := evmDogEvm)
          (evmSolm := evmDog) (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogSigma0)
          (by simpa [evmDogEvm, evmDogOutEvm] using hevmDogCreated)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogGenesis)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogBlocks)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogEnv) hcallFlux
      have hevmDogEnvI : evmDog.executionEnv = I := by
        simpa [evmDogOutEvm, initState] using hevmDogEnv
      have hfluxCodeSolm :
          0 < (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
            hAccountsDog (clipperTakeVatTargetAddress v).symm hfluxCode
      have hcallFluxSolm' : typedCallViaEVM (config v) evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (clipperTakeSalesUsrEVMWord evmLock I).toNat),
            .int (Int.ofNat lotNew.toNat)]
          (false, evmFlux, outFlux) true := by
        simpa [evmDogEvm, evmFluxEvm, hevmDogEnvI, hpackedWord, lotNew, htab,
          hlot] using hcallFluxSolm
      have hpostDog :=
        clipperTakePostDogTabZeroFluxCallFailureBlock v
          evmLock evmPrice evmVat evmDog evmFlux I price slice owe0 owe0 slice'
          tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
          (by exact u256_sub_self _) hfluxCodeSolm hcallFluxSolm'
      exact closeRevert hrev (tailOfPostDog (by simpa [postDogFrame] using hpostDog))
    · intro cAFlux σFlux outFlux AFlux kFlux CFlux hfluxCode hcallFlux hmemFlux
        rd8274
      let evmDogEvm : EVM.State :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σDog, createdAccounts := cADog }
      let evmFluxEvm : EVM.State :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux, createdAccounts := cAFlux }
      obtain ⟨evmFlux, hcallFluxSolm, hAccountsFlux, hevmFluxSigma0,
          hevmFluxCreated, hevmFluxGenesis, hevmFluxBlocks, hevmFluxEnv⟩ :=
        clipperTypedCallSyncFromState
          (cfg := config v) (evmEvm := evmDogEvm)
          (evmSolm := evmDog) (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogSigma0)
          (by simpa [evmDogEvm, evmDogOutEvm] using hevmDogCreated)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogGenesis)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogBlocks)
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogEnv) hcallFlux
      have hevmDogEnvI : evmDog.executionEnv = I := by
        simpa [evmDogOutEvm, initState] using hevmDogEnv
      have hevmFluxEnvI : evmFlux.executionEnv = I := by
        simpa [evmFluxEvm, initState] using hevmFluxEnv
      have hownerFlux : evmFlux.executionEnv.codeOwner = I.codeOwner := by
        rw [hevmFluxEnvI]
      have hfluxCodeSolm :
          0 < (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
            hAccountsDog (clipperTakeVatTargetAddress v).symm hfluxCode
      have hcallFluxSolm' : typedCallViaEVM (config v) evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (clipperTakeSalesUsrEVMWord evmLock I).toNat),
            .int (Int.ofNat lotNew.toNat)]
          (true, evmFlux, outFlux) true := by
        simpa [evmDogEvm, evmFluxEvm, hevmDogEnvI, hpackedWord, lotNew, htab,
          hlot] using hcallFluxSolm
      have hstorageFlux (slot : UInt256) :
          solcSlotWord σFlux I slot =
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner slot := by
        have hslot := accountMapEquiv_storage_findD hAccountsFlux I.codeOwner slot ⟨0⟩
        simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, hevmFluxEnvI, evmFluxEvm, hslot]
      have postDogReverted
          (hremove : ExecFuncBody (config v)
            { contract := contract v, locals := clipperYankRemoveStore I }
            evmFlux removeFunction.body .reverted) :
          ExecBlock (config v) postDogFrame evmDog
            (clipperTakePostDogStmts v) .reverted := by
        simpa [postDogFrame] using
          clipperTakePostDogTabZeroFluxRemoveSourceRevertsOfBody
            v evmLock evmPrice evmVat evmDog evmFlux I price slice owe0 owe0
            slice' tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeSolm hcallFluxSolm' hremove
      apply RD.clipperTakeRemoveContinuationElim v hpatch rd8274
        (by simp [clipperTakeIdWord, clipperYankArgWord]) hmemFlux hperm
      · intro hlen hinvalid
        have hlenSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
          rw [← hstorageFlux]
          exact hlen
        have hremove := clipperYankRemoveEmptySourceReverts v evmFlux I hlenSolm
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))
      · intro hlen hidEq hret
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        have hlenSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [clipperYankLenAddLnotZero_eq_subOne, hstorageFlux]
        have hidEqSolm : clipperYankArgWord I =
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidEq
        have haccFlux : ∃ acc, evmFlux.accountMap.find?
            evmFlux.executionEnv.codeOwner = some acc := by
          cases hfind : evmFlux.accountMap.find? evmFlux.executionEnv.codeOwner with
          | none =>
              exfalso
              apply hlenSolm
              simp [Solm.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
          | some acc => exact ⟨acc, rfl⟩
        obtain ⟨accFlux, haccFlux⟩ := haccFlux
        let sourceLastIndex := UInt256.sub
          (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
        let evmRemove := clipperYankDeleteSaleState
          (clipperYankRemovePopState evmFlux sourceLastIndex) I
        let calleeFrame : Frame :=
          { contract := contract v,
            locals := clipperYankRemoveMoveStore I sourceLastIndex
              (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot sourceLastIndex)) }
        have hremove : ExecFuncBody (config v)
            { contract := contract v, locals := clipperYankRemoveStore I }
            evmFlux removeFunction.body (.returned calleeFrame evmRemove none) := by
          simpa [sourceLastIndex, evmRemove, calleeFrame] using
            clipperYankRemoveIdEqMoveSource v evmFlux I haccFlux hlenSolm hidEqSolm
        have hpostDog :=
          clipperTakePostDogTabZeroFluxRemoveSourceOkOfBody v
            evmLock evmPrice evmVat evmDog evmFlux evmRemove I price slice owe0
            owe0 slice' tabNew lotNew
            (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeSolm hcallFluxSolm' hremove
        have hAccountsFinal :=
          clipperYankSuccessAccountMap_state_accountMapEquiv
            (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I lastIndex
            hAccountsFlux rfl hownerFlux
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdec
          (sourceReturned (tailOfPostDog (by
            simpa [postDogFrame] using hpostDog)))
          (by
            simp [evmRemove, sourceLastIndex, clipperYankDeleteSaleState,
              clipperYankRemovePopState, storageStore_createdAccounts,
              hevmFluxCreated, evmFluxEvm])
          (by
            simpa [lastIndex, sourceLastIndex, hlastIndexEq, evmRemove,
              clipperYankSuccessAccountMap] using hAccountsFinal)
          (by
            simpa [takeTransition] using
              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                rfl rfl (by native_decide)))
      · intro hlen hidNe hidxBound hlenAfter hinvalid
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        let move := solcSlotWord σFlux I (clipperYankActiveSlot lastIndex)
        let idx := solcSlotWord σFlux I (clipperYankSalesPosSlot I)
        let evmIndex := Solm.EVM.storageStore evmFlux
          evmFlux.executionEnv.codeOwner (clipperYankActiveSlot idx) move
        let evmMovePos := Solm.EVM.storageStore evmIndex
          evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
        have hlenSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [clipperYankLenAddLnotZero_eq_subOne, hstorageFlux]
        have hidNeSolm : clipperYankArgWord I ≠
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidNe
        have hidxBoundSolm :
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankSalesPosSlot I)).toNat <
              (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat := by
          rw [← hstorageFlux, ← hstorageFlux]
          simpa [idx] using hidxBound
        have hmoveSolm :
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot
                  (UInt256.sub
                    (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                    ⟨1⟩)) = move := by
          rw [← hlastIndexEq, ← hstorageFlux]
        have hidxSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
          rw [← hstorageFlux]
        have hmoveAccounts : accountMapEquiv
            (clipperYankMoveAccountMap σFlux I idx move) evmMovePos.accountMap := by
          simpa [evmIndex, evmMovePos] using
            clipperYankMoveAccountMap_state_accountMapEquiv
              (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I idx move
              hAccountsFlux rfl hownerFlux
        have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
          simp [evmMovePos, evmIndex, storageStore_executionEnv, hownerFlux]
        have hstorageMove (slot : UInt256) :
            solcSlotWord (clipperYankMoveAccountMap σFlux I idx move) I slot =
              Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
          have hslot := accountMapEquiv_storage_findD hmoveAccounts I.codeOwner slot ⟨0⟩
          simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            solcSlotWord, hownerMovePos, hslot]
        have hlenAfterSolm : Solm.EVM.storageLoad evmMovePos
            evmMovePos.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
          rw [← hstorageMove]
          simpa [lastIndex, move, idx] using hlenAfter
        have hremoveRaw := clipperYankRemoveIdNeMovePopEmptySourceReverts
          v evmFlux I hlenSolm hidNeSolm hidxBoundSolm
        dsimp only at hremoveRaw
        have hremove := hremoveRaw (by
          simpa only [hmoveSolm, hidxSolm, evmIndex, evmMovePos] using hlenAfterSolm)
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))
      · intro hlen hidNe hidxBound hlenAfter hret
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        let move := solcSlotWord σFlux I (clipperYankActiveSlot lastIndex)
        let idx := solcSlotWord σFlux I (clipperYankSalesPosSlot I)
        let σMove := clipperYankMoveAccountMap σFlux I idx move
        let evmIndex := Solm.EVM.storageStore evmFlux
          evmFlux.executionEnv.codeOwner (clipperYankActiveSlot idx) move
        let evmMovePos := Solm.EVM.storageStore evmIndex
          evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
        have hlenSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [clipperYankLenAddLnotZero_eq_subOne, hstorageFlux]
        have hmoveSolm :
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot
                  (UInt256.sub
                    (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                    ⟨1⟩)) = move := by
          rw [← hlastIndexEq, ← hstorageFlux]
        have hidxSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
          rw [← hstorageFlux]
        have hidNeSolm : clipperYankArgWord I ≠
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [hmoveSolm]
          simpa [lastIndex, move] using hidNe
        have hidxBoundSolm :
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankSalesPosSlot I)).toNat <
              (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat := by
          rw [hidxSolm, ← hstorageFlux]
          simpa [idx] using hidxBound
        have hmoveAccounts : accountMapEquiv σMove evmMovePos.accountMap := by
          simpa [σMove, evmIndex, evmMovePos] using
            clipperYankMoveAccountMap_state_accountMapEquiv
              (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I idx move
              hAccountsFlux rfl hownerFlux
        have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
          simp [evmMovePos, evmIndex, storageStore_executionEnv, hownerFlux]
        have hstorageMove (slot : UInt256) :
            solcSlotWord σMove I slot =
              Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
          have hslot := accountMapEquiv_storage_findD hmoveAccounts I.codeOwner slot ⟨0⟩
          simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            solcSlotWord, hownerMovePos, σMove, hslot]
        have hlenAfterSolm : Solm.EVM.storageLoad evmMovePos
            evmMovePos.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          apply hlenAfter
          simpa [lastIndex, move, idx, σMove] using
            (show solcSlotWord σMove I ⟨11⟩ = ⟨0⟩ by
              rw [hstorageMove]
              exact hzero)
        have haccFlux : ∃ acc, evmFlux.accountMap.find?
            evmFlux.executionEnv.codeOwner = some acc := by
          cases hfind : evmFlux.accountMap.find? evmFlux.executionEnv.codeOwner with
          | none =>
              exfalso
              apply hlenSolm
              simp [Solm.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
          | some acc => exact ⟨acc, rfl⟩
        obtain ⟨accFlux, haccFlux⟩ := haccFlux
        let popLastIndex := UInt256.sub
          (Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
        let evmRemove := clipperYankDeleteSaleState
          (clipperYankRemovePopState evmMovePos popLastIndex) I
        let calleeFrame : Frame :=
          { contract := contract v,
            locals := clipperYankRemoveIndexStore I
              (UInt256.sub
                (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)
              move idx }
        have hremoveRaw := clipperYankRemoveIdNeMoveSource
          v evmFlux I haccFlux hlenSolm hidNeSolm hidxBoundSolm
        dsimp only at hremoveRaw
        have hremove : ExecFuncBody (config v)
            { contract := contract v, locals := clipperYankRemoveStore I }
            evmFlux removeFunction.body (.returned calleeFrame evmRemove none) := by
          have hremoveSource := hremoveRaw (by
            simpa only [hmoveSolm, hidxSolm, evmIndex, evmMovePos] using hlenAfterSolm)
          simpa only [calleeFrame, evmRemove, popLastIndex, hmoveSolm, hidxSolm,
            evmIndex, evmMovePos] using hremoveSource
        have hpostDog :=
          clipperTakePostDogTabZeroFluxRemoveSourceOkOfBody v
            evmLock evmPrice evmVat evmDog evmFlux evmRemove I price slice owe0
            owe0 slice' tabNew lotNew
            (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeSolm hcallFluxSolm' hremove
        let lastIndexAfter := solcSlotWord σMove I ⟨11⟩ + UInt256.lnot ⟨0⟩
        have hlastIndexAfterEq : lastIndexAfter = popLastIndex := by
          rw [show lastIndexAfter = solcSlotWord σMove I ⟨11⟩ +
            UInt256.lnot ⟨0⟩ from rfl]
          rw [clipperYankLenAddLnotZero_eq_subOne, hstorageMove]
        have hAccountsFinal :=
          clipperYankSuccessAccountMap_state_accountMapEquiv
            (σ := σMove) (τ := evmMovePos.accountMap) evmMovePos I lastIndexAfter
            hmoveAccounts rfl hownerMovePos
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdec
          (sourceReturned (tailOfPostDog (by
            simpa [postDogFrame] using hpostDog)))
          (by
            simp [evmRemove, popLastIndex, evmMovePos, evmIndex,
              clipperYankDeleteSaleState, clipperYankRemovePopState,
              storageStore_createdAccounts, hevmFluxCreated, evmFluxEvm])
          (by
            simpa [lastIndex, move, idx, σMove, lastIndexAfter,
              hlastIndexAfterEq, evmRemove, popLastIndex,
              clipperYankSuccessAccountMap] using hAccountsFinal)
          (by
            simpa [takeTransition] using
              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                rfl rfl (by native_decide)))
      · intro hlen hidNe hidxBound hinvalid
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        have hlenSolm : Solm.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [clipperYankLenAddLnotZero_eq_subOne, hstorageFlux]
        have hidNeSolm : clipperYankArgWord I ≠
            Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidNe
        have hidxBoundSolm :
            (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat ≤
              (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankSalesPosSlot I)).toNat := by
          rw [← hstorageFlux, ← hstorageFlux]
          simpa using hidxBound
        have hremove := clipperYankRemoveIdNeMoveIndexOobSourceReverts
          v evmFlux I hlenSolm hidNeSolm hidxBoundSolm
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))


end Benchmarks.Dss.Clipper
