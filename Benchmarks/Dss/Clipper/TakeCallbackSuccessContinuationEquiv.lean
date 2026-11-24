import Benchmarks.Dss.Clipper.TakeCallbackContinuationEquiv
import Benchmarks.Dss.Clipper.TakeContinuationEVM
import Benchmarks.Dss.Clipper.TakePostDogContinuationEVM
import Benchmarks.Dss.Clipper.TakeRemoveContinuationEVM
import Benchmarks.Dss.Clipper.YankSuccessSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000 in
theorem clipperTakeOweGtTabCallbackSuccessContinuationEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σVatEvm σCbEvm : AccountMap}
    {evmPrice evmVat evmCb : EVM.State} {outVat outCb : ByteArray}
    {price tab lot : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd4701 : RD fork code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (UInt256.land (solcSlotWord σVatEvm I ⟨1⟩) solcAddrMask ::
        tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
        clipperTakeSalesTicStackWord
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ::
        UInt256.land
          (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I
            (clipperTakeSalesPackedSlot I)) solcAddrMask ::
        ⟨3⟩ :: clipperTakeDataLenWord I ::
        (⟨32⟩ + (⟨4⟩ + clipperTakeDataOffsetWord I)) ::
        UInt256.land (clipperTakeWhoWord I) solcAddrMask ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        [⟨502⟩, clipperSelWord I])
      mem aw rdata σCbEvm k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccountsVat : Eq σVatEvm evmVat.accountMap)
    (hAccountsCb : Eq σCbEvm evmCb.accountMap)
    (hevmCbSigma0 : evmCb.σ₀ = σ₀)
    (hevmCbEnv : evmCb.executionEnv = I)
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
    (hcallVat : typedCallViaEVM fork config evmPrice (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmPrice.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
        .int (Int.ofNat
          (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
      (true, evmVat, outVat) true)
    (hcallback :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
      let slice := clipperMinWord
        (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
      let owe0 := UInt256.mul slice price
      let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price
      let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I)
        (clipperTakeSalesTabEVMWord evmPrice I)
      let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPrice I) slice'
      ExecStmt fork config
        (Frame.mk contract (clipperTakeLocalsDogLoaded evmLock evmPrice evmVat I price slice owe0 owe0
            slice' tabNew lotNew) (immStore v)) evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") vatExpr)
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") [])
        (.ok
          (Frame.mk contract (clipperTakeLocalsCallbackRet evmLock evmPrice evmVat I price slice owe0
              owe0 slice' tabNew lotNew) (immStore v)) evmCb))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk contract (clipperTakeLocalsSt evmLock I false price) (immStore v)) evmPrice)) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Stele.EVM.storageStore evm0 I.codeOwner ⟨13⟩ ⟨1⟩
  let slice := clipperMinWord
    (clipperTakeSalesLotEVMWord evmPrice I) (clipperTakeAmtWord I)
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmPrice I)
    (clipperTakeSalesTabEVMWord evmPrice I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmPrice I) slice'
  let cbFrame := Frame.mk contract (clipperTakeLocalsCallbackRet evmLock evmPrice evmVat I price slice owe0 owe0
      slice' tabNew lotNew) (immStore v)
  have hAccountsLock : Eq
      (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) evmLock.accountMap := by
    simp [evmLock, evm0, initState, storageStore_accountMap]
  have hpackedWord :
      UInt256.land
          (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I
            (clipperTakeSalesPackedSlot I)) solcAddrMask =
        clipperTakeSalesUsrEVMWord evmLock I := by
    have hslot := congrArg (fun m => solcSlotWord m I (clipperTakeSalesPackedSlot I)) hAccountsLock
    simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeSalesUsrEVMWord, Stele.EVM.storageLoad, State.lookupAccount,
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
      (htail : ExecBlock fork config cbFrame evmCb
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted) :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v) := by
    have hafter := clipperTakeOweGtTabCallbackTailSource v evmLock evmPrice
      evmVat evmCb I price slice hsrcMul hsrcGt hsrcSliceLot hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using
        hcallback) htail
    exact clipperTakeSourceRevertsOfAfterSlice (hperm := by assumption)
      (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlockedStele hstoppedSteleLt husrStele hmax hstatus
      (by simpa [evm0, evmLock, slice] using hafter)
  have sourceReturned {finalFrame : Frame} {finalEvm : EVM.State}
      (htail : ExecBlock fork config cbFrame evmCb
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) (.ok finalFrame finalEvm)) :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body
        (.returned finalFrame finalEvm none) (immStore v) := by
    have hafter := clipperTakeOweGtTabCallbackTailSource v evmLock evmPrice
      evmVat evmCb I price slice hsrcMul hsrcGt hsrcSliceLot hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using
        hcallback) htail
    exact clipperTakeSourceOkOfAfterSlice (hperm := by assumption)
      (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlockedStele hstoppedSteleLt husrStele hmax hstatus
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
    exact clipperTakeDogWord_eq hAccountsVat
      (by simpa [hevmPriceEnv] using
        (typedCallViaEVM_preservesBase hcallVat).2)
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
  have closeRevert (hrev : RDrev fork code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      (htail : ExecBlock fork config cbFrame evmCb
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted) :
      runtimeRefinementFor fork config contract
        σ σ₀ g A I (immStore v) := by
    exact clipperTakeOweGtTabCallbackTailRevertEquivFromPostWords (hperm := by assumption) v
      hcode hwv hdispatch hdec hlockedStele hstoppedSteleLt husrStele
      htab hlot hrev hmax hmul hgt hvatCode hcallVat
      (by simpa [evm0, evmLock, slice, owe0, slice', tabNew, lotNew, cbFrame] using hcallback)
      htail hstatus
  apply RD.clipperTakeOweGtTabContinuationElim v hpatch rd4701 hmem hlotNew
    hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeStele :
        (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_zero_lookup_code_zero
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hnoCode)
    have hmove := clipperTakeVatMoveNoCodeBlockAtCallbackRet (fork := fork) v
      evmLock evmPrice evmVat evmCb I price slice owe0 owe0 slice' tabNew lotNew
      hnoCodeStele
    exact closeRevert hrev (by
      simpa [cbFrame] using execBlockAppendReverted hmove)
  · intro σMove outMove AMove hmoveCode hcallMove hrev
    let evmCbEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCbEvm }
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove }
    obtain ⟨evmMove,
      hcallMoveStele,
      _,
      _,
      _⟩ :=
      typedCallViaEVM_syncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hmoveCodeStele :
        0 < (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hvow : clipperTakeVowTarget σCbEvm I =
        clipperTakeVowEVMWord evmCb := by
      have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsCb
      simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmCbEnv,
        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveBlock := clipperTakeVatMoveCallFailureBlockAtCallbackRet v
      evmLock evmPrice evmVat evmCb evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeStele (by
        simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, htab, hvow] using hcallMoveStele)
    exact closeRevert hrev (by
      simpa [cbFrame] using execBlockAppendReverted hmoveBlock)
  · intro σMove outMove AMove hmoveCode hcallMove hdogNoCode hrev
    let evmCbEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCbEvm }
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove, substate := AMove }
    obtain ⟨evmMove,
      hcallMoveStele,
      hAccountsMove,
      _,
      hevmMoveEnv⟩ :=
      typedCallViaEVM_syncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hvow : clipperTakeVowTarget σCbEvm I =
        clipperTakeVowEVMWord evmCb := by
      have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsCb
      simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmCbEnv,
        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeStele :
        0 < (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveStele' : typedCallViaEVM fork config evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, htab, hvow] using hcallMoveStele
    have hnoDogCodeStele :
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_zero_lookup_code_zero
          hdogTargetAddress
          (by simpa only [← hAccountsMove] using hdogNoCode)
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtCallbackRet v
      evmLock evmPrice evmVat evmCb evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeStele hcallMoveStele'
    have hdogBlock := clipperTakeDogDigsOweNoCodeBlockAtCallbackMoveRet (fork := fork) v
      evmLock evmPrice evmVat evmMove I price slice owe0 owe0 slice' tabNew
      lotNew (by simpa [lotNew, htab, hlot] using hlotNew) hnoDogCodeStele
    have htail : ExecBlock fork config cbFrame evmCb
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted := by
      simpa [cbFrame, clipperTakeAfterMoveStmts, List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendReverted hdogBlock)
    exact closeRevert hrev htail
  · intro σMove outMove AMove σDog outDog ADog
      hmoveCode hcallMove hdogCode hcallDog hrev
    let evmCbEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCbEvm }
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove }
    let evmDogEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog }
    obtain ⟨evmMove,
      hcallMoveStele,
      hAccountsMove,
      hevmMoveSigma0,
      hevmMoveEnv⟩ :=
      typedCallViaEVM_syncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hvow : clipperTakeVowTarget σCbEvm I =
        clipperTakeVowEVMWord evmCb := by
      have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsCb
      simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmCbEnv,
        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeStele :
        0 < (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveStele' : typedCallViaEVM fork config evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, htab, hvow] using hcallMoveStele
    obtain ⟨evmDog,
      hcallDogStele,
      _hAccountsDog,
      _,
      _⟩ :=
      typedCallViaEVM_syncFromState
        (cfg := config) (evmEvm := evmMoveEvm)
        (evmStele := evmMove) (evmEvm' := evmDogEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hdogCodeStele :
        0 < (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          hdogTargetAddress
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogStele' : typedCallViaEVM fork config evmMove
        (EVM.address
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat
          (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (false, evmDog, outDog) true := by
      rw [← hdogTargetAddress] at hcallDogStele
      simpa [evmMoveEvm, evmDogEvm, hevmMoveEnv, htab] using hcallDogStele
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtCallbackRet v
      evmLock evmPrice evmVat evmCb evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeStele hcallMoveStele'
    have hdogBlock := clipperTakeDogDigsOweCallFailureBlockAtCallbackMoveRet v
      evmLock evmPrice evmVat evmMove evmDog I price slice owe0 owe0 slice'
      tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
      hdogCodeStele hcallDogStele'
    have htail : ExecBlock fork config cbFrame evmCb
        (checkedExternalCallStmts vatExpr "move" (.intLit 0)
            [sender, .storage vowRef, .var "owe"] "_moveRet" ++
          clipperTakeAfterMoveStmts) .reverted := by
      simpa [cbFrame, clipperTakeAfterMoveStmts, List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendReverted hdogBlock)
    exact closeRevert hrev htail
  · intro σMove outMove AMove σDog outDog ADog kDog CDog
      hmoveCode hcallMove hdogCode hcallDog hmemDog rd5003
    let evmCbEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCbEvm }
    let evmMoveEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σMove }
    let evmDogOutEvm : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σDog, substate := ADog }
    obtain ⟨evmMove,
      hcallMoveStele,
      hAccountsMove,
      hevmMoveSigma0,
      hevmMoveEnv⟩ :=
      typedCallViaEVM_syncFromState hAccountsCb
        (by simp [evmCbEvm, initState, hevmCbSigma0])



        (by simp [evmCbEvm, initState, hevmCbEnv]) hcallMove
    have hvow : clipperTakeVowTarget σCbEvm I =
        clipperTakeVowEVMWord evmCb := by
      have hslot := congrArg (fun m => solcSlotWord m I ⟨2⟩) hAccountsCb
      simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperTakeVowTarget, clipperTakeVowEVMWord, hevmCbEnv,
        Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hslot]
    have hmoveCodeStele :
        0 < (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          (clipperTakeVatTargetAddress v).symm
          (by simpa only [← hAccountsCb] using hmoveCode)
    have hcallMoveStele' : typedCallViaEVM fork config evmCb
        (EVM.address v.vat) "move" 0
        [.address evmCb.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmMove, outMove) true := by
      simpa [evmCbEvm, evmMoveEvm, hevmCbEnv, htab, hvow] using hcallMoveStele
    obtain ⟨evmDog,
      hcallDogStele,
      hAccountsDog,
      hevmDogSigma0,
      hevmDogEnv⟩ :=
      typedCallViaEVM_syncFromState
        (cfg := config) (evmEvm := evmMoveEvm)
        (evmStele := evmMove) (evmEvm' := evmDogOutEvm) hAccountsMove
        (by simp [evmMoveEvm, initState, hevmMoveSigma0])



        (by simp [evmMoveEvm, initState, hevmMoveEnv]) hcallDog
    have hdogCodeStele :
        0 < (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_ne_zero_lookup_code_pos
          hdogTargetAddress
          (by simpa only [← hAccountsMove] using hdogCode)
    have hcallDogStele' : typedCallViaEVM fork config evmMove
        (EVM.address
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0
        [v.ilk, .int (Int.ofNat
          (clipperTakeSalesTabEVMWord evmPrice I).toNat)]
        (true, evmDog, outDog) true := by
      rw [← hdogTargetAddress] at hcallDogStele
      simpa [evmMoveEvm, evmDogOutEvm, hevmMoveEnv, htab] using hcallDogStele
    have hmoveBlock := clipperTakeVatMoveCallSuccessBlockAtCallbackRet v
      evmLock evmPrice evmVat evmCb evmMove I price slice owe0 owe0 slice'
      tabNew lotNew hmoveCodeStele hcallMoveStele'
    have hdogBlock := clipperTakeDogDigsOweCallSuccessBlockAtCallbackMoveRet v
      evmLock evmPrice evmVat evmMove evmDog I price slice owe0 owe0 slice'
      tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
      hdogCodeStele hcallDogStele'
    let postDogFrame := Frame.mk contract (clipperTakeLocalsCallbackDigsRet evmLock evmPrice evmVat I price slice owe0
        owe0 slice' tabNew lotNew) (immStore v)
    have tailOfPostDog {result : ExecResult}
        (hpostDog : ExecBlock fork config postDogFrame evmDog
          (clipperTakePostDogStmts) result) :
        ExecBlock fork config cbFrame evmCb
          (checkedExternalCallStmts vatExpr "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts) result := by
      simpa [cbFrame, postDogFrame, clipperTakeAfterMoveStmts,
        List.append_assoc] using
        execBlockAppendOk hmoveBlock (execBlockAppendOk hdogBlock hpostDog)
    apply RD.clipperTakePostDogTabZeroContinuationElim v hpatch rd5003
      (by simpa [lotNew, htab, hlot] using hlotNew)
      (by exact u256_sub_self _) hmemDog hdepth hperm
    · intro hnoCode hrev
      have hnoCodeStele :
          (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
            0 := by
        simpa [State.lookupAccount] using
          extCodeSizeWord_zero_lookup_code_zero
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hnoCode)
      have hpostDog := clipperTakePostDogTabZeroFluxNoCodeBlockAtCallbackDigsRet (fork := fork)
        v evmLock evmPrice evmVat evmDog I price slice owe0 owe0 slice' tabNew
        lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
        (by exact u256_sub_self _)
        hnoCodeStele
      exact closeRevert hrev (tailOfPostDog (by simpa [postDogFrame] using hpostDog))
    · intro σFlux outFlux AFlux hfluxCode hcallFlux hrev
      let evmDogEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σDog }
      let evmFluxEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux }
      obtain ⟨evmFlux,
      hcallFluxStele,
      _,
      _,
      _⟩ :=
        typedCallViaEVM_syncFromState
          (cfg := config) (evmEvm := evmDogEvm)
          (evmStele := evmDog) (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogSigma0)



          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogEnv) hcallFlux
      have hevmDogEnvI : evmDog.executionEnv = I := by
        simpa [evmDogOutEvm, initState] using hevmDogEnv
      have hfluxCodeStele :
          0 < (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          extCodeSizeWord_ne_zero_lookup_code_pos
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hfluxCode)
      have hcallFluxStele' : typedCallViaEVM fork config evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (clipperTakeSalesUsrEVMWord evmLock I).toNat),
            .int (Int.ofNat lotNew.toNat)]
          (false, evmFlux, outFlux) true := by
        simpa [evmDogEvm, evmFluxEvm, hevmDogEnvI, hpackedWord, lotNew, htab,
          hlot] using hcallFluxStele
      have hpostDog :=
        clipperTakePostDogTabZeroFluxCallFailureBlockAtCallbackDigsRet v
          evmLock evmPrice evmVat evmDog evmFlux I price slice owe0 owe0 slice'
          tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
          (by exact u256_sub_self _) hfluxCodeStele hcallFluxStele'
      exact closeRevert hrev (tailOfPostDog (by simpa [postDogFrame] using hpostDog))
    · intro σFlux outFlux AFlux kFlux CFlux hfluxCode hcallFlux hmemFlux
        rd8274
      let evmDogEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σDog }
      let evmFluxEvm : EVM.State :=
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σFlux, substate := AFlux }
      obtain ⟨evmFlux,
      hcallFluxStele,
      hAccountsFlux,
      hevmFluxSigma0,
      hevmFluxEnv⟩ :=
        typedCallViaEVM_syncFromState
          (cfg := config) (evmEvm := evmDogEvm)
          (evmStele := evmDog) (evmEvm' := evmFluxEvm) hAccountsDog
          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogSigma0)



          (by simpa [evmDogEvm, evmDogOutEvm, initState] using hevmDogEnv) hcallFlux
      have hevmDogEnvI : evmDog.executionEnv = I := by
        simpa [evmDogOutEvm, initState] using hevmDogEnv
      have hevmFluxEnvI : evmFlux.executionEnv = I := by
        simpa [evmFluxEvm, initState] using hevmFluxEnv
      have hownerFlux : evmFlux.executionEnv.codeOwner = I.codeOwner := by
        rw [hevmFluxEnvI]
      have hfluxCodeStele :
          0 < (UInt256.ofNat
            ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat := by
        simpa [State.lookupAccount] using
          extCodeSizeWord_ne_zero_lookup_code_pos
            (clipperTakeVatTargetAddress v).symm
            (by simpa only [← hAccountsDog] using hfluxCode)
      have hcallFluxStele' : typedCallViaEVM fork config evmDog
          (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (clipperTakeSalesUsrEVMWord evmLock I).toNat),
            .int (Int.ofNat lotNew.toNat)]
          (true, evmFlux, outFlux) true := by
        simpa [evmDogEvm, evmFluxEvm, hevmDogEnvI, hpackedWord, lotNew, htab,
          hlot] using hcallFluxStele
      have hstorageFlux (slot : UInt256) :
          solcSlotWord σFlux I slot =
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner slot := by
        have hslot := congrArg (fun m => solcSlotWord m I slot) hAccountsFlux
        simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, hevmFluxEnvI, evmFluxEvm, hslot]
      have postDogReverted
          (hremove : ExecFuncBody fork config
            { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
            evmFlux removeFunction.body .reverted) :
          ExecBlock fork config postDogFrame evmDog
            (clipperTakePostDogStmts) .reverted := by
        simpa [postDogFrame] using
          clipperTakePostDogTabZeroFluxRemoveSourceRevertsAtCallbackDigsRet
            v evmLock evmPrice evmVat evmDog evmFlux I price slice owe0 owe0
            slice' tabNew lotNew (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeStele hcallFluxStele' hremove
      apply RD.clipperTakeRemoveContinuationElim v hpatch rd8274
        (by simp [clipperTakeIdWord, clipperYankArgWord]) hmemFlux hperm
      · intro hlen hinvalid
        have hlenStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
          rw [← hstorageFlux]
          exact hlen
        have hremove := clipperYankRemoveEmptySourceReverts (fork := fork) v evmFlux I hlenStele
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))
      · intro hlen hidEq hret
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        have hlenStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [u256_add_lnot_zero_eq_sub_one, hstorageFlux]
        have hidEqStele : clipperYankArgWord I =
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidEq
        have haccFlux : ∃ acc, evmFlux.accountMap.get?
            evmFlux.executionEnv.codeOwner = some acc := by
          cases hfind : evmFlux.accountMap.get? evmFlux.executionEnv.codeOwner with
          | none =>
              exfalso
              apply hlenStele
              rw [Std.ExtTreeMap.get?_eq_getElem?] at hfind
              simp [Stele.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
          | some acc => exact ⟨acc, rfl⟩
        obtain ⟨accFlux, haccFlux⟩ := haccFlux
        let sourceLastIndex := UInt256.sub
          (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
        let evmRemove := clipperYankDeleteSaleState
          (clipperYankRemovePopState evmFlux sourceLastIndex) I
        let calleeFrame : Frame :=
          { contract := contract,
            locals := clipperYankRemoveMoveStore I sourceLastIndex
              (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot sourceLastIndex)), immutables := immStore v }
        have hremove : ExecFuncBody fork config
            { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
            evmFlux removeFunction.body (.returned calleeFrame evmRemove none) := by
          simpa [sourceLastIndex, evmRemove, calleeFrame] using
            clipperYankRemoveIdEqMoveSource
            (hperm := (congrArg ExecutionEnv.perm hevmFluxEnv).trans hperm) v evmFlux I haccFlux hlenStele hidEqStele
        have hpostDog :=
          clipperTakePostDogTabZeroFluxRemoveSourceOkAtCallbackDigsRet
            (hperm := by
              simpa (config := { zetaDelta := true }) only [clipperYankDeleteSaleState,
                clipperYankRemovePopState, storageStore_executionEnv] using
                (congrArg ExecutionEnv.perm hevmFluxEnv).trans hperm) v
            evmLock evmPrice evmVat evmDog evmFlux evmRemove I price slice owe0
            owe0 slice' tabNew lotNew
            (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeStele hcallFluxStele' hremove
        have hAccountsFinal :=
          clipperYankSuccessAccountMap_state_accounts_eq
            (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I lastIndex
            hAccountsFlux rfl hownerFlux
        exact hret.reEquivExecutionGen hcode hdispatch hdec
          (sourceReturned (tailOfPostDog (by
            simpa [postDogFrame] using hpostDog)))
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
        let evmIndex := Stele.EVM.storageStore evmFlux
          evmFlux.executionEnv.codeOwner (clipperYankActiveSlot idx) move
        let evmMovePos := Stele.EVM.storageStore evmIndex
          evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
        have hlenStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [u256_add_lnot_zero_eq_sub_one, hstorageFlux]
        have hidNeStele : clipperYankArgWord I ≠
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidNe
        have hidxBoundStele :
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankSalesPosSlot I)).toNat <
              (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat := by
          rw [← hstorageFlux, ← hstorageFlux]
          simpa [idx] using hidxBound
        have hmoveStele :
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot
                  (UInt256.sub
                    (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                    ⟨1⟩)) = move := by
          rw [← hlastIndexEq, ← hstorageFlux]
        have hidxStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
          rw [← hstorageFlux]
        have hmoveAccounts : Eq
            (clipperYankMoveAccountMap σFlux I idx move) evmMovePos.accountMap := by
          simpa [evmIndex, evmMovePos] using
            clipperYankMoveAccountMap_state_accounts_eq
              (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I idx move
              hAccountsFlux rfl hownerFlux
        have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
          simp [evmMovePos, evmIndex, storageStore_executionEnv, hownerFlux]
        have hstorageMove (slot : UInt256) :
            solcSlotWord (clipperYankMoveAccountMap σFlux I idx move) I slot =
              Stele.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
          have hslot := congrArg (fun m => solcSlotWord m I slot) hmoveAccounts
          simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            solcSlotWord, hownerMovePos, hslot]
        have hlenAfterStele : Stele.EVM.storageLoad evmMovePos
            evmMovePos.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
          rw [← hstorageMove]
          simpa [lastIndex, move, idx] using hlenAfter
        have hremoveRaw := clipperYankRemoveIdNeMovePopEmptySourceReverts (fork := fork)
            (hperm := (congrArg ExecutionEnv.perm hevmFluxEnv).trans hperm)
          v evmFlux I hlenStele hidNeStele hidxBoundStele
        dsimp only at hremoveRaw
        have hremove := hremoveRaw (by
          simpa only [hmoveStele, hidxStele, evmIndex, evmMovePos] using hlenAfterStele)
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))
      · intro hlen hidNe hidxBound hlenAfter hret
        let lastIndex := solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩
        let move := solcSlotWord σFlux I (clipperYankActiveSlot lastIndex)
        let idx := solcSlotWord σFlux I (clipperYankSalesPosSlot I)
        let σMove := clipperYankMoveAccountMap σFlux I idx move
        let evmIndex := Stele.EVM.storageStore evmFlux
          evmFlux.executionEnv.codeOwner (clipperYankActiveSlot idx) move
        let evmMovePos := Stele.EVM.storageStore evmIndex
          evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
        have hlenStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [u256_add_lnot_zero_eq_sub_one, hstorageFlux]
        have hmoveStele :
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankActiveSlot
                  (UInt256.sub
                    (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                    ⟨1⟩)) = move := by
          rw [← hlastIndexEq, ← hstorageFlux]
        have hidxStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
          rw [← hstorageFlux]
        have hidNeStele : clipperYankArgWord I ≠
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [hmoveStele]
          simpa [lastIndex, move] using hidNe
        have hidxBoundStele :
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankSalesPosSlot I)).toNat <
              (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat := by
          rw [hidxStele, ← hstorageFlux]
          simpa [idx] using hidxBound
        have hmoveAccounts : Eq σMove evmMovePos.accountMap := by
          simpa [σMove, evmIndex, evmMovePos] using
            clipperYankMoveAccountMap_state_accounts_eq
              (σ := σFlux) (τ := evmFlux.accountMap) evmFlux I idx move
              hAccountsFlux rfl hownerFlux
        have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
          simp [evmMovePos, evmIndex, storageStore_executionEnv, hownerFlux]
        have hstorageMove (slot : UInt256) :
            solcSlotWord σMove I slot =
              Stele.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
          have hslot := congrArg (fun m => solcSlotWord m I slot) hmoveAccounts
          simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            solcSlotWord, hownerMovePos, σMove, hslot]
        have hlenAfterStele : Stele.EVM.storageLoad evmMovePos
            evmMovePos.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          apply hlenAfter
          simpa [lastIndex, move, idx, σMove] using
            (show solcSlotWord σMove I ⟨11⟩ = ⟨0⟩ by
              rw [hstorageMove]
              exact hzero)
        have haccFlux : ∃ acc, evmFlux.accountMap.get?
            evmFlux.executionEnv.codeOwner = some acc := by
          cases hfind : evmFlux.accountMap.get? evmFlux.executionEnv.codeOwner with
          | none =>
              exfalso
              apply hlenStele
              rw [Std.ExtTreeMap.get?_eq_getElem?] at hfind
              simp [Stele.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
          | some acc => exact ⟨acc, rfl⟩
        obtain ⟨accFlux, haccFlux⟩ := haccFlux
        let popLastIndex := UInt256.sub
          (Stele.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
        let evmRemove := clipperYankDeleteSaleState
          (clipperYankRemovePopState evmMovePos popLastIndex) I
        let calleeFrame : Frame :=
          { contract := contract,
            locals := clipperYankRemoveIndexStore I
              (UInt256.sub
                (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)
              move idx, immutables := immStore v }
        have hremoveRaw := clipperYankRemoveIdNeMoveSource (fork := fork)
            (hperm := (congrArg ExecutionEnv.perm hevmFluxEnv).trans hperm)
          v evmFlux I haccFlux hlenStele hidNeStele hidxBoundStele
        dsimp only at hremoveRaw
        have hremove : ExecFuncBody fork config
            { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
            evmFlux removeFunction.body (.returned calleeFrame evmRemove none) := by
          have hremoveSource := hremoveRaw (by
            simpa only [hmoveStele, hidxStele, evmIndex, evmMovePos] using hlenAfterStele)
          simpa only [calleeFrame, evmRemove, popLastIndex, hmoveStele, hidxStele,
            evmIndex, evmMovePos] using hremoveSource
        have hpostDog :=
          clipperTakePostDogTabZeroFluxRemoveSourceOkAtCallbackDigsRet
            (hperm := by
              simpa (config := { zetaDelta := true }) only [clipperYankDeleteSaleState,
                clipperYankRemovePopState, storageStore_executionEnv] using
                (congrArg ExecutionEnv.perm hevmFluxEnv).trans hperm) v
            evmLock evmPrice evmVat evmDog evmFlux evmRemove I price slice owe0
            owe0 slice' tabNew lotNew
            (by simpa [lotNew, htab, hlot] using hlotNew)
            (by exact u256_sub_self _) hfluxCodeStele hcallFluxStele' hremove
        let lastIndexAfter := solcSlotWord σMove I ⟨11⟩ + UInt256.lnot ⟨0⟩
        have hlastIndexAfterEq : lastIndexAfter = popLastIndex := by
          rw [show lastIndexAfter = solcSlotWord σMove I ⟨11⟩ +
            UInt256.lnot ⟨0⟩ from rfl]
          rw [u256_add_lnot_zero_eq_sub_one, hstorageMove]
        have hAccountsFinal :=
          clipperYankSuccessAccountMap_state_accounts_eq
            (σ := σMove) (τ := evmMovePos.accountMap) evmMovePos I lastIndexAfter
            hmoveAccounts rfl hownerMovePos
        exact hret.reEquivExecutionGen hcode hdispatch hdec
          (sourceReturned (tailOfPostDog (by
            simpa [postDogFrame] using hpostDog)))
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
        have hlenStele : Stele.EVM.storageLoad evmFlux
            evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
          intro hzero
          exact hlen (by rw [hstorageFlux]; exact hzero)
        have hlastIndexEq : lastIndex = UInt256.sub
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
          rw [show lastIndex = solcSlotWord σFlux I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
          rw [u256_add_lnot_zero_eq_sub_one, hstorageFlux]
        have hidNeStele : clipperYankArgWord I ≠
            Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
              (clipperYankActiveSlot
                (UInt256.sub
                  (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩)
                  ⟨1⟩)) := by
          rw [← hlastIndexEq, ← hstorageFlux]
          simpa [lastIndex] using hidNe
        have hidxBoundStele :
            (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩).toNat ≤
              (Stele.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
                (clipperYankSalesPosSlot I)).toNat := by
          rw [← hstorageFlux, ← hstorageFlux]
          simpa using hidxBound
        have hremove := clipperYankRemoveIdNeMoveIndexOobSourceReverts (fork := fork)
          v evmFlux I hlenStele hidNeStele hidxBoundStele
        exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
          (sourceReverted (tailOfPostDog (postDogReverted hremove)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem clipperTakeOweGtTabCallbackSuccessContinuationEquivFromPostCallAccounts
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost σPostStele σVat σCb : AccountMap}
    {AVat ACb : Substate} {evmPriceStele : EVM.State}
    {outVat outCb : ByteArray} {price tab lot who : UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (List.map Param.name takeTransition.params)
        (transitionSignature takeTransition).paramTypes I.calldata =
      some (clipperTakeStore I))
    (hlockedStele : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstoppedSteleLt :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husrStele :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd4701 : RD fork code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
      (UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask ::
        tab.div price :: tab :: tab.sub tab :: lot.sub (tab.div price) :: price ::
        clipperTakeSalesTicStackWord
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ::
        UInt256.land
          (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I
            (clipperTakeSalesPackedSlot I)) solcAddrMask ::
        ⟨3⟩ :: clipperTakeDataLenWord I ::
        (⟨32⟩ + (⟨4⟩ + clipperTakeDataOffsetWord I)) ::
        UInt256.land (clipperTakeWhoWord I) solcAddrMask ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        [⟨502⟩, clipperSelWord I])
      mem aw rdata σCb k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hAccountsPost : Eq σPost σPostStele)
    (hevmPriceAccounts : evmPriceStele.accountMap = σPostStele)
    (hevmPriceSigma0 : evmPriceStele.σ₀ = σ₀)
    (hevmPriceEnv : evmPriceStele.executionEnv = I)
    (htab : tab = clipperTakeSalesTabEVMWord evmPriceStele I)
    (hlot : lot = clipperTakeSalesLotEVMWord evmPriceStele I)
    (hwho : who = UInt256.land (clipperTakeWhoWord I) solcAddrMask)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I) lot).toNat < UInt256.size)
    (hgt : tab.toNat <
      (UInt256.mul price
        (clipperMinWord (clipperTakeAmtWord I) lot)).toNat)
    (hvatCodeEvm :
      Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hcallVatEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σPost }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat (tab.div price).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true)
    (hcallCbEvm :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σVat, substate := AVat }
        (EVM.address
          (AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat tab.toNat),
          .int (Int.ofNat (tab.div price).toNat), clipperTakeDataValue I]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σCb, substate := ACb },
          outCb) true)
    (hdataLen : clipperTakeDataLenWord I ≠ ⟨0⟩)
    (hpayload : (clipperTakeDataBytes I).length =
      (clipperTakeDataLenWord I).toNat)
    (hwhoVat : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      clipperTakeVatTarget v)
    (hwhoDog : UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
      UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask)
    (hcallbackCode :
      Reasoning.Theory.extCodeSizeWord σVat
        (UInt256.land (clipperTakeWhoWord I) solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Stele.EVM.storageStore evm0
        evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt fork config
        { contract := contract, locals := clipperTakeLocalsTic evmLock I, immutables := immStore v }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok
          { contract := contract,
            locals := clipperTakeLocalsSt evmLock I false price, immutables := immStore v }
          evmPriceStele)) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  obtain ⟨evmVatStele, hcallVatStele, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
    clipperTakeVatFluxCallSyncFromPostAccounts v hAccountsPost
      hevmPriceAccounts hevmPriceSigma0 hevmPriceEnv htab hwho hcallVatEvm
  have hvatCodeStele :
      0 < (UInt256.ofNat
        ((evmPriceStele.lookupAccount v.vat).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount, hevmPriceAccounts] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (target := clipperTakeVatTarget v) (addr := v.vat)
        (clipperTakeVatTargetAddress v).symm
        (by simpa only [← hAccountsPost] using hvatCodeEvm)
  have hdogWord :=
    clipperTakeDogWord_eq hAccountsVat hevmVatEnv
  have hdogClean :
      UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask =
        clipperTakeDogEVMWord evmVatStele := by
    rw [← hdogWord]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
  have hwhoDogStele :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask ≠
        UInt256.land (clipperTakeDogEVMWord evmVatStele) solcAddrMask := by
    simpa [hdogClean, hdogWord] using hwhoDog
  have hguard :=
    clipperEvalTakeCallbackGuardTrue v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hdataLen hpayload hwhoVat hwhoDogStele
  have haddr :
      AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
        AccountAddress.ofUInt256
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact addressOfNat_eq_of_masked_word (clipperTakeWhoWord I)
  have hcodeStele :
      0 < (UInt256.ofNat
        ((evmVatStele.lookupAccount
          (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        haddr
        (by simpa only [← hAccountsVat] using hcallbackCode)
  let evmVatEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σVat, substate := AVat }
  have hAccountsState :
      Eq evmVatEvm.accountMap evmVatStele.accountMap := by
    simpa [evmVatEvm] using hAccountsVat
  obtain ⟨σCbStele, ACbStele, hcallCbSteleRaw, hAccountsCb⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs
      (evm_stele := evmVatStele) (hcall := hcallCbEvm) hAccountsState
      (by simpa [evmVatEvm, initState] using hevmVatSigma0.symm)
      (by simpa [evmVatEvm, initState] using hevmVatEnv.symm)
  let evmCbStele : EVM.State :=
    { evmVatStele with
      accountMap := σCbStele
      substate := ACbStele
       }
  have hcallCbStele :
      typedCallViaEVM fork config evmVatStele
        (EVM.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat))
        "clipperCall" 0
        [.address evmVatStele.executionEnv.source,
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmPriceStele I).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price).toNat),
          clipperTakeDataValue I]
        (true, evmCbStele, outCb) true := by
    have hwhoClean : UInt256.land who solcAddrMask = who := by
      rw [hwho]
      exact solcAddrMask_clean
        (solcAddrMask_result_canonical (clipperTakeWhoWord I))
    have htargetAddr :
        AccountAddress.ofNat (UInt256.land who solcAddrMask).toNat =
          AccountAddress.ofNat (clipperTakeWhoWord I).toNat := by
      rw [hwhoClean, hwho]
      exact (addressOfNat_eq_of_masked_word (clipperTakeWhoWord I)).symm
    rw [htargetAddr] at hcallCbSteleRaw
    simpa only [evmCbStele, hevmVatEnv, htab] using hcallCbSteleRaw
  have hcallback :=
    clipperTakeCallbackCallSuccessStmt v
      (Stele.EVM.storageStore
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨13⟩ ⟨1⟩)
      evmPriceStele evmVatStele evmCbStele I price
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
        (clipperTakeAmtWord I))
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.mul
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPriceStele I)
          (clipperTakeAmtWord I)) price)
      (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price)
      (UInt256.sub (clipperTakeSalesTabEVMWord evmPriceStele I)
        (clipperTakeSalesTabEVMWord evmPriceStele I))
      (UInt256.sub (clipperTakeSalesLotEVMWord evmPriceStele I)
        (UInt256.div (clipperTakeSalesTabEVMWord evmPriceStele I) price))
      hguard hcodeStele hcallCbStele
  exact clipperTakeOweGtTabCallbackSuccessContinuationEquiv
    (evmPrice := evmPriceStele) (evmVat := evmVatStele) (evmCb := evmCbStele)
    (σPost := σPost) (σVatEvm := σVat) (σCbEvm := σCb)
    (outCb := outCb)
    v hpatch hcode hwv hdispatch hdec hlockedStele
    hstoppedSteleLt husrStele rd4701 hmem hAccountsVat
    (by simpa [evmCbStele] using hAccountsCb)
    (by simpa [evmCbStele] using hevmVatSigma0)
    (by simpa [evmCbStele] using hevmVatEnv)
    htab hlot hevmPriceEnv hmax hmul hgt hvatCodeStele hcallVatStele
    (by simpa using hcallback) hdepth hperm hstatus

end Benchmarks.Dss.Clipper
