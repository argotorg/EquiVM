import Benchmarks.Dss.Clipper.TakeFluxCallbackEVM
import Benchmarks.Dss.Clipper.TakeNonzeroStoreContinuationEquiv
import Benchmarks.Dss.Clipper.TakeGenericCallbackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeCallbackStmt (v : ClipperImmutables) : Stmt :=
  .ite
    (.binary .and
      (.binary .gt (bytesLength "data") (.intLit 0))
      (.binary .and
        (.binary .ne (.var "who") (vatExpr v))
        (.binary .ne (.var "who") (.var "dog_"))))
    (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
      [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet") []

/- The arithmetic branches all reach the same callback and vat-flux suffix, but
   they do not all reach the same storage suffix: a full purchase removes the
   sale, while a partial purchase stores nonzero residual values.  Abstracting
   that final continuation keeps the shared external-call proof independent of
   this arithmetic distinction. -/
abbrev ClipperTakeStoreContinuationEquiv
    (v : ClipperImmutables) (code : ByteArray)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (σ_evm σ_solm σ₀ : AccountMap) (A : Substate)
    (I : ExecutionEnv) (g slice owe tabNew lotNew price tic packed stopped dataLen
      dataStart who max amt id sel : UInt256) : Prop :=
  ∀ {cACont : Batteries.RBSet AccountAddress compare} {σCont : AccountMap}
    {evmCont : EVM.State} {locals : Store} {dog : UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ},
    RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4701⟩
        (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
          [⟨502⟩, sel])
        mem aw rdata (cACont, σCont) k C →
    clipperTakeMemoryWF mem aw →
    accountMapEquiv σCont evmCont.accountMap →
    evmCont.σ₀ = σ₀ →
    evmCont.createdAccounts = cACont →
    evmCont.genesisBlockHeader = gh →
    evmCont.blocks = bl →
    evmCont.executionEnv = I →
    UInt256.land solcAddrMask dog = dog →
    locals.get? "owe" = some (.int (Int.ofNat owe.toNat)) →
    locals.get? "tab" = some (.int (Int.ofNat tabNew.toNat)) →
    locals.get? "lot" = some (.int (Int.ofNat lotNew.toNat)) →
    locals.get? "dog_" = some (.address (AccountAddress.ofNat dog.toNat)) →
    locals.get? "usr" = some (.address (AccountAddress.ofNat packed.toNat)) →
    locals.get? "id" = some (clipperTakeIdValue I) →
    locals.get? "locked" = none →
    locals.get? "vow" = none →
    locals.get? "sales" = none →
    (ExecBlock (config v) (Frame.mk (contract v) locals) evmCont
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) .reverted →
        ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) (takeTransition v).body .reverted) →
    (∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v) (Frame.mk (contract v) locals) evmCont
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm) →
        ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) (takeTransition v).body
          (.returned finalFrame finalEvm none)) →
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I

/- This theorem connects the common PC-4223 EVM suffix to an arbitrary arithmetic
   source prefix.  The prefix and callback steps are explicit hypotheses because the
   arithmetic branches retain different dead scratch locals. -/
set_option maxHeartbeats 8000000 in
theorem clipperTakeFromFluxEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σPost : AccountMap} {evmPrice : EVM.State}
    {sliceLocals fluxLocals : Store}
    {price slice owe tab lot tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {baseMem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name (takeTransition v).params)
        (transitionSignature (takeTransition v)).paramTypes I.calldata =
      some (clipperTakeStore I))
    (rd4223 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4223⟩
      (slice :: owe :: tab :: lot :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      baseMem (UInt256.ofNat 7) rdata (cAPost, σPost) k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccountsPost : accountMapEquiv σPost evmPrice.accountMap)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceCreated : evmPrice.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPrice.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPrice.blocks = bl)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat)
    (hwhoClean : UInt256.land who solcAddrMask = who)
    (hfluxDogAbsent : fluxLocals.get? "dog" = none)
    (hfluxOwe : fluxLocals.get? "owe" = some (.int (Int.ofNat owe.toNat)))
    (hfluxSlice : fluxLocals.get? "slice" = some (.int (Int.ofNat slice.toNat)))
    (hfluxTab : fluxLocals.get? "tab" =
      some (.int (Int.ofNat (UInt256.sub tab owe).toNat)))
    (hfluxLot : fluxLocals.get? "lot" =
      some (.int (Int.ofNat (UInt256.sub lot slice).toNat)))
    (hfluxWho : fluxLocals.get? "who" =
      some (.address (AccountAddress.ofNat who.toNat)))
    (hfluxUsr : fluxLocals.get? "usr" =
      some (.address (AccountAddress.ofNat packed.toNat)))
    (hfluxData : fluxLocals.get? "data" = some (clipperTakeDataValue I))
    (hfluxId : fluxLocals.get? "id" = some (clipperTakeIdValue I))
    (hfluxLocked : fluxLocals.get? "locked" = none)
    (hfluxVow : fluxLocals.get? "vow" = none)
    (hfluxSales : fluxLocals.get? "sales" = none)
    (hsourceVatNoCode :
      (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0 →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceVatFailure : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceFluxSuccess : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true →
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts v)
        (.ok (Frame.mk (contract v) fluxLocals) evmVat))
    (hsourceCloseReverted :
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (clipperTakeAfterSliceStmts v) .reverted →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceCloseReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (clipperTakeAfterSliceStmts v) (.ok finalFrame finalEvm) →
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body
        (.returned finalFrame finalEvm none))
    (hcontinue : ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm σ_solm
      σ₀ A I g slice owe (UInt256.sub tab owe) (UInt256.sub lot slice) price tic
      packed stopped dataLen dataStart who max amt id sel)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmPriceEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost, createdAccounts := cAPost }
  have hdataBytesLen : (clipperTakeDataBytes I).length = dataLen.toNat := by
    simpa [clipperTakeDataBytes, hdataLenEq] using hpayload
  have hdataBytesPos : 0 < (clipperTakeDataBytes I).length := by
    have hdataNat : dataLen.toNat ≠ 0 := by
      intro hz
      exact hdataLen (uint256_toNat_eq_zero hz)
    omega
  have hvatTargetAddress : AccountAddress.ofNat (clipperTakeVatTarget v).toNat =
      v.vat := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    exact clipperTakeVatTargetAddress v
  have hvatTargetClean : UInt256.land (clipperTakeVatTarget v) solcAddrMask =
      clipperTakeVatTarget v := by
    exact solcAddrMask_clean (by
      simpa [clipperTakeVatTarget, u256_land_comm] using
        solcAddrMask_result_canonical (EVM.Word.ofNat (↑v.vat : Nat)))
  have hwhoAddressNeVat
      (hne : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v) :
      AccountAddress.ofNat who.toNat ≠ v.vat := by
    intro haddr
    apply hne
    have hmasked := clipperMaskedAddress_injective (a := who)
      (b := clipperTakeVatTarget v) (by
        rw [hwhoClean, hvatTargetClean]
        exact haddr.trans hvatTargetAddress.symm)
    simpa [hvatTargetClean] using hmasked
  have hwhoAddressNeDog {dog : UInt256}
      (hdogClean : UInt256.land dog solcAddrMask = dog)
      (hne : UInt256.land who solcAddrMask ≠ dog) :
      AccountAddress.ofNat who.toNat ≠ AccountAddress.ofNat dog.toNat := by
    intro haddr
    apply hne
    have hmasked := clipperMaskedAddress_injective (a := who) (b := dog) (by
      rw [hwhoClean, hdogClean]
      exact haddr)
    simpa [hdogClean] using hmasked
  have hvatCodeSolmOf
      (hne : Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩) :
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
        hAccountsPost (clipperTakeVatTargetAddress v).symm hne
  have syncFlux {cAVat : Batteries.RBSet AccountAddress compare}
      {σVat : AccountMap} {AVat : Substate} {zVat : Bool} {outVat : ByteArray}
      (hcall : typedCallViaEVM (config v) evmPriceEvm
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (zVat,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat, createdAccounts := cAVat },
          outVat) true) :=
    clipperTypedCallSyncFromState hAccountsPost
      (by simp [evmPriceEvm, initState, hevmPriceSigma0])
      (by simp [evmPriceEvm, hevmPriceCreated])
      (by simp [evmPriceEvm, initState, hevmPriceGenesis])
      (by simp [evmPriceEvm, initState, hevmPriceBlocks])
      (by simp [evmPriceEvm, initState, hevmPriceEnv]) hcall
  have closeRevert
      (hrev : RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
      (hbody : ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) (takeTransition v).body .reverted) :
      runtimeEquivalenceFor (config v) (contract v)
        cA gh bl σ_evm σ_solm σ₀ g A I :=
    hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
  apply RD.clipperTakeFluxCallbackElim v hpatch rd4223 hbaseSize hbaseRead64
    hdataLen hdataLenEq hdataStartEq hlenMax hpayload hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm : (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccountsPost (clipperTakeVatTargetAddress v).symm hnoCode
    exact closeRevert hrev (hsourceVatNoCode hnoCodeSolm)
  · intro cAVat σVat outVat AVat hcall hvatCode hrev
    obtain ⟨evmVat, hcallSolm, _, _, _, _, _, _⟩ := syncFlux (by simpa [evmPriceEvm] using hcall)
    exact closeRevert hrev (hsourceVatFailure (hvatCodeSolmOf hvatCode)
      (by simpa [hevmPriceEnv] using hcallSolm))
  · intro cAVat σVat outVat AVat memVat awVat kVat CVat hcall hvatCode hskip hmem
      rd4701
    obtain ⟨evmVat, hcallSolm, hAccountsVat, hevmVatSigma0, hevmVatCreated,
        hevmVatGenesis, hevmVatBlocks, hevmVatEnv⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    have hcallSolm' : typedCallViaEVM (config v) evmPrice (EVM.address v.vat)
        "flux" 0 [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true := by
      simpa [hevmPriceEnv] using hcallSolm
    have hflux := hsourceFluxSuccess (hvatCodeSolmOf hvatCode) hcallSolm'
    let dogLocals := fluxLocals.insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
    have hletDog : ExecStmt (config v) (Frame.mk (contract v) fluxLocals) evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok (Frame.mk (contract v) dogLocals) evmVat) := by
      simpa [dogLocals] using
        (ExecStmt.letDecl (cfg := config v) (solm := Frame.mk (contract v) fluxLocals)
          (evm := evmVat) (name := "dog_") (ty := some addr) (expr := .storage dogRef)
          (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
          (by simpa [clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat fluxLocals hfluxDogAbsent))
    have hdogWord : UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask =
        clipperTakeDogEVMWord evmVat :=
      clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
    have hwhoLocal : dogLocals.get? "who" =
        some (.address (AccountAddress.ofNat who.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxWho
    have hdataLocal : dogLocals.get? "data" = some (clipperTakeDataValue I) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxData
    have hdogLocal : dogLocals.get? "dog_" = some (.address
        (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simp [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have hguard : evalExpr? (config v) (Frame.mk (contract v) dogLocals) evmVat
        (.binary .and
          (.binary .gt (bytesLength "data") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "who") (vatExpr v))
            (.binary .ne (.var "who") (.var "dog_")))) = .ok (.bool false) := by
      rcases hskip with hwhoVat | ⟨_, hwhoDog⟩
      · have hword : who = clipperTakeVatTarget v := hwhoClean.symm.trans hwhoVat
        apply clipperTakeGenericCallbackGuardFalseWhoVat hdataLocal hwhoLocal
          hdogLocal hdataBytesPos
        simpa [hword] using hvatTargetAddress
      · have hword : who = clipperTakeDogEVMWord evmVat :=
          hwhoClean.symm.trans (hwhoDog.trans hdogWord)
        apply clipperTakeGenericCallbackGuardFalseWhoDog hdataLocal hwhoLocal
          hdogLocal hdataBytesPos
        exact congrArg (fun w : UInt256 => AccountAddress.ofNat w.toNat) hword
    have hcb := clipperTakeCallbackSkipOfEval hguard
    have sourceReverted
        (htail : ExecBlock (config v) (Frame.mk (contract v) dogLocals) evmVat
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) .reverted) :=
      hsourceCloseReverted
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb) htail)
    have sourceReturned {finalFrame : Frame} {finalEvm : EVM.State}
        (htail : ExecBlock (config v) (Frame.mk (contract v) dogLocals) evmVat
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm)) :=
      hsourceCloseReturned
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb) htail)
    apply hcontinue (locals := dogLocals) rd4701 hmem hAccountsVat
      hevmVatSigma0 hevmVatCreated
      hevmVatGenesis hevmVatBlocks hevmVatEnv
    · simpa [hdogWord] using solcAddrMask_clean_left
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxOwe
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxTab
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxLot
    · simp [dogLocals, hdogWord, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxUsr
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxId
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxLocked
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxVow
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxSales
    · exact sourceReverted
    · exact sourceReturned
  · intro cAVat σVat outVat AVat hcall hvatCode hwhoVat hwhoDog hnoCode hrev
    obtain ⟨evmVat, hcallSolm, hAccountsVat, _, _, _, _, hevmVatEnv⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    have hflux := hsourceFluxSuccess (hvatCodeSolmOf hvatCode)
      (by simpa [hevmPriceEnv] using hcallSolm)
    let dogLocals := fluxLocals.insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
    have hletDog : ExecStmt (config v) (Frame.mk (contract v) fluxLocals) evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok (Frame.mk (contract v) dogLocals) evmVat) := by
      simpa [dogLocals] using
        (ExecStmt.letDecl (cfg := config v) (solm := Frame.mk (contract v) fluxLocals)
          (evm := evmVat) (name := "dog_") (ty := some addr) (expr := .storage dogRef)
          (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
          (by simpa [clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat fluxLocals hfluxDogAbsent))
    have hnoCodeSolm : (UInt256.ofNat
        ((evmVat.lookupAccount (AccountAddress.ofNat who.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount, hwhoClean] using
        clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
          hAccountsVat (by
            rw [accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm,
              hwhoClean]) hnoCode
    have hdogWord : UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask =
        clipperTakeDogEVMWord evmVat :=
      clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
    have hdogClean : UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask =
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using solcAddrMask_clean
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    have hwhoDogWord : UInt256.land who solcAddrMask ≠
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using hwhoDog
    have hwhoLocal : dogLocals.get? "who" =
        some (.address (AccountAddress.ofNat who.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxWho
    have hdataLocal : dogLocals.get? "data" = some (clipperTakeDataValue I) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxData
    have hdogLocal : dogLocals.get? "dog_" = some (.address
        (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simp [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have hguard := clipperTakeGenericCallbackGuardTrue (v := v) (evm := evmVat)
      hdataLocal hwhoLocal hdogLocal
      hdataBytesPos (hwhoAddressNeVat hwhoVat)
        (hwhoAddressNeDog hdogClean hwhoDogWord)
    have hcodeEval : evalExpr? (config v) (Frame.mk (contract v) dogLocals) evmVat
        (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool false) := by
      simpa [hnoCodeSolm] using
        (clipperEvalTakeGenericCallbackCodeGuard (v := v) (evm := evmVat) hwhoLocal)
    have hcb := clipperTakeCallbackNoCodeOfEvals hguard hcodeEval
    exact closeRevert hrev
      (hsourceCloseReverted
        (clipperTakeAfterSliceOfPrefixAndCallbackRevert hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb)))
  · intro cAVat σVat outVat AVat cACb σCb outCb ACb hcall hvatCode hwhoVat hwhoDog
      hcallbackCode hcallCb hrev
    obtain ⟨evmVat, hcallSolm, hAccountsVat, hevmVatSigma0, hevmVatCreated,
        hevmVatGenesis, hevmVatBlocks, hevmVatEnv⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVat, createdAccounts := cAVat }
    let evmCbEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCb, substate := ACb, createdAccounts := cACb }
    obtain ⟨evmCb, hcallCbSolm, _, _, _, _, _, _⟩ :=
      clipperTypedCallSyncFromState (evmEvm := evmVatEvm) (evmSolm := evmVat)
        (evmEvm' := evmCbEvm) hAccountsVat
        (by simp [evmVatEvm, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, hevmVatGenesis])
        (by simp [evmVatEvm, hevmVatBlocks])
        (by simp [evmVatEvm, hevmVatEnv])
        (by simpa [evmVatEvm, evmCbEvm, hwhoClean] using hcallCb)
    have hflux := hsourceFluxSuccess (hvatCodeSolmOf hvatCode)
      (by simpa [hevmPriceEnv] using hcallSolm)
    let dogLocals := fluxLocals.insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
    have hletDog : ExecStmt (config v) (Frame.mk (contract v) fluxLocals) evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok (Frame.mk (contract v) dogLocals) evmVat) := by
      simpa [dogLocals] using
        (ExecStmt.letDecl (cfg := config v) (solm := Frame.mk (contract v) fluxLocals)
          (evm := evmVat) (name := "dog_") (ty := some addr) (expr := .storage dogRef)
          (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
          (by simpa [clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat fluxLocals hfluxDogAbsent))
    have hcallCbSolm' : typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofNat who.toNat)) "clipperCall" 0
        [.address evmVat.executionEnv.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I]
        (false, evmCb, outCb) true := by
      simpa [evmVatEvm, evmCbEvm, initState, hwhoClean, hevmVatEnv,
        u256_land_comm] using hcallCbSolm
    have hdogWord : UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask =
        clipperTakeDogEVMWord evmVat :=
      clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
    have hdogClean : UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask =
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using solcAddrMask_clean
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    have hwhoDogWord : UInt256.land who solcAddrMask ≠
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using hwhoDog
    have hwhoLocal : dogLocals.get? "who" =
        some (.address (AccountAddress.ofNat who.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxWho
    have hdataLocal : dogLocals.get? "data" = some (clipperTakeDataValue I) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxData
    have hdogLocal : dogLocals.get? "dog_" = some (.address
        (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simp [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have howeLocal : dogLocals.get? "owe" = some (.int (Int.ofNat owe.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxOwe
    have hsliceLocal : dogLocals.get? "slice" =
        some (.int (Int.ofNat slice.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxSlice
    have hguard := clipperTakeGenericCallbackGuardTrue (v := v) (evm := evmVat)
      hdataLocal hwhoLocal hdogLocal
      hdataBytesPos (hwhoAddressNeVat hwhoVat)
        (hwhoAddressNeDog hdogClean hwhoDogWord)
    have hcallbackCodeSolm : 0 < (UInt256.ofNat
        ((evmVat.lookupAccount (AccountAddress.ofNat who.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (by
            rw [accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm,
              hwhoClean]) hcallbackCode
    have hcodeEval : evalExpr? (config v) (Frame.mk (contract v) dogLocals) evmVat
        (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool true) := by
      simpa [hcallbackCodeSolm] using
        (clipperEvalTakeGenericCallbackCodeGuard (v := v) (evm := evmVat) hwhoLocal)
    have hargs := clipperEvalTakeGenericCallbackArgs (v := v) (I := I) (evm := evmVat)
      howeLocal hsliceLocal hdataLocal
    have hcb := clipperTakeCallbackFailureOfEvals hguard hcodeEval hwhoLocal hargs
      hcallCbSolm'
    exact closeRevert hrev
      (hsourceCloseReverted
        (clipperTakeAfterSliceOfPrefixAndCallbackRevert hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb)))
  · intro cAVat σVat outVat AVat cACb σCb outCb ACb memCb awCb kCb CCb
      hcall hvatCode hwhoVat hwhoDog hcallbackCode hcallCb rd4701 hmem
    obtain ⟨evmVat, hcallSolm, hAccountsVat, hevmVatSigma0, hevmVatCreated,
        hevmVatGenesis, hevmVatBlocks, hevmVatEnv⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    let evmVatEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σVat, createdAccounts := cAVat }
    let evmCbEvm : EVM.State :=
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σCb, substate := ACb, createdAccounts := cACb }
    obtain ⟨evmCb, hcallCbSolm, hAccountsCb, hevmCbSigma0, hevmCbCreated,
        hevmCbGenesis, hevmCbBlocks, hevmCbEnv⟩ :=
      clipperTypedCallSyncFromState (evmEvm := evmVatEvm) (evmSolm := evmVat)
        (evmEvm' := evmCbEvm) hAccountsVat
        (by simp [evmVatEvm, hevmVatSigma0])
        (by simp [evmVatEvm, hevmVatCreated])
        (by simp [evmVatEvm, hevmVatGenesis])
        (by simp [evmVatEvm, hevmVatBlocks])
        (by simp [evmVatEvm, hevmVatEnv])
        (by simpa [evmVatEvm, evmCbEvm, hwhoClean] using hcallCb)
    have hflux := hsourceFluxSuccess (hvatCodeSolmOf hvatCode)
      (by simpa [hevmPriceEnv] using hcallSolm)
    let dogLocals := fluxLocals.insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
    let cbLocals := dogLocals.insert "_clipperCallRet" .unit
    have hletDog : ExecStmt (config v) (Frame.mk (contract v) fluxLocals) evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok (Frame.mk (contract v) dogLocals) evmVat) := by
      simpa [dogLocals] using
        (ExecStmt.letDecl (cfg := config v) (solm := Frame.mk (contract v) fluxLocals)
          (evm := evmVat) (name := "dog_") (ty := some addr) (expr := .storage dogRef)
          (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
          (by simpa [clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat fluxLocals hfluxDogAbsent))
    have hcallCbSolm' : typedCallViaEVM (config v) evmVat
        (EVM.address (AccountAddress.ofNat who.toNat)) "clipperCall" 0
        [.address evmVat.executionEnv.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I]
        (true, evmCb, outCb) true := by
      simpa [evmVatEvm, evmCbEvm, initState, hwhoClean, hevmVatEnv,
        u256_land_comm] using hcallCbSolm
    have hdogWord : UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask =
        clipperTakeDogEVMWord evmVat :=
      clipperTakeDogWord_eq_of_accountMapEquiv hAccountsVat hevmVatEnv
    have hdogClean : UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask =
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using solcAddrMask_clean
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    have hwhoDogWord : UInt256.land who solcAddrMask ≠
        clipperTakeDogEVMWord evmVat := by
      simpa [hdogWord] using hwhoDog
    have hwhoLocal : dogLocals.get? "who" =
        some (.address (AccountAddress.ofNat who.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxWho
    have hdataLocal : dogLocals.get? "data" = some (clipperTakeDataValue I) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxData
    have hdogLocal : dogLocals.get? "dog_" = some (.address
        (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simp [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have howeLocal : dogLocals.get? "owe" = some (.int (Int.ofNat owe.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxOwe
    have hsliceLocal : dogLocals.get? "slice" =
        some (.int (Int.ofNat slice.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hfluxSlice
    have hguard := clipperTakeGenericCallbackGuardTrue (v := v) (evm := evmVat)
      hdataLocal hwhoLocal hdogLocal
      hdataBytesPos (hwhoAddressNeVat hwhoVat)
        (hwhoAddressNeDog hdogClean hwhoDogWord)
    have hcallbackCodeSolm : 0 < (UInt256.ofNat
        ((evmVat.lookupAccount (AccountAddress.ofNat who.toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
      simpa [State.lookupAccount] using
        clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
          hAccountsVat (by
            rw [accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm,
              hwhoClean]) hcallbackCode
    have hcodeEval : evalExpr? (config v) (Frame.mk (contract v) dogLocals) evmVat
        (.binary .gt (.extCodeSize (.var "who")) (.intLit 0)) = .ok (.bool true) := by
      simpa [hcallbackCodeSolm] using
        (clipperEvalTakeGenericCallbackCodeGuard (v := v) (evm := evmVat) hwhoLocal)
    have hargs := clipperEvalTakeGenericCallbackArgs (v := v) (I := I) (evm := evmVat)
      howeLocal hsliceLocal hdataLocal
    have hcb := clipperTakeCallbackSuccessOfEvals hguard hcodeEval hwhoLocal hargs
      hcallCbSolm'
    have sourceReverted
        (htail : ExecBlock (config v) (Frame.mk (contract v) cbLocals) evmCb
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) .reverted) :=
      hsourceCloseReverted
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals, cbLocals] using hcb) htail)
    have sourceReturned {finalFrame : Frame} {finalEvm : EVM.State}
        (htail : ExecBlock (config v) (Frame.mk (contract v) cbLocals) evmCb
          (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts v) (.ok finalFrame finalEvm)) :=
      hsourceCloseReturned
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals, cbLocals] using hcb) htail)
    apply hcontinue (locals := cbLocals) rd4701 hmem hAccountsCb
      hevmCbSigma0 hevmCbCreated
      hevmCbGenesis hevmCbBlocks hevmCbEnv
    · simpa [hdogWord] using solcAddrMask_clean_left
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxOwe
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxTab
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxLot
    · simp [cbLocals, dogLocals, hdogWord, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxUsr
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxId
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxLocked
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxVow
    · simpa [cbLocals, dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxSales
    · exact sourceReverted
    · exact sourceReturned

/- Instantiate the abstract continuation with the ordinary partial-purchase
   storage path. -/
theorem clipperTakeNonzeroStoreContinuation
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
    (htabNe : tabNew ≠ ⟨0⟩) (hlotNe : lotNew ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm σ_solm σ₀ A I g
      slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt
      id sel := by
  intro cACont σCont evmCont locals dog mem rdata aw k C rd4701 hmem hAccounts
    hevmSigma0 hevmCreated hevmGenesis hevmBlocks hevmEnv hdogClean howe htab hlot
    hdog _husr hid hlocked hvow hsales hsourceReverted hsourceReturned
  exact clipperTakeNonzeroStoreContinuationEquiv (locals := locals) v hpatch hcode
    hdispatch hdec rd4701 hmem hAccounts hevmSigma0 hevmCreated hevmGenesis
    hevmBlocks hevmEnv hdogClean howe htab hlot hdog hid hidWord hlocked hvow hsales
    htabNe hlotNe hsourceReverted hsourceReturned hdepth hperm

end Benchmarks.Dss.Clipper
