import Benchmarks.Dss.Clipper.TakeFluxCallbackEVM
import Benchmarks.Dss.Clipper.TakeNonzeroFromFluxEquiv
import Benchmarks.Dss.Clipper.TakeGenericCallbackSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Empty callback data has the same vat-flux and storage continuations as the
   ordinary path, but both implementations skip `clipperCall` immediately. -/
set_option maxHeartbeats 8000000 in
theorem clipperTakeFromFluxDataEmptyEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σPost : AccountMap} {evmPrice : EVM.State}
    {sliceLocals fluxLocals : Store}
    {price slice owe tab lot tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {baseMem rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (List.map Param.name takeTransition.params)
      (transitionSignature takeTransition).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd4223 : RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4223⟩
      (slice :: owe :: tab :: lot :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      baseMem (UInt256.ofNat 7) rdata σPost k C)
    (hbaseSize : baseMem.size = 196)
    (hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccountsPost : Eq σPost evmPrice.accountMap)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hdataLen : dataLen = ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
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
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v))
    (hsourceVatFailure : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM config evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true →
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v))
    (hsourceFluxSuccess : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM config evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true →
      ExecBlock config (Frame.mk contract sliceLocals (immStore v)) evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++
          clipperTakePostOweFluxStmts)
        (.ok (Frame.mk contract fluxLocals (immStore v)) evmVat))
    (hsourceCloseReverted :
      ExecBlock config (Frame.mk contract sliceLocals (immStore v)) evmPrice
        (clipperTakeAfterSliceStmts) .reverted →
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v))
    (hsourceCloseReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock config (Frame.mk contract sliceLocals (immStore v)) evmPrice
        (clipperTakeAfterSliceStmts) (.ok finalFrame finalEvm) →
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body
        (.returned finalFrame finalEvm none) (immStore v))
    (hcontinue : ClipperTakeStoreContinuationEquiv v code σ
      σ₀ A I g slice owe (UInt256.sub tab owe) (UInt256.sub lot slice) price tic
      packed stopped dataLen dataStart who max amt id sel)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeRefinementFor config contract
      σ σ₀ g A I (immStore v) := by
  let evmPriceEvm : EVM.State :=
    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σPost }
  have hvatCodeSolmOf
      (hne : Reasoning.Theory.extCodeSizeWord σPost (clipperTakeVatTarget v) ≠ ⟨0⟩) :
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat := by
    have hneEvm :
        Reasoning.Theory.extCodeSizeWord evmPrice.accountMap (clipperTakeVatTarget v) ≠
          ⟨0⟩ := by
      simpa only [← hAccountsPost] using hne
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (clipperTakeVatTargetAddress v).symm hneEvm
  have syncFlux {σVat : AccountMap} {AVat : Substate} {zVat : Bool} {outVat : ByteArray}
      (hcall : typedCallViaEVM config evmPriceEvm
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
          .int (Int.ofNat slice.toNat)]
        (zVat,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σVat, substate := AVat },
          outVat) true) :=
    typedCallViaEVM_syncFromState hAccountsPost
      (by simp [evmPriceEvm, initState, hevmPriceSigma0])



      (by simp [evmPriceEvm, initState, hevmPriceEnv]) hcall
  have closeRevert
      (hrev : RDrev code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      (hbody : ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperTakeStore I) takeTransition.body .reverted (immStore v)) :
      runtimeRefinementFor config contract
        σ σ₀ g A I (immStore v) :=
    hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
  apply RD.clipperTakeFluxDataEmptyElim v hpatch rd4223 hbaseSize hbaseRead64
    hdataLen hdepth hperm (by simp)
  · intro hnoCode hrev
    have hnoCodeSolm : (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
      have hnoCodeEvm :
          Reasoning.Theory.extCodeSizeWord evmPrice.accountMap
            (clipperTakeVatTarget v) = ⟨0⟩ := by
        simpa only [← hAccountsPost] using hnoCode
      simpa [State.lookupAccount] using
        extCodeSizeWord_zero_lookup_code_zero
          (clipperTakeVatTargetAddress v).symm hnoCodeEvm
    exact closeRevert hrev (hsourceVatNoCode hnoCodeSolm)
  · intro σVat outVat AVat hcall hvatCode hrev
    obtain ⟨evmVat, hcallSolm, _, _, _, _, _, _⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    exact closeRevert hrev (hsourceVatFailure (hvatCodeSolmOf hvatCode)
      (by simpa [hevmPriceEnv] using hcallSolm))
  · intro σVat outVat AVat memVat awVat kVat CVat hcall hvatCode hmem
      rd4701
    obtain ⟨evmVat, hcallSolm, hAccountsVat, hevmVatSigma0, hevmVatEnv⟩ :=
      syncFlux (by simpa [evmPriceEvm] using hcall)
    have hcallSolm' : typedCallViaEVM config evmPrice (EVM.address v.vat)
        "flux" 0 [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true := by
      simpa [hevmPriceEnv] using hcallSolm
    have hflux := hsourceFluxSuccess (hvatCodeSolmOf hvatCode) hcallSolm'
    let dogLocals := fluxLocals.insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
    have hletDog : ExecStmt config (Frame.mk contract fluxLocals (immStore v)) evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok (Frame.mk contract dogLocals (immStore v)) evmVat) := by
      simpa [dogLocals] using
        (ExecStmt.letDecl (cfg := config)
          (solm := Frame.mk contract fluxLocals (immStore v)) (evm := evmVat)
          (name := "dog_") (ty := some addr) (expr := .storage dogRef)
          (value := .address
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
          (by simpa [clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat fluxLocals hfluxDogAbsent))
    have hdogWord : UInt256.land (solcSlotWord σVat I ⟨1⟩) solcAddrMask =
        clipperTakeDogEVMWord evmVat :=
      clipperTakeDogWord_eq hAccountsVat hevmVatEnv
    have hwhoLocal : dogLocals.get? "who" =
        some (.address (AccountAddress.ofNat who.toNat)) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxWho
    have hdataLocal : dogLocals.get? "data" = some (clipperTakeDataValue I) := by
      simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxData
    have hdogLocal : dogLocals.get? "dog_" = some (.address
        (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simp [dogLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have hguard := clipperTakeGenericCallbackGuardFalseDataEmpty
      (v := v) (evm := evmVat) hdataLocal hwhoLocal hdogLocal
      (hdataLenEq.symm.trans hdataLen)
    have hcb := clipperTakeCallbackSkipOfEval hguard
    have sourceReverted
        (htail : ExecBlock config (Frame.mk contract dogLocals (immStore v)) evmVat
          (checkedExternalCallStmts vatExpr "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts) .reverted) :=
      hsourceCloseReverted
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb) htail)
    have sourceReturned {finalFrame : Frame} {finalEvm : EVM.State}
        (htail : ExecBlock config (Frame.mk contract dogLocals (immStore v)) evmVat
          (checkedExternalCallStmts vatExpr "move" (.intLit 0)
              [sender, .storage vowRef, .var "owe"] "_moveRet" ++
            clipperTakeAfterMoveStmts) (.ok finalFrame finalEvm)) :=
      hsourceCloseReturned
        (clipperTakeAfterSliceOfPrefixAndContinuation hflux hletDog
          (by simpa [clipperTakeCallbackStmt, dogLocals] using hcb) htail)
    apply hcontinue (locals := dogLocals) rd4701 hmem hAccountsVat
      hevmVatSigma0 hevmVatEnv
    · simpa [hdogWord] using solcAddrMask_clean_left
        (solcAddrMask_result_canonical (solcSlotWord σVat I ⟨1⟩))
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxOwe
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxTab
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxLot
    · simp [dogLocals, hdogWord, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxUsr
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxId
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxLocked
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxVow
    · simpa [dogLocals, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hfluxSales
    · exact sourceReverted
    · exact sourceReturned

end Benchmarks.Dss.Clipper
