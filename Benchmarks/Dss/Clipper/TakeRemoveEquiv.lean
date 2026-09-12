import Benchmarks.Dss.Clipper.TakeRemoveContinuationEVM
import Benchmarks.Dss.Clipper.YankSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Common refinement argument for the internal `_remove` call reached by both
   zero-lot and zero-tab purchases.  The callers supply only how that internal
   call is embedded in their source continuation. -/
set_option maxHeartbeats 4000000 in
theorem clipperTakeRemoveEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA0 cACont gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σCont : AccountMap} {evmCont : EVM.State}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd8274 : RD code I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8274⟩
      (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
        stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel]) mem aw out (cACont, σCont) k C)
    (hidWord : id = clipperYankArgWord I)
    (hmem : clipperTakeMemoryWF mem aw) (hperm : I.perm = true)
    (hAccounts : accountMapEquiv σCont evmCont.accountMap)
    (hevmCreated : evmCont.createdAccounts = cACont)
    (hevmEnv : evmCont.executionEnv = I)
    (hsourceReverted :
      ExecFuncBody (config v)
          { contract := contract v, locals := clipperYankRemoveStore I }
          evmCont removeFunction.body .reverted →
        ExecTransitionBody (config v) (contract v)
          (initState cA0 gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) (takeTransition v).body .reverted)
    (hsourceReturned : ∀ {callee : Frame} {evmRemove : EVM.State},
      ExecFuncBody (config v)
          { contract := contract v, locals := clipperYankRemoveStore I }
          evmCont removeFunction.body (.returned callee evmRemove none) →
        ∃ finalFrame : Frame,
          ExecTransitionBody (config v) (contract v)
            (initState cA0 gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (clipperTakeStore I) (takeTransition v).body
            (.returned finalFrame
              (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner
                ⟨13⟩ ⟨0⟩) none)) :
    runtimeEquivalenceFor (config v) (contract v)
      cA0 gh bl σ_evm σ_solm σ₀ g A I := by
  have howner : evmCont.executionEnv.codeOwner = I.codeOwner := by rw [hevmEnv]
  have hstorage (slot : UInt256) :
      solcSlotWord σCont I slot =
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner slot := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hevmEnv, hslot]
  apply RD.clipperTakeRemoveContinuationElim v hpatch rd8274 hidWord hmem hperm
  · intro hlen hinvalid
    have hlenSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
      rw [← hstorage]
      exact hlen
    have hremove := clipperYankRemoveEmptySourceReverts v evmCont I hlenSolm
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)
  · intro hlen hidEq hret
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    have hlenSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [clipperYankLenAddLnotZero_eq_subOne, hstorage]
    have hidEqSolm : clipperYankArgWord I =
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidEq
    have hacc : ∃ acc, evmCont.accountMap.find?
        evmCont.executionEnv.codeOwner = some acc := by
      cases hfind : evmCont.accountMap.find? evmCont.executionEnv.codeOwner with
      | none =>
          exfalso
          apply hlenSolm
          simp [Solm.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
      | some acc => exact ⟨acc, rfl⟩
    obtain ⟨acc, hacc⟩ := hacc
    let sourceLastIndex := UInt256.sub
      (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState
      (clipperYankRemovePopState evmCont sourceLastIndex) I
    let calleeFrame : Frame :=
      { contract := contract v,
        locals := clipperYankRemoveMoveStore I sourceLastIndex
          (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
            (clipperYankActiveSlot sourceLastIndex)) }
    have hremove : ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I }
        evmCont removeFunction.body (.returned calleeFrame evmRemove none) := by
      simpa [sourceLastIndex, evmRemove, calleeFrame] using
        clipperYankRemoveIdEqMoveSource v evmCont I hacc hlenSolm hidEqSolm
    obtain ⟨finalFrame, hbody⟩ := hsourceReturned hremove
    have hAccountsFinal :=
      clipperYankSuccessAccountMap_state_accountMapEquiv
        (σ := σCont) (τ := evmCont.accountMap) evmCont I lastIndex
        hAccounts rfl howner
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdec hbody
      (by
        simp [evmRemove, sourceLastIndex, clipperYankDeleteSaleState,
          clipperYankRemovePopState, storageStore_createdAccounts, hevmCreated])
      (by
        simpa [lastIndex, sourceLastIndex, hlastIndexEq, evmRemove,
          clipperYankSuccessAccountMap] using hAccountsFinal)
      (by
        simpa [takeTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            rfl rfl (by native_decide)))
  · intro hlen hidNe hidxBound hlenAfter hinvalid
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σCont I (clipperYankActiveSlot lastIndex)
    let idx := solcSlotWord σCont I (clipperYankSalesPosSlot I)
    let evmIndex := Solm.EVM.storageStore evmCont
      evmCont.executionEnv.codeOwner (clipperYankActiveSlot idx) move
    let evmMovePos := Solm.EVM.storageStore evmIndex
      evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
    have hlenSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [clipperYankLenAddLnotZero_eq_subOne, hstorage]
    have hidNeSolm : clipperYankArgWord I ≠
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidNe
    have hidxBoundSolm :
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat <
          (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat := by
      rw [← hstorage, ← hstorage]
      simpa [idx] using hidxBound
    have hmoveSolm :
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) = move := by
      rw [← hlastIndexEq, ← hstorage]
    have hidxSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
      rw [← hstorage]
    have hmoveAccounts : accountMapEquiv
        (clipperYankMoveAccountMap σCont I idx move) evmMovePos.accountMap := by
      simpa [evmIndex, evmMovePos] using
        clipperYankMoveAccountMap_state_accountMapEquiv
          (σ := σCont) (τ := evmCont.accountMap) evmCont I idx move
          hAccounts rfl howner
    have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
      simp [evmMovePos, evmIndex, storageStore_executionEnv, howner]
    have hstorageMove (slot : UInt256) :
        solcSlotWord (clipperYankMoveAccountMap σCont I idx move) I slot =
          Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
      have hslot := accountMapEquiv_storage_findD hmoveAccounts I.codeOwner slot ⟨0⟩
      simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hownerMovePos, hslot]
    have hlenAfterSolm : Solm.EVM.storageLoad evmMovePos
        evmMovePos.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
      rw [← hstorageMove]
      simpa [lastIndex, move, idx] using hlenAfter
    have hremoveRaw := clipperYankRemoveIdNeMovePopEmptySourceReverts
      v evmCont I hlenSolm hidNeSolm hidxBoundSolm
    dsimp only at hremoveRaw
    have hremove := hremoveRaw (by
      simpa only [hmoveSolm, hidxSolm, evmIndex, evmMovePos] using hlenAfterSolm)
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)
  · intro hlen hidNe hidxBound hlenAfter hret
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σCont I (clipperYankActiveSlot lastIndex)
    let idx := solcSlotWord σCont I (clipperYankSalesPosSlot I)
    let σMove := clipperYankMoveAccountMap σCont I idx move
    let evmIndex := Solm.EVM.storageStore evmCont
      evmCont.executionEnv.codeOwner (clipperYankActiveSlot idx) move
    let evmMovePos := Solm.EVM.storageStore evmIndex
      evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
    have hlenSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [clipperYankLenAddLnotZero_eq_subOne, hstorage]
    have hmoveSolm :
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) = move := by
      rw [← hlastIndexEq, ← hstorage]
    have hidxSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
      rw [← hstorage]
    have hidNeSolm : clipperYankArgWord I ≠
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [hmoveSolm]
      simpa [lastIndex, move] using hidNe
    have hidxBoundSolm :
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat <
          (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat := by
      rw [hidxSolm, ← hstorage]
      simpa [idx] using hidxBound
    have hmoveAccounts : accountMapEquiv σMove evmMovePos.accountMap := by
      simpa [σMove, evmIndex, evmMovePos] using
        clipperYankMoveAccountMap_state_accountMapEquiv
          (σ := σCont) (τ := evmCont.accountMap) evmCont I idx move
          hAccounts rfl howner
    have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
      simp [evmMovePos, evmIndex, storageStore_executionEnv, howner]
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
    have hacc : ∃ acc, evmCont.accountMap.find?
        evmCont.executionEnv.codeOwner = some acc := by
      cases hfind : evmCont.accountMap.find? evmCont.executionEnv.codeOwner with
      | none =>
          exfalso
          apply hlenSolm
          simp [Solm.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
      | some acc => exact ⟨acc, rfl⟩
    obtain ⟨acc, hacc⟩ := hacc
    let popLastIndex := UInt256.sub
      (Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState
      (clipperYankRemovePopState evmMovePos popLastIndex) I
    let calleeFrame : Frame :=
      { contract := contract v,
        locals := clipperYankRemoveIndexStore I
          (UInt256.sub
            (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)
          move idx }
    have hremoveRaw := clipperYankRemoveIdNeMoveSource
      v evmCont I hacc hlenSolm hidNeSolm hidxBoundSolm
    dsimp only at hremoveRaw
    have hremove : ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I }
        evmCont removeFunction.body (.returned calleeFrame evmRemove none) := by
      have hremoveSource := hremoveRaw (by
        simpa only [hmoveSolm, hidxSolm, evmIndex, evmMovePos] using hlenAfterSolm)
      simpa only [calleeFrame, evmRemove, popLastIndex, hmoveSolm, hidxSolm,
        evmIndex, evmMovePos] using hremoveSource
    obtain ⟨finalFrame, hbody⟩ := hsourceReturned hremove
    let lastIndexAfter := solcSlotWord σMove I ⟨11⟩ + UInt256.lnot ⟨0⟩
    have hlastIndexAfterEq : lastIndexAfter = popLastIndex := by
      rw [show lastIndexAfter = solcSlotWord σMove I ⟨11⟩ +
        UInt256.lnot ⟨0⟩ from rfl]
      rw [clipperYankLenAddLnotZero_eq_subOne, hstorageMove]
    have hAccountsFinal :=
      clipperYankSuccessAccountMap_state_accountMapEquiv
        (σ := σMove) (τ := evmMovePos.accountMap) evmMovePos I lastIndexAfter
        hmoveAccounts rfl hownerMovePos
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdec hbody
      (by
        simp [evmRemove, popLastIndex, evmMovePos, evmIndex,
          clipperYankDeleteSaleState, clipperYankRemovePopState,
          storageStore_createdAccounts, hevmCreated])
      (by
        simpa [lastIndex, move, idx, σMove, lastIndexAfter,
          hlastIndexAfterEq, evmRemove, popLastIndex,
          clipperYankSuccessAccountMap] using hAccountsFinal)
      (by
        simpa [takeTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            rfl rfl (by native_decide)))
  · intro hlen hidNe hidxBound hinvalid
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    have hlenSolm : Solm.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [clipperYankLenAddLnotZero_eq_subOne, hstorage]
    have hidNeSolm : clipperYankArgWord I ≠
        Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidNe
    have hidxBoundSolm :
        (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat ≤
          (Solm.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
            (clipperYankSalesPosSlot I)).toNat := by
      rw [← hstorage, ← hstorage]
      simpa using hidxBound
    have hremove := clipperYankRemoveIdNeMoveIndexOobSourceReverts
      v evmCont I hlenSolm hidNeSolm hidxBoundSolm
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)

end Benchmarks.Dss.Clipper
