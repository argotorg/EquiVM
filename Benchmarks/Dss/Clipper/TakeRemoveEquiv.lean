import Benchmarks.Dss.Clipper.TakeRemoveContinuationEVM
import Benchmarks.Dss.Clipper.YankSuccessSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- Common refinement argument for the internal `_remove` call reached by both
   zero-lot and zero-tab purchases.  The callers supply only how that internal
   call is embedded in their source continuation. -/
set_option maxHeartbeats 4000000 in
theorem clipperTakeRemoveEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    {σCont : AccountMap} {evmCont : EVM.State}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg contract I.calldata = some takeTransition)
    (hdec : config.externalABI.decodeCalldata?
      (List.map Param.name takeTransition.params)
      (transitionSignature takeTransition).paramTypes I.calldata =
        some (clipperTakeStore I))
    (rd8274 : RD fork code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8274⟩
      (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
        stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel]) mem aw out σCont k C)
    (hidWord : id = clipperYankArgWord I)
    (hmem : clipperTakeMemoryWF mem aw) (hperm : I.perm = true)
    (hAccounts : Eq σCont evmCont.accountMap)
    (hevmEnv : evmCont.executionEnv = I)
    (hsourceReverted :
      ExecFuncBody fork config
          { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
          evmCont removeFunction.body .reverted →
        ExecTransitionBody fork config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (clipperTakeStore I) takeTransition.body .reverted (immStore v))
    (hsourceReturned : ∀ {callee : Frame} {evmRemove : EVM.State},
      ExecFuncBody fork config
          { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
          evmCont removeFunction.body (.returned callee evmRemove none) →
        evmRemove.executionEnv.perm = true →
        ∃ finalFrame : Frame,
          ExecTransitionBody fork config contract
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (clipperTakeStore I) takeTransition.body
            (.returned finalFrame
              (Stele.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner
                ⟨13⟩ ⟨0⟩) none) (immStore v)) :
    runtimeRefinementFor fork config contract
      σ σ₀ g A I (immStore v) := by
  have howner : evmCont.executionEnv.codeOwner = I.codeOwner := by rw [hevmEnv]
  have hstorage (slot : UInt256) :
      solcSlotWord σCont I slot =
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner slot := by
    have hslot := congrArg (fun m => solcSlotWord m I slot) hAccounts
    simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      solcSlotWord, hevmEnv, hslot]
  apply RD.clipperTakeRemoveContinuationElim v hpatch rd8274 hidWord hmem hperm
  · intro hlen hinvalid
    have hlenStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
      rw [← hstorage]
      exact hlen
    have hremove := clipperYankRemoveEmptySourceReverts (fork := fork) v evmCont I hlenStele
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)
  · intro hlen hidEq hret
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    have hlenStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [u256_add_lnot_zero_eq_sub_one, hstorage]
    have hidEqStele : clipperYankArgWord I =
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidEq
    have hacc : ∃ acc, evmCont.accountMap.get?
        evmCont.executionEnv.codeOwner = some acc := by
      cases hfind : evmCont.accountMap.get? evmCont.executionEnv.codeOwner with
      | none =>
          exfalso
          apply hlenStele
          rw [Std.ExtTreeMap.get?_eq_getElem?] at hfind
          simp [Stele.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
      | some acc => exact ⟨acc, rfl⟩
    obtain ⟨acc, hacc⟩ := hacc
    let sourceLastIndex := UInt256.sub
      (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState
      (clipperYankRemovePopState evmCont sourceLastIndex) I
    let calleeFrame : Frame :=
      { contract := contract,
        locals := clipperYankRemoveMoveStore I sourceLastIndex
          (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
            (clipperYankActiveSlot sourceLastIndex)), immutables := immStore v }
    have hremove : ExecFuncBody fork config
        { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
        evmCont removeFunction.body (.returned calleeFrame evmRemove none) := by
      simpa [sourceLastIndex, evmRemove, calleeFrame] using
        clipperYankRemoveIdEqMoveSource (hperm := (congrArg ExecutionEnv.perm hevmEnv).trans hperm) v evmCont I hacc hlenStele hidEqStele
    obtain ⟨finalFrame, hbody⟩ := hsourceReturned hremove (by
      simpa (config := { zetaDelta := true }) only [clipperYankDeleteSaleState,
        clipperYankRemovePopState, storageStore_executionEnv] using
        (congrArg ExecutionEnv.perm hevmEnv).trans hperm)
    have hAccountsFinal :=
      clipperYankSuccessAccountMap_state_accounts_eq
        (σ := σCont) (τ := evmCont.accountMap) evmCont I lastIndex
        hAccounts rfl howner
    exact hret.reEquivExecutionGen hcode hdispatch hdec hbody
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
    let evmIndex := Stele.EVM.storageStore evmCont
      evmCont.executionEnv.codeOwner (clipperYankActiveSlot idx) move
    let evmMovePos := Stele.EVM.storageStore evmIndex
      evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
    have hlenStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [u256_add_lnot_zero_eq_sub_one, hstorage]
    have hidNeStele : clipperYankArgWord I ≠
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidNe
    have hidxBoundStele :
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat <
          (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat := by
      rw [← hstorage, ← hstorage]
      simpa [idx] using hidxBound
    have hmoveStele :
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) = move := by
      rw [← hlastIndexEq, ← hstorage]
    have hidxStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
      rw [← hstorage]
    have hmoveAccounts : Eq
        (clipperYankMoveAccountMap σCont I idx move) evmMovePos.accountMap := by
      simpa [evmIndex, evmMovePos] using
        clipperYankMoveAccountMap_state_accounts_eq
          (σ := σCont) (τ := evmCont.accountMap) evmCont I idx move
          hAccounts rfl howner
    have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
      simp [evmMovePos, evmIndex, storageStore_executionEnv, howner]
    have hstorageMove (slot : UInt256) :
        solcSlotWord (clipperYankMoveAccountMap σCont I idx move) I slot =
          Stele.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner slot := by
      have hslot := congrArg (fun m => solcSlotWord m I slot) hmoveAccounts
      simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord, hownerMovePos, hslot]
    have hlenAfterStele : Stele.EVM.storageLoad evmMovePos
        evmMovePos.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
      rw [← hstorageMove]
      simpa [lastIndex, move, idx] using hlenAfter
    have hremoveRaw := clipperYankRemoveIdNeMovePopEmptySourceReverts (fork := fork) (hperm := (congrArg ExecutionEnv.perm hevmEnv).trans hperm)
      v evmCont I hlenStele hidNeStele hidxBoundStele
    dsimp only at hremoveRaw
    have hremove := hremoveRaw (by
      simpa only [hmoveStele, hidxStele, evmIndex, evmMovePos] using hlenAfterStele)
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)
  · intro hlen hidNe hidxBound hlenAfter hret
    let lastIndex := solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σCont I (clipperYankActiveSlot lastIndex)
    let idx := solcSlotWord σCont I (clipperYankSalesPosSlot I)
    let σMove := clipperYankMoveAccountMap σCont I idx move
    let evmIndex := Stele.EVM.storageStore evmCont
      evmCont.executionEnv.codeOwner (clipperYankActiveSlot idx) move
    let evmMovePos := Stele.EVM.storageStore evmIndex
      evmIndex.executionEnv.codeOwner (clipperYankSalesMovePosSlot move) idx
    have hlenStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [u256_add_lnot_zero_eq_sub_one, hstorage]
    have hmoveStele :
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) = move := by
      rw [← hlastIndexEq, ← hstorage]
    have hidxStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner (clipperYankSalesPosSlot I) = idx := by
      rw [← hstorage]
    have hidNeStele : clipperYankArgWord I ≠
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [hmoveStele]
      simpa [lastIndex, move] using hidNe
    have hidxBoundStele :
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat <
          (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat := by
      rw [hidxStele, ← hstorage]
      simpa [idx] using hidxBound
    have hmoveAccounts : Eq σMove evmMovePos.accountMap := by
      simpa [σMove, evmIndex, evmMovePos] using
        clipperYankMoveAccountMap_state_accounts_eq
          (σ := σCont) (τ := evmCont.accountMap) evmCont I idx move
          hAccounts rfl howner
    have hownerMovePos : evmMovePos.executionEnv.codeOwner = I.codeOwner := by
      simp [evmMovePos, evmIndex, storageStore_executionEnv, howner]
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
    have hacc : ∃ acc, evmCont.accountMap.get?
        evmCont.executionEnv.codeOwner = some acc := by
      cases hfind : evmCont.accountMap.get? evmCont.executionEnv.codeOwner with
      | none =>
          exfalso
          apply hlenStele
          rw [Std.ExtTreeMap.get?_eq_getElem?] at hfind
          simp [Stele.EVM.storageLoad, State.lookupAccount, hfind, Option.option]
      | some acc => exact ⟨acc, rfl⟩
    obtain ⟨acc, hacc⟩ := hacc
    let popLastIndex := UInt256.sub
      (Stele.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState
      (clipperYankRemovePopState evmMovePos popLastIndex) I
    let calleeFrame : Frame :=
      { contract := contract,
        locals := clipperYankRemoveIndexStore I
          (UInt256.sub
            (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)
          move idx, immutables := immStore v }
    have hremoveRaw := clipperYankRemoveIdNeMoveSource (fork := fork) (hperm := (congrArg ExecutionEnv.perm hevmEnv).trans hperm)
      v evmCont I hacc hlenStele hidNeStele hidxBoundStele
    dsimp only at hremoveRaw
    have hremove : ExecFuncBody fork config
        { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
        evmCont removeFunction.body (.returned calleeFrame evmRemove none) := by
      have hremoveSource := hremoveRaw (by
        simpa only [hmoveStele, hidxStele, evmIndex, evmMovePos] using hlenAfterStele)
      simpa only [calleeFrame, evmRemove, popLastIndex, hmoveStele, hidxStele,
        evmIndex, evmMovePos] using hremoveSource
    obtain ⟨finalFrame, hbody⟩ := hsourceReturned hremove (by
      simpa (config := { zetaDelta := true }) only [clipperYankDeleteSaleState,
        clipperYankRemovePopState, storageStore_executionEnv] using
        (congrArg ExecutionEnv.perm hevmEnv).trans hperm)
    let lastIndexAfter := solcSlotWord σMove I ⟨11⟩ + UInt256.lnot ⟨0⟩
    have hlastIndexAfterEq : lastIndexAfter = popLastIndex := by
      rw [show lastIndexAfter = solcSlotWord σMove I ⟨11⟩ +
        UInt256.lnot ⟨0⟩ from rfl]
      rw [u256_add_lnot_zero_eq_sub_one, hstorageMove]
    have hAccountsFinal :=
      clipperYankSuccessAccountMap_state_accounts_eq
        (σ := σMove) (τ := evmMovePos.accountMap) evmMovePos I lastIndexAfter
        hmoveAccounts rfl hownerMovePos
    exact hret.reEquivExecutionGen hcode hdispatch hdec hbody
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
    have hlenStele : Stele.EVM.storageLoad evmCont
        evmCont.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hlen (by rw [hstorage]; exact hzero)
    have hlastIndexEq : lastIndex = UInt256.sub
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
      rw [show lastIndex = solcSlotWord σCont I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
      rw [u256_add_lnot_zero_eq_sub_one, hstorage]
    have hidNeStele : clipperYankArgWord I ≠
        Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩)
              ⟨1⟩)) := by
      rw [← hlastIndexEq, ← hstorage]
      simpa [lastIndex] using hidNe
    have hidxBoundStele :
        (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner ⟨11⟩).toNat ≤
          (Stele.EVM.storageLoad evmCont evmCont.executionEnv.codeOwner
            (clipperYankSalesPosSlot I)).toNat := by
      rw [← hstorage, ← hstorage]
      simpa using hidxBound
    have hremove := clipperYankRemoveIdNeMoveIndexOobSourceReverts (fork := fork)
      v evmCont I hlenStele hidNeStele hidxBoundStele
    exact hinvalid.reEquivExecutionInvalid hcode hdispatch hdec
      (hsourceReverted hremove)

end Benchmarks.Dss.Clipper
