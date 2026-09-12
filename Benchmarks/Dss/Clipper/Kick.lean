import Benchmarks.Dss.Clipper.KickDepthLimit
import Benchmarks.Dss.Clipper.Invalid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false

/-! The top-level coupling for `kick`.  The source and compiler traces are
split at the point where the auction has been initialized; the external-call
and post-call portions are coupled by `ClipperKickTailOutcome`. -/

private theorem clipperKickConnectOutcome
    (v : ClipperImmutables) {code : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σEvm σSolm σ₀ : AccountMap} {A : Substate}
    {g : UInt256} {I : ExecutionEnv} {evmLock sourceInit : EVM.State}
    {id : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (kickTransition v))
    (hdecode : decodeCalldataWithMode (config v).abiDecodeMode
      ((kickTransition v).params.map Param.name)
      (transitionSignature (kickTransition v)).paramTypes I.calldata =
        some (clipperKickStore I))
    (hprefix : ∀ {result : ExecResult},
      ExecBlock (config v)
          (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
          sourceInit (clipperKickAfterInitializationBody v) result →
        ExecBlock (config v) (Frame.mk (contract v) (clipperKickStore I))
          (initState cA gh bl σSolm σ₀ (Sat256.ofUInt256 g) A I)
          (kickTransition v).body result)
    (hid : clipperKickSourceIdWord evmLock = id)
    (houtcome : ClipperKickTailOutcome v code g
      (initState cA gh bl σEvm σ₀ (Sat256.ofUInt256 g) A I) I
      evmLock sourceInit id) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σEvm σSolm σ₀ g A I := by
  cases houtcome with
  | reverted hsource hevm =>
      have hbody : ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σSolm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperKickStore I) (kickTransition v).body .reverted :=
        ExecFuncBody.execBlockRevert (hprefix hsource)
      exact hevm.reEquivExecutionRevert hcode hdispatch hdecode hbody
  | invalid hsource hevm =>
      have hbody : ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σSolm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperKickStore I) (kickTransition v).body .reverted :=
        ExecFuncBody.execBlockRevert (hprefix hsource)
      exact RDinvalid.reEquivExecutionInvalid hcode hevm hdispatch hdecode hbody
  | returned cAFinal σFinal sourceAfter frame hsource hevm hcreated haccounts =>
      have hbody : ExecTransitionBody (config v) (contract v)
          (initState cA gh bl σSolm σ₀ (Sat256.ofUInt256 g) A I)
          (clipperKickStore I) (kickTransition v).body
          (.returned frame sourceAfter
            (some [.int (Int.ofNat id.toNat)])) := by
        apply ExecFuncBody.execBlockRet
        simpa [hid] using hprefix hsource
      have henc : returnEquiv id.toByteArray
          (some [.int (Int.ofNat id.toNat)]) (kickTransition v).returnType := by
        rw [show (kickTransition v).returnType = [uint256] from rfl]
        exact returnEquiv_of_encode
          (by simpa [uint256] using uint256ReturnEncoding id)
      exact hevm.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
        hbody hcreated.symm haccounts henc

private theorem clipperKickStore_originalAccounts (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

private theorem clipperKickStore_genesisBlockHeader (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

private theorem clipperKickStore_blocks (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

private theorem clipperKickSourceInitializedState_originalAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickSourceInitializedState evm I).σ₀ = evm.σ₀ := by
  simp [clipperKickSourceInitializedState, clipperKickSourceSalesUsrState,
    clipperKickSourceSalesLotState, clipperKickSourceSalesTabState,
    clipperKickSourceSalesPosState, clipperKickSourceActiveState,
    clipperKickSourceActiveLengthState, clipperKickSourceIdState,
    clipperKickStore_originalAccounts]

private theorem clipperKickSourceInitializedState_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickSourceInitializedState evm I).createdAccounts =
      evm.createdAccounts := by
  simp [clipperKickSourceInitializedState, clipperKickSourceSalesUsrState,
    clipperKickSourceSalesLotState, clipperKickSourceSalesTabState,
    clipperKickSourceSalesPosState, clipperKickSourceActiveState,
    clipperKickSourceActiveLengthState, clipperKickSourceIdState,
    storageStore_createdAccounts]

private theorem clipperKickSourceInitializedState_genesisBlockHeader
    (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickSourceInitializedState evm I).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp [clipperKickSourceInitializedState, clipperKickSourceSalesUsrState,
    clipperKickSourceSalesLotState, clipperKickSourceSalesTabState,
    clipperKickSourceSalesPosState, clipperKickSourceActiveState,
    clipperKickSourceActiveLengthState, clipperKickSourceIdState,
    clipperKickStore_genesisBlockHeader]

private theorem clipperKickSourceInitializedState_blocks
    (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickSourceInitializedState evm I).blocks = evm.blocks := by
  simp [clipperKickSourceInitializedState, clipperKickSourceSalesUsrState,
    clipperKickSourceSalesLotState, clipperKickSourceSalesTabState,
    clipperKickSourceSalesPosState, clipperKickSourceActiveState,
    clipperKickSourceActiveLengthState, clipperKickSourceIdState,
    clipperKickStore_blocks]

private theorem clipperKickSourceInitializedState_executionEnv
    (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickSourceInitializedState evm I).executionEnv = evm.executionEnv := by
  simp [clipperKickSourceInitializedState, clipperKickSourceSalesUsrState,
    clipperKickSourceSalesLotState, clipperKickSourceSalesTabState,
    clipperKickSourceSalesPosState, clipperKickSourceActiveState,
    clipperKickSourceActiveLengthState, clipperKickSourceIdState,
    storageStore_executionEnv]

set_option maxHeartbeats 8000000 in
theorem clipperKickBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hStorageWF : clipperStorageWF σ_evm I) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 13) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some (kickTransition v) :=
    clipperDispatch_kick v hsel
  have hreachEntry := clipperReachKickEntry (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) v hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz132 : 132 ≤ I.calldata.size
  · have hdecode := clipperDecode_kick_ok v (I := I) hsz132
    obtain ⟨_, _, rd5361⟩ := clipperKickX_decoded
      (v := v) (g := Sat256.ofUInt256 g) hpatch hsz132 hsize hreachEntry
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hvalue : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
      simpa [evmSolm, initState] using hwv
    have hsrc : evmSolm.executionEnv.source = I.source := by
      simp [evmSolm, initState]
    have hInitialAccounts : accountMapEquiv σ_evm evmSolm.accountMap := by
      simpa [evmSolm, initState] using hAccounts
    have hauthEq : clipperRelyAuthWord σ_evm I =
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
          (clipperRelyAuthStorageSlot I) := by
      simpa [clipperRelyAuthWord] using
        clipperKickSlotWord_eq_of_accountMapEquiv evmSolm I
          (clipperRelyAuthStorageSlot I) (by simp [evmSolm, initState])
          hInitialAccounts
    have connectRevert
        (hsource : ExecBlock (config v)
          (Frame.mk (contract v) (clipperKickStore I)) evmSolm
          (kickTransition v).body .reverted)
        (hevm : RDrev code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
        runtimeEquivalenceFor (config v) (contract v)
          cA gh bl σ_evm σ_solm σ₀ g A I := by
      have hbody : ExecTransitionBody (config v) (contract v) evmSolm
          (clipperKickStore I) (kickTransition v).body .reverted :=
        ExecFuncBody.execBlockRevert hsource
      simpa [evmSolm] using
        hevm.reEquivExecutionRevert hcode hdispatch hdecode hbody
    by_cases hauth : clipperRelyAuthWord σ_evm I = ⟨1⟩
    · have hauthSource : Solm.EVM.storageLoad evmSolm
          evmSolm.executionEnv.codeOwner (clipperRelyAuthStorageSlot I) = ⟨1⟩ := by
        rw [← hauthEq]
        exact hauth
      obtain ⟨_, _, rd5443⟩ := clipperKickX_authorized v hpatch hauth rd5361
      have hlockEq : solcSlotWord σ_evm I ⟨13⟩ =
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨13⟩ :=
        clipperKickSlotWord_eq_of_accountMapEquiv evmSolm I ⟨13⟩
          (by simp [evmSolm, initState]) hInitialAccounts
      by_cases hlocked : solcSlotWord σ_evm I ⟨13⟩ = ⟨0⟩
      · have hlockedSource : Solm.EVM.storageLoad evmSolm
            evmSolm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩ := by
          rw [← hlockEq]
          exact hlocked
        obtain ⟨_, _, rd5520⟩ := clipperKickX_lockOpen v hpatch hlocked rd5443
        let σLock := sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩
        let evmLock := clipperKickLockedState evmSolm
        have hLockAccounts : accountMapEquiv σLock evmLock.accountMap := by
          simpa [σLock, evmLock, clipperKickLockedState, storageStore_accountMap,
            evmSolm, initState] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
        have henvLock : evmLock.executionEnv = I := by
          simp [evmLock, clipperKickLockedState, evmSolm, initState,
            storageStore_executionEnv]
        have hstoppedEq : solcSlotWord σLock I ⟨14⟩ =
            Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨14⟩ :=
          clipperKickSlotWord_eq_of_accountMapEquiv evmLock I ⟨14⟩
            henvLock hLockAccounts
        by_cases hstopped : (solcSlotWord σLock I ⟨14⟩).toNat < 1
        · have hstoppedSource :
              (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨14⟩).toNat < 1 := by
            rw [← hstoppedEq]
            exact hstopped
          obtain ⟨_, _, rd5609⟩ := clipperKickX_lockAndStoppedOpen
            (σ := σ_evm) v hpatch hperm (by simpa [σLock] using hstopped) rd5520
          by_cases htab : 0 < (clipperKickTabWord I).toNat
          · obtain ⟨_, _, rd5681⟩ := clipperKickX_tabPositive
              (σ := σLock) v hpatch htab (by simpa [σLock] using rd5609)
            by_cases hlot : 0 < (clipperKickLotWord I).toNat
            · obtain ⟨_, _, rd5753⟩ := clipperKickX_lotPositive
                (σ := σLock) v hpatch hlot rd5681
              by_cases husr : clipperKickUsrMaskedWord I ≠ ⟨0⟩
              · obtain ⟨_, _, rd5831⟩ := clipperKickX_usrPositive
                  (σ := σLock) v hpatch husr rd5753
                have hidEq : clipperKickSourceIdWord evmLock =
                    clipperKickIdWord σLock I := by
                  simp only [clipperKickSourceIdWord, clipperKickIdWord]
                  rw [← clipperKickSlotWord_eq_of_accountMapEquiv evmLock I ⟨10⟩
                    henvLock hLockAccounts]
                by_cases hid : clipperKickIdWord σLock I ≠ ⟨0⟩
                · obtain ⟨_, _, rd5913⟩ := clipperKickX_idPositive
                    (σ := σLock) v hpatch hperm hid rd5831
                  obtain ⟨_, _, rd8728⟩ := clipperKickX_initializeAuction
                    (σ := σLock) v hpatch hperm rd5913
                  let sourceInit := clipperKickSourceInitializedState evmLock I
                  have hlenEq : clipperKickSourceActiveLengthWord evmLock =
                      solcSlotWord σ_evm I ⟨11⟩ := by
                    calc
                      clipperKickSourceActiveLengthWord evmLock =
                          Solm.EVM.storageLoad evmLock
                            evmLock.executionEnv.codeOwner ⟨11⟩ := by
                        simp only [clipperKickSourceActiveLengthWord,
                          clipperKickSourceIdState]
                        exact storageLoad_storageStore_ne evmLock
                          evmLock.executionEnv.codeOwner (by decide)
                      _ = solcSlotWord σLock I ⟨11⟩ :=
                        (clipperKickSlotWord_eq_of_accountMapEquiv evmLock I ⟨11⟩
                          henvLock hLockAccounts).symm
                      _ = solcSlotWord σ_evm I ⟨11⟩ := by
                        simpa [σLock, solcSlotWord] using
                          sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner
                            ⟨11⟩ ⟨13⟩ ⟨1⟩ (by decide)
                  have hlen : (clipperKickSourceActiveLengthWord evmLock).toNat + 1 <
                      UInt256.size := by
                    rw [hlenEq]
                    unfold clipperStorageWF at hStorageWF
                    omega
                  have hpresentSolm : ∃ acc,
                      evmSolm.accountMap.find? I.codeOwner = some acc := by
                    cases hacc : evmSolm.accountMap.find? I.codeOwner with
                    | none =>
                        exfalso
                        have hownerSolm : evmSolm.executionEnv.codeOwner =
                            I.codeOwner := by simp [evmSolm, initState]
                        have hacc' : evmSolm.accountMap.find?
                            evmSolm.executionEnv.codeOwner = none := by
                          simpa [hownerSolm] using hacc
                        have hzeroLoad : Solm.EVM.storageLoad evmSolm
                            evmSolm.executionEnv.codeOwner
                              (clipperRelyAuthStorageSlot I) = ⟨0⟩ := by
                          unfold Solm.EVM.storageLoad State.lookupAccount
                          rw [hacc']
                          rfl
                        rw [hzeroLoad] at hauthSource
                        exact (by decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hauthSource
                    | some acc => exact ⟨acc, rfl⟩
                  obtain ⟨accSolm, haccSolm⟩ := hpresentSolm
                  obtain ⟨accLock, haccLock⟩ := clipperKickStorageStore_present
                    evmSolm evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                      (by simpa [evmSolm, initState] using haccSolm)
                  have hpresentLock : ∃ acc,
                      evmLock.accountMap.find? I.codeOwner = some acc := by
                    exact ⟨accLock, by
                      simpa [evmLock, clipperKickLockedState, evmSolm, initState,
                        storageStore_executionEnv] using haccLock⟩
                  have hInitAccounts : accountMapEquiv
                      (clipperKickInitializedMap σLock I) sourceInit.accountMap := by
                    simpa [sourceInit] using
                      clipperKickInitializedState_accountMapEquiv evmLock I
                        henvLock hpresentLock hLockAccounts
                  have halignInit : ClipperKickCallAligned
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      cA (clipperKickInitializedMap σLock I) I sourceInit :=
                    { accounts := hInitAccounts
                      originalAccounts := by
                        calc
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀ =
                              σ₀ := rfl
                          _ = evmSolm.σ₀ := rfl
                          _ = evmLock.σ₀ := by
                            simpa [evmLock, clipperKickLockedState] using
                              (clipperKickStore_originalAccounts evmSolm
                                evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩).symm
                          _ = sourceInit.σ₀ := by
                            simpa [sourceInit] using
                              (clipperKickSourceInitializedState_originalAccounts
                                evmLock I).symm
                      createdAccounts := by
                        calc
                          sourceInit.createdAccounts = evmLock.createdAccounts := by
                            simpa [sourceInit] using
                              clipperKickSourceInitializedState_createdAccounts evmLock I
                          _ = evmSolm.createdAccounts := by
                            simpa [evmLock, clipperKickLockedState] using
                              storageStore_createdAccounts evmSolm
                                evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                          _ = cA := rfl
                      genesisBlockHeader := by
                        calc
                          sourceInit.genesisBlockHeader = evmLock.genesisBlockHeader := by
                            simpa [sourceInit] using
                              clipperKickSourceInitializedState_genesisBlockHeader evmLock I
                          _ = evmSolm.genesisBlockHeader := by
                            simpa [evmLock, clipperKickLockedState] using
                              clipperKickStore_genesisBlockHeader evmSolm
                                evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                          _ = (initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I).genesisBlockHeader := rfl
                      blocks := by
                        calc
                          sourceInit.blocks = evmLock.blocks := by
                            simpa [sourceInit] using
                              clipperKickSourceInitializedState_blocks evmLock I
                          _ = evmSolm.blocks := by
                            simpa [evmLock, clipperKickLockedState] using
                              clipperKickStore_blocks evmSolm
                                evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
                          _ = (initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I).blocks := rfl
                      executionEnv := by
                        calc
                          sourceInit.executionEnv = evmLock.executionEnv := by
                            simpa [sourceInit] using
                              clipperKickSourceInitializedState_executionEnv evmLock I
                          _ = I := henvLock }
                  have hslot : clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩ =
                      clipperKickTopSlot (clipperKickIdWord σLock I) := by
                    simpa [clipperKickTopSlot] using congrArg (fun slot => slot + ⟨4⟩)
                      (clipperKickSalesBaseSlot_eq evmLock σLock I hidEq)
                  have hprefix : ∀ {result : ExecResult},
                      ExecBlock (config v)
                          (Frame.mk (contract v)
                            (clipperKickLocalsActivePos evmLock I))
                          sourceInit (clipperKickAfterInitializationBody v) result →
                        ExecBlock (config v) (Frame.mk (contract v) (clipperKickStore I))
                          evmSolm (kickTransition v).body result := by
                    intro result hafter
                    exact clipperKickSourcePrefix v evmSolm I hvalue hsrc hauthSource
                      hlockedSource hstoppedSource htab hlot husr
                      (by rw [hidEq]; exact hid) hlen hafter
                  have houtcome : ClipperKickTailOutcome v code g
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
                      evmLock sourceInit (clipperKickIdWord σLock I) := by
                    by_cases hdepth : I.depth.val < 1024
                    · have hfeed := clipperKickSimulateGetFeedPrice
                        (callerLocals := clipperKickLocalsActivePos evmLock I)
                        v hpatch rd8728
                        halignInit hdepth hperm
                        (clipperKickSalesHashMem_size σLock I)
                        (clipperKickSalesHashMem_read64 σLock I)
                        (clipperKickJumpDest6061 v hpatch) (by simp)
                      exact clipperKickFinishAfterFeedPrice v hpatch hdepth hperm
                        hslot (by simp) hfeed
                    · have hdepthEq : I.depth = (1024 : Fin 1025) := by
                        have hval : I.depth.val = 1024 := by
                          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                          omega
                        apply Fin.ext
                        simpa using hval
                      by_cases hspotter : extCodeSizeWord
                          (clipperKickInitializedMap σLock I)
                          (clipperSpotterTarget (clipperKickInitializedMap σLock I) I) = ⟨0⟩
                      · have hevm := RD.clipperKickGetFeedPriceSpotterIlksNoCode
                            v hpatch rd8728 hspotter
                            (clipperKickSalesHashMem_size σLock I)
                            (clipperKickSalesHashMem_read64 σLock I) (by simp)
                        have haddr := clipperKickSpotterAddress_eq_of_aligned halignInit
                        have hnoCode := clipperKickNoCode_of_aligned halignInit
                          haddr hspotter
                        have hcall := clipperGetFeedPriceCallRevertsSpotterIlksNoCode
                          v sourceInit (clipperKickLocalsActivePos evmLock I)
                            "feedPrice" hnoCode
                        exact .reverted
                          (clipperKickAfterInitializationGetFeedReverts
                            v evmLock sourceInit I hcall) hevm
                      · exact clipperKickDepthLimitReverts v hpatch hdepthEq hspotter
                          halignInit rd8728
                          (clipperKickSalesHashMem_size σLock I)
                          (clipperKickSalesHashMem_read64 σLock I) (by simp)
                  exact clipperKickConnectOutcome v hcode hdispatch hdecode
                    (by
                      intro result hafter
                      simpa [evmSolm] using hprefix hafter)
                    hidEq houtcome
                · have hidZero : clipperKickIdWord σLock I = ⟨0⟩ := by
                    simpa using hid
                  have hsource := clipperKickSourceRevertsId v evmSolm I hvalue hsrc
                    hauthSource hlockedSource hstoppedSource htab hlot husr
                    (by rw [hidEq]; exact hidZero)
                  have hevm := clipperKickX_idZero (σ := σLock) v hpatch hperm
                    hidZero rd5831
                  exact connectRevert hsource hevm
              · have husrZero : clipperKickUsrMaskedWord I = ⟨0⟩ := by
                  simpa using husr
                have hsource := clipperKickSourceRevertsUsr v evmSolm I hvalue hsrc
                  hauthSource hlockedSource hstoppedSource htab hlot husrZero
                have hevm := clipperKickX_usrZero (σ := σLock) v hpatch husrZero rd5753
                exact connectRevert hsource hevm
            · have hsource := clipperKickSourceRevertsLot v evmSolm I hvalue hsrc
                hauthSource hlockedSource hstoppedSource htab hlot
              have hevm := clipperKickX_lotZero (σ := σLock) v hpatch hlot rd5681
              exact connectRevert hsource hevm
          · have hsource := clipperKickSourceRevertsTab v evmSolm I hvalue hsrc
              hauthSource hlockedSource hstoppedSource htab
            have hevm := clipperKickX_tabZero (σ := σLock) v hpatch htab
              (by simpa [σLock] using rd5609)
            exact connectRevert hsource hevm
        · have hstoppedGe : 1 ≤ (solcSlotWord σLock I ⟨14⟩).toNat := by omega
          have hsource := clipperKickSourceRevertsStopped v evmSolm I hvalue hsrc
            hauthSource hlockedSource (by rw [← hstoppedEq]; exact hstoppedGe)
          have hevm := clipperKickX_stopped (σ := σ_evm) v hpatch hperm
            (by simpa [σLock] using hstoppedGe) rd5520
          exact connectRevert hsource hevm
      · have hlockedSource : Solm.EVM.storageLoad evmSolm
            evmSolm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩ := by
          intro hz
          exact hlocked (by rw [hlockEq, hz])
        have hsource := clipperKickSourceRevertsLocked v evmSolm I hvalue hsrc
          hauthSource hlockedSource
        have hevm := clipperKickX_locked v hpatch hlocked rd5443
        exact connectRevert hsource hevm
    · have hauthSource : Solm.EVM.storageLoad evmSolm
          evmSolm.executionEnv.codeOwner (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩ := by
        intro hone
        exact hauth (by rw [hauthEq, hone])
      have hsource := clipperKickSourceRevertsUnauthorized v evmSolm I hvalue hsrc
        hauthSource
      have hevm := clipperKickX_unauthorized v hpatch hauth rd5361
      exact connectRevert hsource hevm
  · have hshort : I.calldata.size < 132 := by omega
    exact (clipperKickX_shortarg (v := v) (g := Sat256.ofUInt256 g)
      hpatch hsz4 hsize hshort hreachEntry).reEquivDecodingFailed
        hcode hdispatch (clipperDecode_kick_none_short v hsz4 hshort)

end Benchmarks.Dss.Clipper
