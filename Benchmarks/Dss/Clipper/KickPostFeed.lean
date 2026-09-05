import Benchmarks.Dss.Clipper.KickFeedPriceSimulation
import Benchmarks.Dss.Clipper.RedoSuccessBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false

private theorem clipperKickStorageStore_originalAccounts (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

private theorem clipperKickStorageStore_genesisBlockHeader (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

private theorem clipperKickStorageStore_blocks (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem clipperKickVowAddress_eq_of_aligned
    {s0 evm : EVM.State} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {I : ExecutionEnv}
    (halign : ClipperKickCallAligned s0 cA σ I evm) :
    clipperKickSourceVowAddress evm =
      AccountAddress.ofNat (clipperRedoVowTarget σ I).toNat := by
  have hslot := accountMapEquiv_storage_findD halign.accounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hword : solcSlotWord σ I ⟨2⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ := by
    simpa [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, halign.executionEnv] using hslot
  simp only [clipperKickSourceVowAddress, clipperRedoVowTarget]
  rw [← hword]
  rw [u256_land_comm]

theorem clipperKickKprValue_eq_masked (I : ExecutionEnv) :
    clipperKickKprValue I =
      .address (AccountAddress.ofNat (clipperKickKprMaskedWord I).toNat) := by
  exact solcAddressValue_masked (clipperKickKprWord I)

inductive ClipperKickTailOutcome (v : ClipperImmutables) (code : ByteArray)
    (g : UInt256) (s0 : EVM.State) (I : ExecutionEnv)
    (evmLock sourceInit : EVM.State) (id : UInt256) : Prop
  | reverted
      (hsource : ExecBlock (config v)
        (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
        sourceInit (clipperKickAfterInitializationBody v) .reverted)
      (hevm : RDrev code (Sat256.ofUInt256 g) s0)
  | invalid
      (hsource : ExecBlock (config v)
        (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
        sourceInit (clipperKickAfterInitializationBody v) .reverted)
      (hevm : RDinvalid code (Sat256.ofUInt256 g) s0)
  | returned
      (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
      (sourceAfter : EVM.State) (frame : Frame)
      (hsource : ExecBlock (config v)
        (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
        sourceInit (clipperKickAfterInitializationBody v)
        (.returned frame sourceAfter
          (some [.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)])))
      (hevm : RDret code (Sat256.ofUInt256 g) s0 (cA, σ) id.toByteArray)
      (hcreated : sourceAfter.createdAccounts = cA)
      (haccounts : accountMapEquiv σ sourceAfter.accountMap)

theorem clipperKickAfterFeedTopPrefix
    (v : ClipperImmutables) (evmLock sourceInit sourceAfter evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256)
    (hgetFeed : ExecStmt (config v)
      (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
      sourceInit (.internalCall "getFeedPrice" [] "feedPrice")
      (.ok (Frame.mk (contract v)
        (clipperKickLocalsFeedPrice evmLock I feedPrice)) sourceAfter))
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad sourceAfter
        sourceAfter.executionEnv.codeOwner ⟨5⟩).toNat < UInt256.size)
    (htopEq : UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad sourceAfter
          sourceAfter.executionEnv.codeOwner ⟨5⟩)) clipperRayWord = top)
    (htopPos : 0 < top.toNat) {result : ExecResult}
    (htail : ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top))
      evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ] result)
    (hevmTop : evmTop = clipperKickSourceTopState evmLock sourceAfter top) :
    ExecBlock (config v)
      (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
      sourceInit (clipperKickAfterInitializationBody v) result := by
  exact clipperKickAfterInitializationSuccessPrefix
    v evmLock sourceInit sourceAfter evmTop I feedPrice top hgetFeed hmul
      htopEq htopPos hevmTop htail

theorem clipperKickFinishActive
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA0 : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σStart σ₀ : AccountMap} {A : Substate}
    {g : UInt256} {I : ExecutionEnv} {evmLock sourceInit evmTop : EVM.State}
    {feedPrice top id sel : UInt256} {R : List UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σTop : AccountMap}
    {memTop out : ByteArray} {k C : ℕ}
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hactive : clipperKickTipWord σTop I ≠ ⟨0⟩ ∨
      clipperKickChipWord σTop I ≠ ⟨0⟩)
    (hprefix : ∀ {result : ExecResult},
      ExecBlock (config v)
        (Frame.mk (contract v)
          (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top))
        evmTop
        [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
          .assign .storage lockedRef (.intLit 0), .return [.var "id"] ] result →
      ExecBlock (config v)
        (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
        sourceInit (clipperKickAfterInitializationBody v) result)
    (halignTop : ClipperKickCallAligned
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I)
      cA σTop I evmTop)
    (rd6203 : RD code I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) ⟨6203⟩
      (⟨0⟩ :: clipperKickChipWord σTop I :: clipperKickTipWord σTop I ::
        top :: ⟨1⟩ :: id :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I ::
        clipperKickTabWord I :: ⟨476⟩ :: sel :: R)
      memTop (UInt256.ofNat 6) out (cA, σTop) k C)
    (hmemTop : memTop.size = 192)
    (hreadTop : memTop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 100 ≤ 1024) :
    ClipperKickTailOutcome v code g
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) I
      evmLock sourceInit id := by
  have htip : clipperKickTipWord σTop I = clipperRedoTipSolmWord evmTop := by
    simpa [clipperKickTipWord, clipperRedoTipWord] using
      clipperRedoTipWord_eq_of_accountMapEquiv evmTop I
        halignTop.executionEnv halignTop.accounts
  have hchip : clipperKickChipWord σTop I = clipperRedoChipSolmWord evmTop := by
    simpa [clipperKickChipWord, clipperRedoChipWord] using
      clipperRedoChipWord_eq_of_accountMapEquiv evmTop I
        halignTop.executionEnv halignTop.accounts
  have hactiveSource : clipperRedoTipSolmWord evmTop ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmTop ≠ ⟨0⟩ := by
    rcases hactive with htipNe | hchipNe
    · exact Or.inl (by simpa [← htip] using htipNe)
    · exact Or.inr (by simpa [← hchip] using hchipNe)
  obtain ⟨k6222, C6222, rd6222⟩ := RD.clipperKickIncentiveActive
    v hpatch rd6203 hactive (by omega)
  obtain ⟨k8238, C8238, rd8238⟩ := RD.clipperKickIncentiveToWmul
    v hpatch rd6222 (by omega)
  by_cases hoverWmul : UInt256.size ≤
      (clipperKickChipWord σTop I).toNat * (clipperKickTabWord I).toNat
  · have hevm := RD.clipperRedoPayoutWmulOverflowReverts
      v hpatch rd8238 hoverWmul
        (by simp only [List.length_cons]; omega)
    have hoverSource : UInt256.size ≤ (clipperKickTabWord I).toNat *
        (clipperRedoChipSolmWord evmTop).toNat := by
      rw [← hchip, Nat.mul_comm]
      exact hoverWmul
    have htail := clipperKickIncentiveWmulReverts
      v evmLock evmTop I feedPrice top hactiveSource hoverSource
    exact .reverted (hprefix htail) hevm
  · have hmulWmul : (clipperKickChipWord σTop I).toNat *
        (clipperKickTabWord I).toNat < UInt256.size := by omega
    obtain ⟨k9258, C9258, rd9258⟩ :=
      RD.clipperKickIncentiveWmulToCheckedAdd
        v hpatch rd8238 hmulWmul
          (by simp only [List.length_cons]; omega)
    let chipCoin := UInt256.div
      (UInt256.mul (clipperKickChipWord σTop I) (clipperKickTabWord I))
      ⟨1000000000000000000⟩
    have hchipCoin : clipperKickSourceChipCoinWord evmTop I = chipCoin := by
      simp only [clipperKickSourceChipCoinWord, chipCoin, ← hchip,
        u256_mul_comm]
    by_cases hoverAdd : UInt256.size ≤
        (clipperKickTipWord σTop I).toNat + chipCoin.toNat
    · have hevm := RD.clipperRedoPayoutAddOverflowReverts
        v hpatch (by simpa [chipCoin] using rd9258) hoverAdd
          (by simp only [List.length_cons]; omega)
      have hoverSource : UInt256.size ≤
          (clipperRedoTipSolmWord evmTop).toNat +
            (clipperKickSourceChipCoinWord evmTop I).toNat := by
        simpa [← htip, hchipCoin] using hoverAdd
      have hwmulSource : (clipperKickTabWord I).toNat *
          (clipperRedoChipSolmWord evmTop).toNat < UInt256.size := by
        rw [← hchip, Nat.mul_comm]
        exact hmulWmul
      have htail := clipperKickIncentiveAddReverts
        v evmLock evmTop I feedPrice top hactiveSource hwmulSource hoverSource
      exact .reverted (hprefix htail) hevm
    · have hfitAdd : (clipperKickTipWord σTop I).toNat + chipCoin.toNat <
          UInt256.size := by omega
      obtain ⟨k6240, C6240, rd6240⟩ := RD.clipperKickIncentiveAddSuccess
        v hpatch (by simpa [chipCoin] using rd9258) hfitAdd
          (by simp only [List.length_cons]; omega)
      let coin := clipperKickTipWord σTop I + chipCoin
      obtain ⟨k6357, C6357, rd6357⟩ := RD.clipperKickIncentiveToSuckGuard
        v hpatch (by simpa [coin] using rd6240) hmemTop hreadTop (by omega)
      have hwmulSource : (clipperKickTabWord I).toNat *
          (clipperRedoChipSolmWord evmTop).toNat < UInt256.size := by
        rw [← hchip, Nat.mul_comm]
        exact hmulWmul
      have haddSource : (clipperRedoTipSolmWord evmTop).toNat +
          (clipperKickSourceChipCoinWord evmTop I).toNat < UInt256.size := by
        simpa [← htip, hchipCoin] using hfitAdd
      have hcoin : clipperKickSourceCoinWord evmTop I = coin := by
        simp [clipperKickSourceCoinWord, coin, ← htip, hchipCoin]
      by_cases hvat : extCodeSizeWord σTop (clipperRedoVatTarget v) = ⟨0⟩
      · have hevm := RD.clipperKickSuckNoCode
          v hpatch rd6357 hvat (by omega)
        have hnoCode := clipperKickNoCode_of_aligned halignTop
          (clipperRedoVatTargetAddress v).symm hvat
        have hsuck := clipperKickSuckNoCodeSource
          v evmLock evmTop I feedPrice top hnoCode
        have htail := clipperKickIncentiveSuckReverts
          v evmLock evmTop I feedPrice top hactiveSource hwmulSource
            haddSource hsuck
        exact .reverted (hprefix htail) hevm
      · obtain ⟨cASuck, σSuck, zSuck, outSuck, ASuck, k6373, C6373,
            rd6373, hcallSuck, houtSuck⟩ := RD.clipperKickSuckPostCall
          v hpatch (by simpa [coin] using rd6357) hvat hdepth hperm hmemTop
            (by omega)
        obtain ⟨σSuckSolm, ASuckSolm, evmSuck, hevmeq, hcallSuckSolm,
            halignSuck⟩ := clipperKickCallAligned_transport halignTop hcallSuck
        have hvow := clipperKickVowAddress_eq_of_aligned halignTop
        have hkpr := clipperKickKprValue_eq_masked I
        have hcallSuckSource : typedCallViaEVM (config v) evmTop
            (EVM.address v.vat) "suck" 0
            [.address (clipperKickSourceVowAddress evmTop),
              clipperKickKprValue I,
              .int (Int.ofNat (clipperKickSourceCoinWord evmTop I).toNat)]
            (zSuck, evmSuck, outSuck) true := by
          simpa [hvow, hkpr, hcoin, coin] using hcallSuckSolm
        have hcodeVat := clipperKickHasCode_of_aligned halignTop
          (clipperRedoVatTargetAddress v).symm hvat
        cases zSuck
        · have hevm := RD.clipperKickSuckCallFailure
            v hpatch (by simpa using rd6373) houtSuck
              (by simp only [List.length_cons]; omega)
          have hsuck := clipperKickSuckCallFailureSource
            v evmLock evmTop evmSuck I feedPrice top outSuck hcodeVat
              hcallSuckSource
          have htail := clipperKickIncentiveSuckReverts
            v evmLock evmTop I feedPrice top hactiveSource hwmulSource
              haddSource hsuck
          exact .reverted (hprefix htail) hevm
        · obtain ⟨k6394, C6394, rd6394⟩ := RD.clipperKickSuckCallSuccess
            v hpatch (by simpa using rd6373) (by omega)
          let memSuck := clipperRedoSuckCalldataMem σTop I
            (clipperKickKprMaskedWord I) coin memTop
          have hmemSuck : memSuck.size = 228 := by
            simpa [memSuck] using clipperKickSuckCalldataMem_size σTop I
              (clipperKickKprMaskedWord I) coin hmemTop
          have hreadSuck : memSuck.readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ := by
            simpa [memSuck] using clipperKickSuckCalldataMem_read64 σTop I
              (clipperKickKprMaskedWord I) coin hmemTop hreadTop
          have hevm := RD.clipperKickEventUnlockReturnFrom228
            v hpatch (by simpa [memSuck, coin] using rd6394)
              hmemSuck hreadSuck hperm (by omega)
          have hsuck := clipperKickSuckCallSuccessSource
            v evmLock evmTop evmSuck I feedPrice top outSuck hcodeVat
              hcallSuckSource
          have htail := clipperKickIncentiveSucceeds
            v evmLock evmTop evmSuck I feedPrice top hactiveSource
              hwmulSource haddSource hsuck
          let sourceFinal := Solm.EVM.storageStore evmSuck
            evmSuck.executionEnv.codeOwner ⟨13⟩ ⟨0⟩
          have hFinalAccounts := clipperKickUnlockedState_accountMapEquiv
            evmSuck I halignSuck.executionEnv halignSuck.accounts
          exact .returned cASuck
            (sstoreAccountMap I.codeOwner σSuck ⟨13⟩ ⟨0⟩) sourceFinal _
            (by simpa [sourceFinal, hevmeq] using hprefix htail) hevm
            (by
              calc
                sourceFinal.createdAccounts = evmSuck.createdAccounts :=
                  storageStore_createdAccounts _ _ _ _
                _ = cASuck := halignSuck.createdAccounts)
            (by simpa [sourceFinal, hevmeq] using hFinalAccounts)

theorem clipperKickFinishAfterFeedPrice
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA0 : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σStart σ₀ : AccountMap} {A : Substate}
    {g : UInt256} {I : ExecutionEnv} {evmLock sourceInit : EVM.State}
    {id sel : UInt256} {R : List UInt256}
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hslot : clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩ =
      clipperKickTopSlot id)
    (hov : R.length + 100 ≤ 1024)
    (hfeed : ClipperKickFeedPriceOutcome v code g
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) I
      (clipperKickLocalsActivePos evmLock I) sourceInit
      ⟨6061⟩ ⟨6069⟩ ⟨0⟩ ⟨1⟩
      (id :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: sel :: R)) :
    ClipperKickTailOutcome v code g
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) I
      evmLock sourceInit id := by
  let s0 := initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I
  cases hfeed with
  | reverted hsource hevm =>
      exact .reverted
        (clipperKickAfterInitializationGetFeedReverts v evmLock sourceInit I hsource)
        hevm
  | invalid hsource hevm =>
      exact .invalid
        (clipperKickAfterInitializationGetFeedReverts v evmLock sourceInit I hsource)
        hevm
  | returned feedPrice cA σ sourceAfter mem out k C hgetFeed halign hrd hmem
      hread64 =>
    obtain ⟨k9233, C9233, rd9233⟩ := RD.clipperKickGetFeedPriceToRmul
      v hpatch hrd (by omega)
    have hbuf := clipperKickSlotWord_eq_of_accountMapEquiv sourceAfter I ⟨5⟩
      halign.executionEnv halign.accounts
    by_cases hoverRmul : UInt256.size ≤
        (solcSlotWord σ I ⟨5⟩).toNat * feedPrice.toNat
    · have hevm := RD.clipperKickRmulOverflowReverts
        v hpatch rd9233 hoverRmul
          (by simp only [List.length_cons]; omega)
      have hoverSource : UInt256.size ≤ feedPrice.toNat *
          (Solm.EVM.storageLoad sourceAfter sourceAfter.executionEnv.codeOwner ⟨5⟩).toNat := by
        rw [← hbuf, Nat.mul_comm]
        exact hoverRmul
      exact .reverted
        (clipperKickAfterInitializationRmulReverts
          v evmLock sourceInit sourceAfter I feedPrice hgetFeed hoverSource)
        hevm
    · have hmulRmul : (solcSlotWord σ I ⟨5⟩).toNat * feedPrice.toNat <
          UInt256.size := by omega
      obtain ⟨k6069, C6069, rd6069⟩ := RD.clipperKickRmulSuccess
        v hpatch rd9233 hmulRmul
          (by simp only [List.length_cons]; omega)
      let top := UInt256.div (UInt256.mul (solcSlotWord σ I ⟨5⟩) feedPrice)
        clipperRayWord
      have htopSource : UInt256.div
          (UInt256.mul feedPrice
            (Solm.EVM.storageLoad sourceAfter sourceAfter.executionEnv.codeOwner ⟨5⟩))
          clipperRayWord = top := by
        simp only [top, ← hbuf, u256_mul_comm]
      have hmulSource : feedPrice.toNat *
          (Solm.EVM.storageLoad sourceAfter sourceAfter.executionEnv.codeOwner ⟨5⟩).toNat <
          UInt256.size := by
        rw [← hbuf, Nat.mul_comm]
        exact hmulRmul
      by_cases htopZero : top = ⟨0⟩
      · have hevm := RD.clipperKickTopZeroReverts
          v hpatch (by simpa [top] using rd6069) htopZero hmem hread64
            (by omega)
        exact .reverted
          (clipperKickAfterInitializationTopZeroReverts
            v evmLock sourceInit sourceAfter I feedPrice hgetFeed hmulSource
              (by rw [htopSource]; exact htopZero))
          hevm
      · have htopPos : 0 < top.toNat := Nat.pos_of_ne_zero
          (fun hz => htopZero (uint256_toNat_eq_zero hz))
        let σTop := clipperKickTopMap σ I id top
        obtain ⟨k6203, C6203, rd6203⟩ := RD.clipperKickTopPositiveToIncentive
          v hpatch (by simpa [top] using rd6069) htopPos hperm hmem
            (by omega)
        let evmTop := clipperKickSourceTopState evmLock sourceAfter top
        have hTopAccounts : accountMapEquiv σTop evmTop.accountMap := by
          exact clipperKickTopState_accountMapEquiv evmLock sourceAfter I id top
            halign.executionEnv hslot halign.accounts
        have halignTop : ClipperKickCallAligned s0 cA σTop I evmTop :=
          { accounts := hTopAccounts
            originalAccounts := by
              calc
                s0.σ₀ = sourceAfter.σ₀ := halign.originalAccounts
                _ = evmTop.σ₀ := by
                  symm
                  exact clipperKickStorageStore_originalAccounts _ _ _ _
            createdAccounts := by
              calc
                evmTop.createdAccounts = sourceAfter.createdAccounts :=
                  storageStore_createdAccounts _ _ _ _
                _ = cA := halign.createdAccounts
            genesisBlockHeader := by
              calc
                evmTop.genesisBlockHeader = sourceAfter.genesisBlockHeader :=
                  clipperKickStorageStore_genesisBlockHeader _ _ _ _
                _ = s0.genesisBlockHeader := halign.genesisBlockHeader
            blocks := by
              calc
                evmTop.blocks = sourceAfter.blocks :=
                  clipperKickStorageStore_blocks _ _ _ _
                _ = s0.blocks := halign.blocks
            executionEnv := by
              calc
                evmTop.executionEnv = sourceAfter.executionEnv :=
                  storageStore_executionEnv _ _ _ _
                _ = I := halign.executionEnv }
        have htip : clipperKickTipWord σTop I = clipperRedoTipSolmWord evmTop := by
          simpa [clipperKickTipWord, clipperRedoTipWord] using
            clipperRedoTipWord_eq_of_accountMapEquiv evmTop I
              halignTop.executionEnv halignTop.accounts
        have hchip : clipperKickChipWord σTop I = clipperRedoChipSolmWord evmTop := by
          simpa [clipperKickChipWord, clipperRedoChipWord] using
            clipperRedoChipWord_eq_of_accountMapEquiv evmTop I
              halignTop.executionEnv halignTop.accounts
        let memTop := twoWordHashMem id ⟨12⟩ mem
        have hmemTop : memTop.size = 192 := by
          exact (twoWordHashMem_size_of_ge_64 id ⟨12⟩ (by omega)).trans hmem
        have hreadTop : memTop.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          exact twoWordHashMem_read64_of_ge id ⟨12⟩ (by omega) hread64
        have hprefix {result : ExecResult}
            (htail : ExecBlock (config v)
              (Frame.mk (contract v)
                (clipperKickLocalsCoinZero evmLock evmTop I feedPrice top))
              evmTop
              [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
                .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
              result) :
            ExecBlock (config v)
              (Frame.mk (contract v) (clipperKickLocalsActivePos evmLock I))
              sourceInit (clipperKickAfterInitializationBody v) result := by
          exact clipperKickAfterFeedTopPrefix v evmLock sourceInit sourceAfter
            evmTop I feedPrice top hgetFeed hmulSource htopSource htopPos htail rfl
        by_cases htipZero : clipperKickTipWord σTop I = ⟨0⟩
        · by_cases hchipZero : clipperKickChipWord σTop I = ⟨0⟩
          · obtain ⟨k6394, C6394, rd6394⟩ := RD.clipperKickIncentiveInactive
              v hpatch (by simpa [σTop, htipZero, hchipZero, memTop] using rd6203)
              (by omega)
            have hevm := RD.clipperKickEventUnlockReturnFrom192
              v hpatch rd6394 hmemTop hreadTop hperm
              (by omega)
            have htail := clipperKickIncentiveInactiveTail
              v evmLock evmTop I feedPrice top (htip.symm.trans htipZero)
                (hchip.symm.trans hchipZero)
            have hsource := hprefix htail
            let sourceFinal := Solm.EVM.storageStore evmTop
              evmTop.executionEnv.codeOwner ⟨13⟩ ⟨0⟩
            have hFinalAccounts := clipperKickUnlockedState_accountMapEquiv
              evmTop I halignTop.executionEnv halignTop.accounts
            exact .returned cA
              (sstoreAccountMap I.codeOwner σTop ⟨13⟩ ⟨0⟩) sourceFinal _
              (by simpa [sourceFinal] using hsource) hevm
              (by
                calc
                  sourceFinal.createdAccounts = evmTop.createdAccounts :=
                    storageStore_createdAccounts _ _ _ _
                  _ = cA := halignTop.createdAccounts)
              (by simpa [sourceFinal] using hFinalAccounts)
          · exact clipperKickFinishActive v hpatch hdepth hperm
              (Or.inr hchipZero) hprefix halignTop
              (by simpa [σTop, memTop] using rd6203) hmemTop hreadTop hov
        · exact clipperKickFinishActive v hpatch hdepth hperm
            (Or.inl htipZero) hprefix halignTop
            (by simpa [σTop, memTop] using rd6203) hmemTop hreadTop hov

end Benchmarks.Dss.Clipper
