import Benchmarks.Dss.Flopper.Dent.Part7

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreKissCallFailureMoveCallerNeTicZero
    {cA cA' cAAsh cAKiss gh bl σ_evm σ_solm σ' σAsh σKiss σ₀ A A' AAsh Ain
      AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨0⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss, createdAccounts := cAKiss },
          outKiss) true)
    (houtKissSize : outKiss.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (true, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  let evmAshEvmBase : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
  let evmAshSolmBase : EVM.State := { evmAshSolm with substate := Ain }
  have hcallKissCreated :
      evmAshSolmBase.createdAccounts = evmAshEvmBase.createdAccounts := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase]
  have hcallKissEnv : evmAshSolmBase.executionEnv = evmAshEvmBase.executionEnv := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase, evmCallSolm, evmSolm, initState,
      hcallEnv]
  obtain ⟨σKissSolm, AKissSolm0, hkissCallSolmBase, _hpostKissAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmAshSolmBase)
      hkissCall
      (by simpa [evmAshEvmBase, evmAshSolmBase, evmAshSolm] using hpostAshAccounts)
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      hcallKissCreated
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by simp [evmAshSolmBase])
      hcallKissEnv
  have hdepthNeKissBase : evmAshSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissSolm, hkissCallSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hkissCallSolmBase hdepthNeKissBase
      evmAshSolm.substate
  let evmKissSolm : EVM.State :=
    { evmAshSolm with
        accountMap := σKissSolm, substate := AKissSolm, createdAccounts := cAKiss }
  have hguyAshEq :
      flopperAddressReturnWord packedSlot σAsh I =
        flopperAddressReturnWord packedSlot σAshSolm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAshAccounts packedSlot
  have hkissCallSolm :
      typedCallViaEVM config evmAshSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshSolm I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false, evmKissSolm, outKiss) true := by
    have hraw := hkissCallSolmRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissSolm, evmAshSolmBase, evmAshSolm, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hkissCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
        (dentGuyWord evmAshSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAshAccounts packedSlot hkissCodeSize
    simpa [evmAshSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_kissCallFailure_moveCallerNe_ticZero
      evmSolm evmCallSolm evmAshSolm evmKissSolm I outMove outAsh outKiss
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm houtAsh32
      hkissCodeSizeSolm hkissCallSolm
  have hrev := flopperDentX_kissCallFailure rd2833 houtKissSize
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAddOverflowMoveCallerNeTicZeroKissSuccess
    {cA cA' cAAsh cAKiss gh bl σ_evm σ_solm σ' σAsh σKiss σ₀ A A' AAsh Ain
      AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤
        (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner
            (dentRuntimeAfterGuyMap I.codeOwner σKiss I) I).toNat)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss, createdAccounts := cAKiss },
          outKiss) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (true, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  let evmAshEvmBase : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
  let evmAshSolmBase : EVM.State := { evmAshSolm with substate := Ain }
  have hcallKissCreated :
      evmAshSolmBase.createdAccounts = evmAshEvmBase.createdAccounts := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase]
  have hcallKissEnv : evmAshSolmBase.executionEnv = evmAshEvmBase.executionEnv := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase, evmCallSolm, evmSolm, initState,
      hcallEnv]
  obtain ⟨σKissSolm, AKissSolm0, hkissCallSolmBase, hpostKissAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmAshSolmBase)
      hkissCall
      (by simpa [evmAshEvmBase, evmAshSolmBase, evmAshSolm] using hpostAshAccounts)
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      hcallKissCreated
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by simp [evmAshSolmBase])
      hcallKissEnv
  have hdepthNeKissBase : evmAshSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissSolm, hkissCallSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hkissCallSolmBase hdepthNeKissBase
      evmAshSolm.substate
  let evmKissSolm : EVM.State :=
    { evmAshSolm with
        accountMap := σKissSolm, substate := AKissSolm, createdAccounts := cAKiss }
  have hguyAshEq :
      flopperAddressReturnWord packedSlot σAsh I =
        flopperAddressReturnWord packedSlot σAshSolm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAshAccounts packedSlot
  have hkissCallSolm :
      typedCallViaEVM config evmAshSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshSolm I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKissSolm, outKiss) true := by
    have hraw := hkissCallSolmRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissSolm, evmAshSolmBase, evmAshSolm, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hkissEnv : evmKissSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hkissCallSolm
    simpa [evmKissSolm, evmAshSolm, evmCallSolm, evmSolm, initState, hcallEnv] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_accountMapEquiv
      (I := I) (σ_evm := σKiss) (evmSolm := evmKissSolm)
      (by simpa [evmKissSolm] using hpostKissAccounts) hkissEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hkissEnv
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hkissCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
        (dentGuyWord evmAshSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAshAccounts packedSlot hkissCodeSize
    simpa [evmAshSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have haddOverflowSolm :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmKissSolm I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKissSolm I) I)).toNat := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hkissEnv, httl] using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_addOverflow_moveCallerNe_ticZero_kissSuccess
      evmSolm evmCallSolm evmAshSolm evmKissSolm I outMove outAsh outKiss
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm houtAsh32
      hkissCodeSizeSolm hkissCallSolm haddOverflowSolm
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_kissCallSuccessToTail (g := Sat256.ofUInt256 g) hperm rd2833
  have hrev :=
    flopperDentX_addOverflowFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddOverflow rd2889
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreSuccessMoveCallerNeTicZeroKissSuccess
    {cA cA' cAAsh cAKiss gh bl σ_evm σ_solm σ' σAsh σKiss σ₀ A A' AAsh Ain
      AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner
            (dentRuntimeAfterGuyMap I.codeOwner σKiss I) I).toNat <
        2 ^ 48)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          outMove) true)
    (hashCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss, createdAccounts := cAKiss },
          outKiss) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCallEvm : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := A', createdAccounts := cA' }
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, outMove) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  let evmCallSolmBase : EVM.State := { evmCallSolm with substate := A' }
  have hcallAshCreated :
      evmCallSolmBase.createdAccounts = evmCallEvm.createdAccounts := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm]
  have hcallAshEnv : evmCallSolmBase.executionEnv = evmCallEvm.executionEnv := by
    simp [evmCallSolmBase, evmCallSolm, evmCallEvm, evmSolm, initState, hcallEnv]
  obtain ⟨σAshSolm, AAshSolm0, hcallAshSolmBase, hpostAshAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmCallSolmBase)
      hashCall
      (by simpa [evmCallEvm, evmCallSolmBase, evmCallSolm] using hpostAccountsCall)
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      hcallAshCreated
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallEvm, evmCallSolmBase, evmCallSolm, evmSolm, initState])
      (by simp [evmCallSolmBase])
      hcallAshEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSolmBase, evmCallSolm, evmSolm, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshSolm, hcallAshSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hcallAshSolmBase hdepthNeBase
      evmCallSolm.substate
  let evmAshSolm : EVM.State :=
    { evmCallSolm with
        accountMap := σAshSolm, substate := AAshSolm, createdAccounts := cAAsh }
  have hguyMoveEq :
      flopperAddressReturnWord packedSlot σ' I =
        flopperAddressReturnWord packedSlot σ'_solm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAccountsCall packedSlot
  have hcallAshSolm :
      typedCallViaEVM config evmCallSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallSolm I).toNat)) "Ash" 0 []
        (true, evmAshSolm, outAsh) true := by
    simpa [evmAshSolm, evmCallSolmBase, evmCallSolm, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSolmRaw
  let evmAshEvmBase : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σAsh, substate := Ain, createdAccounts := cAAsh }
  let evmAshSolmBase : EVM.State := { evmAshSolm with substate := Ain }
  have hcallKissCreated :
      evmAshSolmBase.createdAccounts = evmAshEvmBase.createdAccounts := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase]
  have hcallKissEnv : evmAshSolmBase.executionEnv = evmAshEvmBase.executionEnv := by
    simp [evmAshSolmBase, evmAshSolm, evmAshEvmBase, evmCallSolm, evmSolm, initState,
      hcallEnv]
  obtain ⟨σKissSolm, AKissSolm0, hkissCallSolmBase, hpostKissAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmAshSolmBase)
      hkissCall
      (by simpa [evmAshEvmBase, evmAshSolmBase, evmAshSolm] using hpostAshAccounts)
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      hcallKissCreated
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by
        simp [evmAshEvmBase, evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm,
          initState, hcallEnv])
      (by simp [evmAshSolmBase])
      hcallKissEnv
  have hdepthNeKissBase : evmAshSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSolmBase, evmAshSolm, evmCallSolm, evmSolm, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissSolm, hkissCallSolmRaw⟩ :=
    dentTypedCallViaEVM_zero_setSubstate hkissCallSolmBase hdepthNeKissBase
      evmAshSolm.substate
  let evmKissSolm : EVM.State :=
    { evmAshSolm with
        accountMap := σKissSolm, substate := AKissSolm, createdAccounts := cAKiss }
  have hguyAshEq :
      flopperAddressReturnWord packedSlot σAsh I =
        flopperAddressReturnWord packedSlot σAshSolm I :=
    flopperAddressReturnWord_accountMapEquiv hpostAshAccounts packedSlot
  have hkissCallSolm :
      typedCallViaEVM config evmAshSolm
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshSolm I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKissSolm, outKiss) true := by
    have hraw := hkissCallSolmRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissSolm, evmAshSolmBase, evmAshSolm, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hkissEnv : evmKissSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hkissCallSolm
    simpa [evmKissSolm, evmAshSolm, evmCallSolm, evmSolm, initState, hcallEnv] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_accountMapEquiv
      (I := I) (σ_evm := σKiss) (evmSolm := evmKissSolm)
      (by simpa [evmKissSolm] using hpostKissAccounts) hkissEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hkissEnv
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmCallSolm.accountMap
        (dentGuyWord evmCallSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAccountsCall packedSlot hashCodeSize
    simpa [evmCallSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have hkissCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
        (dentGuyWord evmAshSolm I) ≠ ⟨0⟩ := by
    have hne :=
      flopperCodeSize_ne_accountMapEquiv_addressSlot
        hpostAshAccounts packedSlot hkissCodeSize
    simpa [evmAshSolm, dentGuyWord, packedSlot, hcallEnv] using hne
  have haddFitSolm :
      (dentNow48Word (dentAfterGuyStore evmKissSolm I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKissSolm I) I)).toNat <
        2 ^ 48 := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hkissEnv, httl] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        (.returned
          { contract := contract
            locals := dentKissRetTicLocals evmSolm
              (dentAfterGuyStore evmKissSolm I) I outAsh }
          (dentPostState (dentAfterGuyStore evmKissSolm I) I)
          none) := by
    exact flopperDentBodyReturns_success_moveCallerNe_ticZero_kissSuccess
      evmSolm evmCallSolm evmAshSolm evmKissSolm I outMove outAsh outKiss
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm hashCodeSizeSolm hcallAshSolm houtAsh32
      hkissCodeSizeSolm hkissCallSolm haddFitSolm
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_kissCallSuccessToTail (g := Sat256.ofUInt256 g) hperm rd2833
  have hret :=
    flopperDentX_successFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddFit rd2889
  have hpostAccounts :=
    dentRuntimeTailSuccessAccountMap_afterGuy_accountMapEquiv
      (I := I) hAfterGuy hkissEnv haddFit
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp only [dentPostState, dentAfterTicStore, dentAfterLotStore, dentAfterGuyStore,
        storageStore_createdAccounts, evmKissSolm])
    (by simpa [evmKissSolm] using hpostAccounts)
    (by
      simpa [dentTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAddOverflowMoveCallerNeTicNonzero
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ' I) I).toNat)
    (rd2545 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_accountMapEquiv
      (I := I) hpostAccountsCall hcallEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hcallEnv
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hticMove
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    rw [hword]
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv] using hzero
  have haddOverflowSolm :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmCallSolm I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmCallSolm I) I)).toNat := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hcallEnv, httl] using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_addOverflow_moveCallerNe_ticNonzero
      evmSolm evmCallSolm I out
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm haddOverflowSolm
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_moveSuccessTicNonzeroToTail
      (g := Sat256.ofUInt256 g) hperm hticMove rd2545
  have hrev :=
    flopperDentX_addOverflowFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddOverflow rd2889
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreSuccessMoveCallerNeTicNonzero
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I = flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hlotLt :
      (dentLotWord I).toNat <
        (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat)
    (hbegFit : (flopperSlotWord ⟨4⟩ σ_evm I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (flopperSlotWord (auctionLotSlot (dentIdWord I)) σ_evm I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hticMove :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ' I) I).toNat <
        2 ^ 48)
    (rd2545 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostAccountsCall⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hguyEq :
      flopperAddressReturnWord packedSlot σ_evm I =
        flopperAddressReturnWord packedSlot σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts packedSlot
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "move" 0
        [.address evmSolm.executionEnv.source,
          .address (AccountAddress.ofNat
            (flopperAddressReturnWord packedSlot σ_solm I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, packedSlot, hvatEq, hguyEq, hsrcEq] using
      hcallSolmRaw
  have hcallEnv : evmCallSolm.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallSolm
    simpa [evmSolm, initState] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_accountMapEquiv
      (I := I) hpostAccountsCall hcallEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hcallEnv
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot, hword] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    simpa [evmSolm, dentBidStoredWord, initState, hword] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    simpa [evmSolm, dentBegWord, initState, hword] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentLotStoredWord, initState, hword] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    have hbeg := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (dentIdWord I))
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState, hbeg, hlot] using hsuff
  have hcallerSolm :
      UInt256.ofNat evmSolm.executionEnv.source.val ≠ dentGuyWord evmSolm I := by
    intro heq
    apply hcaller
    rw [hguyEq]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hticMoveSolm : dentTicWord evmCallSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hticMove
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I)
      hpostAccountsCall packedSlot
    rw [hword]
    simpa [evmCallSolm, dentTicWord, packedSlot, hcallEnv] using hzero
  have haddFitSolm :
      (dentNow48Word (dentAfterGuyStore evmCallSolm I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmCallSolm I) I)).toNat <
        2 ^ 48 := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hcallEnv, httl] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        (.returned
          { contract := contract
            locals := dentMoveTicLocals evmSolm (dentAfterGuyStore evmCallSolm I) I }
          (dentPostState (dentAfterGuyStore evmCallSolm I) I)
          none) := by
    exact flopperDentBodyReturns_success_moveCallerNe_ticNonzero
      evmSolm evmCallSolm I out
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm
      (by simpa [evmSolm, dentVatWord, initState] using hcodeSizeSolm)
      hcallSolm hticMoveSolm haddFitSolm
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_moveSuccessTicNonzeroToTail
      (g := Sat256.ofUInt256 g) hperm hticMove rd2545
  have hret :=
    flopperDentX_successFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddFit rd2889
  have hpostAccounts :=
    dentRuntimeTailSuccessAccountMap_afterGuy_accountMapEquiv
      (I := I) hAfterGuy hcallEnv haddFit
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp only [dentPostState, dentAfterTicStore, dentAfterLotStore, dentAfterGuyStore,
        storageStore_createdAccounts, evmCallSolm])
    (by simpa [evmCallSolm] using hpostAccounts)
    (by
      simpa [dentTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperDentBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flopperDentX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_dent_none_short hsz4 hshort)

theorem flopperDentBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolm : dentLiveWord evmSolm ≠ ⟨1⟩ := by
    intro hbad
    apply hlive
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [hword]
    simpa [evmSolm, dentLiveWord, initState] using hbad
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_notLive evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm
  have hrev :=
    flopperDentX_notLive (g := Sat256.ofUInt256 g) hlive
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreGuyNotSet
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I = ⟨0⟩ := by
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentGuyWord, initState, packedSlot, hword] using hguy
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_guyNotSet evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
  have hrev :=
    flopperDentX_guyNotSet (g := Sat256.ofUInt256 g) hlive hguy
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreTicFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticNe : flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticLe :
      (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticNeSolm : dentTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hticNe
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentTicWord, initState, packedSlot] using hzero
  have hticLeSolm : (dentTicWord evmSolm I).toNat ≤ (dentTimestampWord evmSolm).toNat := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [evmSolm, dentTicWord, dentTimestampWord, initState, packedSlot, hword]
      using hticLe
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_ticFinished evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticNeSolm hticLeSolm
  have hrev :=
    flopperDentX_ticFinished (g := Sat256.ofUInt256 g) hlive hguy hticNe hticLe
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreEndFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendLe :
      (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := dentIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_solm I =
          flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I :=
      (flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dentIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, hword] using hzero
  have hendLeSolm : (dentEndWord evmSolm I).toNat ≤ (dentTimestampWord evmSolm).toNat := by
    have hword :
        flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_solm I =
          flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I :=
      (flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dentIdWord I))).symm
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState, hword]
      using hendLe
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_endFinished evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendLeSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flopperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memEnd := twoWordHashMem id ⟨1⟩ memTic
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        obtain ⟨_, _, rd1964⟩ :=
          flopperDentX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd2001⟩ := flopperDentX_toEndGtGuard rd1964
        exact flopperDentX_endFinishedFromGuard hendLe hmemEnd hreadEnd rd2001
    | inr hticZero =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memTicZero := twoWordHashMem id ⟨1⟩ memTic
        let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemTicZero : memTicZero.size = 96 := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadTicZero :
            memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
        obtain ⟨_, _, rd1964⟩ :=
          flopperDentX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd2001⟩ := flopperDentX_toEndGtGuard rd1964
        exact flopperDentX_endFinishedFromGuard hendLe hmemEnd hreadEnd rd2001
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreBidMismatch
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat ∨
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I).toNat)
    (hbid : dentBidWord I ≠ flopperSlotWord (auctionBidSlot (dentIdWord I)) σ_evm I)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    simpa [evmSolm, dentLiveWord, initState, hword] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_solm I =
          flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ_evm I :=
      (flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dentIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, hword] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    have hword :
        flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_solm I =
          flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ_evm I :=
      (flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (dentIdWord I))).symm
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState, hword] using hendGt
  have hbidSolm : dentBidWord I ≠ dentBidStoredWord evmSolm I := by
    intro heq
    apply hbid
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (dentIdWord I))
    rw [hword]
    simpa [evmSolm, dentBidStoredWord, initState] using heq
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_bidMismatch evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨memBid, _, _, hmemBid, hreadBid, rd2099⟩ :=
    flopperDentX_toBidEqGuardFromDecoded hlive hguy hticOk hendGt hdecoded
  have hrev := flopperDentX_bidMismatchFromGuard hbid hmemBid hreadBid rd2099
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

end Benchmarks.Dss.Flopper
