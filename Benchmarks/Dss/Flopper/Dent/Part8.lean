import Benchmarks.Dss.Flopper.Dent.Part7

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreKissCallFailureMoveCallerNeTicZero
    {σ σ' σAsh σKiss σ₀ A A' AAsh Ain AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨0⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss σKiss k C)
    (hcall :
      typedCallViaEVM fork config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          outMove) true)
    (hashCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A' }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss },
          outKiss) true)
    (houtKissSize : outKiss.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let σ'_stele := σ'
  let A'_stele := A'
  have hcallSteleRaw := hcall
  have hpostAccountsCall : σ' = σ'_stele := rfl
  let evmCallStele : EVM.State :=
    { evmStele with accountMap := σ'_stele, substate := A'_stele }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallStele :
      typedCallViaEVM fork config evmStele
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address evmStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (solcAddressSlotWord packedSlot σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallStele, outMove) true := by
    simpa [evmStele, evmCallStele, packedSlot, hsrcEq] using
      hcallSteleRaw
  have hcallEnv : evmCallStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallStele
    simpa [evmStele, initState] using h
  let evmCallSteleBase : EVM.State := { evmCallStele with substate := A' }
  let σAshStele := σAsh
  let AAshStele0 := AAsh
  have hcallAshSteleBase := hashCall
  have hpostAsrfl : σAsh = σAshStele := rfl
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSteleBase, evmCallStele, evmStele, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshStele, hcallAshSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallAshSteleBase hdepthNeBase
      evmCallStele.substate
  let evmAshStele : EVM.State :=
    { evmCallStele with
        accountMap := σAshStele, substate := AAshStele }
  have hguyMoveEq :
      solcAddressSlotWord packedSlot σ' I =
        solcAddressSlotWord packedSlot σ'_stele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAccountsCall
  have hcallAshStele :
      typedCallViaEVM fork config evmCallStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallStele I).toNat)) "Ash" 0 []
        (true, evmAshStele, outAsh) true := by
    simpa [evmAshStele, evmCallSteleBase, evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSteleRaw
  let evmAshSteleBase : EVM.State := { evmAshStele with substate := Ain }
  let σKissStele := σKiss
  let AKissStele0 := AKiss
  have hkissCallSteleBase := hkissCall
  have hdepthNeKissBase : evmAshSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSteleBase, evmAshStele, evmCallStele, evmStele, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissStele, hkissCallSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hkissCallSteleBase hdepthNeKissBase
      evmAshStele.substate
  let evmKissStele : EVM.State :=
    { evmAshStele with
        accountMap := σKissStele, substate := AKissStele }
  have hguyAshEq :
      solcAddressSlotWord packedSlot σAsh I =
        solcAddressSlotWord packedSlot σAshStele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAsrfl
  have hkissCallStele :
      typedCallViaEVM fork config evmAshStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshStele I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false, evmKissStele, outKiss) true := by
    have hraw := hkissCallSteleRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissStele, evmAshSteleBase, evmAshStele, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidStele : dentBidWord I = dentBidStoredWord evmStele I := by
    simpa [evmStele, dentBidStoredWord, initState] using hbid
  have hlotLtStele :
      (dentLotWord I).toNat < (dentLotStoredWord evmStele I).toNat := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotLt
  have hbegFitStele :
      (dentBegWord evmStele).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmStele, dentBegWord, initState] using hbegFit
  have hlotOneFitStele :
      (dentLotStoredWord evmStele I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotOneFit
  have hsuffStele :
      (dentBegLotWord evmStele I).toNat ≤ (dentLotOneWord evmStele I).toNat := by
    simpa [evmStele, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerStele :
      UInt256.ofNat evmStele.executionEnv.source.val ≠ dentGuyWord evmStele I := by
    intro heq
    apply hcaller
    simpa [evmStele, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩ :=
    hcodeSize
  have hticMoveStele : dentTicWord evmCallStele I = ⟨0⟩ := by
    have hword := congrArg (fun accounts => uint48Offset20Word packedSlot accounts I) hpostAccountsCall
    simpa [evmCallStele, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmCallStele.accountMap
        (dentGuyWord evmCallStele I) ≠ ⟨0⟩ := by
    simpa [evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAccountsCall] using hashCodeSize
  have hkissCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmAshStele.accountMap
        (dentGuyWord evmAshStele I) ≠ ⟨0⟩ := by
    simpa [evmAshStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAsrfl] using hkissCodeSize
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_kissCallFailure_moveCallerNe_ticZero
      evmStele evmCallStele evmAshStele evmKissStele I outMove outAsh outKiss
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
      hcallerStele
      (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
      hcallStele hticMoveStele hashCodeSizeStele hcallAshStele houtAsh32
      hkissCodeSizeStele hkissCallStele
  have hrev := flopperDentX_kissCallFailure rd2833 houtKissSize
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAddOverflowMoveCallerNeTicZeroKissSuccess
    {σ σ' σAsh σKiss σ₀ A A' AAsh Ain AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤
        (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner
            (dentRuntimeAfterGuyMap I.codeOwner σKiss I) I).toNat)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss σKiss k C)
    (hcall :
      typedCallViaEVM fork config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          outMove) true)
    (hashCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A' }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss },
          outKiss) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let σ'_stele := σ'
  let A'_stele := A'
  have hcallSteleRaw := hcall
  have hpostAccountsCall : σ' = σ'_stele := rfl
  let evmCallStele : EVM.State :=
    { evmStele with accountMap := σ'_stele, substate := A'_stele }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallStele :
      typedCallViaEVM fork config evmStele
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address evmStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (solcAddressSlotWord packedSlot σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallStele, outMove) true := by
    simpa [evmStele, evmCallStele, packedSlot, hsrcEq] using
      hcallSteleRaw
  have hcallEnv : evmCallStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallStele
    simpa [evmStele, initState] using h
  let evmCallSteleBase : EVM.State := { evmCallStele with substate := A' }
  let σAshStele := σAsh
  let AAshStele0 := AAsh
  have hcallAshSteleBase := hashCall
  have hpostAsrfl : σAsh = σAshStele := rfl
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSteleBase, evmCallStele, evmStele, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshStele, hcallAshSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallAshSteleBase hdepthNeBase
      evmCallStele.substate
  let evmAshStele : EVM.State :=
    { evmCallStele with
        accountMap := σAshStele, substate := AAshStele }
  have hguyMoveEq :
      solcAddressSlotWord packedSlot σ' I =
        solcAddressSlotWord packedSlot σ'_stele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAccountsCall
  have hcallAshStele :
      typedCallViaEVM fork config evmCallStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallStele I).toNat)) "Ash" 0 []
        (true, evmAshStele, outAsh) true := by
    simpa [evmAshStele, evmCallSteleBase, evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSteleRaw
  let evmAshSteleBase : EVM.State := { evmAshStele with substate := Ain }
  let σKissStele := σKiss
  let AKissStele0 := AKiss
  have hkissCallSteleBase := hkissCall
  have hpostKissAccounts : σKiss = σKissStele := rfl
  have hdepthNeKissBase : evmAshSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSteleBase, evmAshStele, evmCallStele, evmStele, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissStele, hkissCallSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hkissCallSteleBase hdepthNeKissBase
      evmAshStele.substate
  let evmKissStele : EVM.State :=
    { evmAshStele with
        accountMap := σKissStele, substate := AKissStele }
  have hguyAshEq :
      solcAddressSlotWord packedSlot σAsh I =
        solcAddressSlotWord packedSlot σAshStele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAsrfl
  have hkissCallStele :
      typedCallViaEVM fork config evmAshStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshStele I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKissStele, outKiss) true := by
    have hraw := hkissCallSteleRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissStele, evmAshSteleBase, evmAshStele, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hkissEnv : evmKissStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hkissCallStele
    simpa [evmKissStele, evmAshStele, evmCallStele, evmStele, initState, hcallEnv] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_eq_afterGuyStore
      (I := I) (σ := σKiss) (evmStele := evmKissStele)
      (by simpa [evmKissStele] using hpostKissAccounts) hkissEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hkissEnv
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidStele : dentBidWord I = dentBidStoredWord evmStele I := by
    simpa [evmStele, dentBidStoredWord, initState] using hbid
  have hlotLtStele :
      (dentLotWord I).toNat < (dentLotStoredWord evmStele I).toNat := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotLt
  have hbegFitStele :
      (dentBegWord evmStele).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmStele, dentBegWord, initState] using hbegFit
  have hlotOneFitStele :
      (dentLotStoredWord evmStele I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotOneFit
  have hsuffStele :
      (dentBegLotWord evmStele I).toNat ≤ (dentLotOneWord evmStele I).toNat := by
    simpa [evmStele, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerStele :
      UInt256.ofNat evmStele.executionEnv.source.val ≠ dentGuyWord evmStele I := by
    intro heq
    apply hcaller
    simpa [evmStele, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩ :=
    hcodeSize
  have hticMoveStele : dentTicWord evmCallStele I = ⟨0⟩ := by
    have hword := congrArg (fun accounts => uint48Offset20Word packedSlot accounts I) hpostAccountsCall
    simpa [evmCallStele, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmCallStele.accountMap
        (dentGuyWord evmCallStele I) ≠ ⟨0⟩ := by
    simpa [evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAccountsCall] using hashCodeSize
  have hkissCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmAshStele.accountMap
        (dentGuyWord evmAshStele I) ≠ ⟨0⟩ := by
    simpa [evmAshStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAsrfl] using hkissCodeSize
  have haddOverflowStele :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmKissStele I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKissStele I) I)).toNat := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hkissEnv, httl] using haddOverflow
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have hstatic := permSplit_false hp
      (flopperDentX_kissCallSuccessToTailSplit (g := Sat256.ofUInt256 g) rd2833)
    have hsource := (flopperDentBodyReturns_success_moveCallerNe_ticZero_kissSuccessSplit
        evmStele evmCallStele evmAshStele evmKissStele I outMove outAsh outKiss
        (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
        hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
        hcallerStele
        (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
        hcallStele hticMoveStele hashCodeSizeStele hcallAshStele houtAsh32
        hkissCodeSizeStele hkissCallStele).2 hp
    exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_addOverflow_moveCallerNe_ticZero_kissSuccess (hperm := hperm)
      evmStele evmCallStele evmAshStele evmKissStele I outMove outAsh outKiss
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
      hcallerStele
      (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
      hcallStele hticMoveStele hashCodeSizeStele hcallAshStele houtAsh32
      hkissCodeSizeStele hkissCallStele haddOverflowStele
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_kissCallSuccessToTail (g := Sat256.ofUInt256 g) hperm rd2833
  have hrev :=
    flopperDentX_addOverflowFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddOverflow rd2889
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreSuccessMoveCallerNeTicZeroKissSuccess
    {σ σ' σAsh σKiss σ₀ A A' AAsh Ain AKiss I}
    {g : UInt256} {sel : UInt256} {memKiss outMove outAsh outKiss : ByteArray}
    {k C : ℕ}
    (hcode : I.code = flopperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hkissCodeSize :
      Reasoning.Theory.extCodeSizeWord σAsh
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠ ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner
            (dentRuntimeAfterGuyMap I.codeOwner σKiss I) I).toNat <
        2 ^ 48)
    (hdepth : I.depth.val < 1024)
    (rd2833 : RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
      (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) outKiss σKiss k C)
    (hcall :
      typedCallViaEVM fork config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          outMove) true)
    (hashCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A' }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
        "Ash" 0 []
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAsh, substate := AAsh },
          outAsh) true)
    (houtAsh32 : 32 ≤ outAsh.size)
    (hkissCall :
      typedCallViaEVM fork config
        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σAsh, substate := Ain }
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σKiss, substate := AKiss },
          outKiss) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let σ'_stele := σ'
  let A'_stele := A'
  have hcallSteleRaw := hcall
  have hpostAccountsCall : σ' = σ'_stele := rfl
  let evmCallStele : EVM.State :=
    { evmStele with accountMap := σ'_stele, substate := A'_stele }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallStele :
      typedCallViaEVM fork config evmStele
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address evmStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (solcAddressSlotWord packedSlot σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallStele, outMove) true := by
    simpa [evmStele, evmCallStele, packedSlot, hsrcEq] using
      hcallSteleRaw
  have hcallEnv : evmCallStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallStele
    simpa [evmStele, initState] using h
  let evmCallSteleBase : EVM.State := { evmCallStele with substate := A' }
  let σAshStele := σAsh
  let AAshStele0 := AAsh
  have hcallAshSteleBase := hashCall
  have hpostAsrfl : σAsh = σAshStele := rfl
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepth
    norm_num at hdepth
  have hdepthNeBase : evmCallSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmCallSteleBase, evmCallStele, evmStele, initState, hcallEnv] using hdepthNeI
  obtain ⟨AAshStele, hcallAshSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallAshSteleBase hdepthNeBase
      evmCallStele.substate
  let evmAshStele : EVM.State :=
    { evmCallStele with
        accountMap := σAshStele, substate := AAshStele }
  have hguyMoveEq :
      solcAddressSlotWord packedSlot σ' I =
        solcAddressSlotWord packedSlot σ'_stele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAccountsCall
  have hcallAshStele :
      typedCallViaEVM fork config evmCallStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmCallStele I).toNat)) "Ash" 0 []
        (true, evmAshStele, outAsh) true := by
    simpa [evmAshStele, evmCallSteleBase, evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      hguyMoveEq] using hcallAshSteleRaw
  let evmAshSteleBase : EVM.State := { evmAshStele with substate := Ain }
  let σKissStele := σKiss
  let AKissStele0 := AKiss
  have hkissCallSteleBase := hkissCall
  have hpostKissAccounts : σKiss = σKissStele := rfl
  have hdepthNeKissBase : evmAshSteleBase.executionEnv.depth ≠ 1024 := by
    simpa [evmAshSteleBase, evmAshStele, evmCallStele, evmStele, initState, hcallEnv]
      using hdepthNeI
  obtain ⟨AKissStele, hkissCallSteleRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hkissCallSteleBase hdepthNeKissBase
      evmAshStele.substate
  let evmKissStele : EVM.State :=
    { evmAshStele with
        accountMap := σKissStele, substate := AKissStele }
  have hguyAshEq :
      solcAddressSlotWord packedSlot σAsh I =
        solcAddressSlotWord packedSlot σAshStele I :=
    congrArg (fun accounts => solcAddressSlotWord packedSlot accounts I) hpostAsrfl
  have hkissCallStele :
      typedCallViaEVM fork config evmAshStele
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAshStele I).toNat))
        "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKissStele, outKiss) true := by
    have hraw := hkissCallSteleRaw
    rw [hguyAshEq] at hraw
    simpa only [evmKissStele, evmAshSteleBase, evmAshStele, dentGuyWord, packedSlot,
      hcallEnv] using hraw
  have hkissEnv : evmKissStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hkissCallStele
    simpa [evmKissStele, evmAshStele, evmCallStele, evmStele, initState, hcallEnv] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_eq_afterGuyStore
      (I := I) (σ := σKiss) (evmStele := evmKissStele)
      (by simpa [evmKissStele] using hpostKissAccounts) hkissEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hkissEnv
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidStele : dentBidWord I = dentBidStoredWord evmStele I := by
    simpa [evmStele, dentBidStoredWord, initState] using hbid
  have hlotLtStele :
      (dentLotWord I).toNat < (dentLotStoredWord evmStele I).toNat := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotLt
  have hbegFitStele :
      (dentBegWord evmStele).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmStele, dentBegWord, initState] using hbegFit
  have hlotOneFitStele :
      (dentLotStoredWord evmStele I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotOneFit
  have hsuffStele :
      (dentBegLotWord evmStele I).toNat ≤ (dentLotOneWord evmStele I).toNat := by
    simpa [evmStele, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerStele :
      UInt256.ofNat evmStele.executionEnv.source.val ≠ dentGuyWord evmStele I := by
    intro heq
    apply hcaller
    simpa [evmStele, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩ :=
    hcodeSize
  have hticMoveStele : dentTicWord evmCallStele I = ⟨0⟩ := by
    have hword := congrArg (fun accounts => uint48Offset20Word packedSlot accounts I) hpostAccountsCall
    simpa [evmCallStele, dentTicWord, packedSlot, hcallEnv, hword] using hticMove
  have hashCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmCallStele.accountMap
        (dentGuyWord evmCallStele I) ≠ ⟨0⟩ := by
    simpa [evmCallStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAccountsCall] using hashCodeSize
  have hkissCodeSizeStele :
      Reasoning.Theory.extCodeSizeWord evmAshStele.accountMap
        (dentGuyWord evmAshStele I) ≠ ⟨0⟩ := by
    simpa [evmAshStele, dentGuyWord, packedSlot, hcallEnv,
      ← hpostAsrfl] using hkissCodeSize
  have haddFitStele :
      (dentNow48Word (dentAfterGuyStore evmKissStele I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmKissStele I) I)).toNat <
        2 ^ 48 := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hkissEnv, httl] using haddFit
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have hstatic := permSplit_false hp
      (flopperDentX_kissCallSuccessToTailSplit (g := Sat256.ofUInt256 g) rd2833)
    have hsource := (flopperDentBodyReturns_success_moveCallerNe_ticZero_kissSuccessSplit
        evmStele evmCallStele evmAshStele evmKissStele I outMove outAsh outKiss
        (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
        hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
        hcallerStele
        (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
        hcallStele hticMoveStele hashCodeSizeStele hcallAshStele houtAsh32
        hkissCodeSizeStele hkissCallStele).2 hp
    exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        (.returned
          { contract := contract
            locals := dentKissRetTicLocals evmStele
              (dentAfterGuyStore evmKissStele I) I outAsh }
          (dentPostState (dentAfterGuyStore evmKissStele I) I)
          none) := by
    exact flopperDentBodyReturns_success_moveCallerNe_ticZero_kissSuccess (hperm := hperm)
      evmStele evmCallStele evmAshStele evmKissStele I outMove outAsh outKiss
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
      hcallerStele
      (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
      hcallStele hticMoveStele hashCodeSizeStele hcallAshStele houtAsh32
      hkissCodeSizeStele hkissCallStele haddFitStele
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_kissCallSuccessToTail (g := Sat256.ofUInt256 g) hperm rd2833
  have hret :=
    flopperDentX_successFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddFit rd2889
  have hpostAccounts :=
    dentRuntimeTailSuccessAccountMap_afterGuy_eq_postState
      (I := I) hAfterGuy hkissEnv haddFit
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simpa [evmKissStele] using hpostAccounts)
    (by
      simpa [dentTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreAddOverflowMoveCallerNeTicNonzero
    {σ σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ' I) I).toNat)
    (rd2545 : RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        solcAddressSlotWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out σ' k C)
    (hcall :
      typedCallViaEVM fork config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let σ'_stele := σ'
  let A'_stele := A'
  have hcallSteleRaw := hcall
  have hpostAccountsCall : σ' = σ'_stele := rfl
  let evmCallStele : EVM.State :=
    { evmStele with accountMap := σ'_stele, substate := A'_stele }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallStele :
      typedCallViaEVM fork config evmStele
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address evmStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (solcAddressSlotWord packedSlot σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallStele, out) true := by
    simpa [evmStele, evmCallStele, packedSlot, hsrcEq] using
      hcallSteleRaw
  have hcallEnv : evmCallStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallStele
    simpa [evmStele, initState] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_eq_afterGuyStore
      (I := I) hpostAccountsCall hcallEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hcallEnv
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidStele : dentBidWord I = dentBidStoredWord evmStele I := by
    simpa [evmStele, dentBidStoredWord, initState] using hbid
  have hlotLtStele :
      (dentLotWord I).toNat < (dentLotStoredWord evmStele I).toNat := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotLt
  have hbegFitStele :
      (dentBegWord evmStele).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmStele, dentBegWord, initState] using hbegFit
  have hlotOneFitStele :
      (dentLotStoredWord evmStele I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotOneFit
  have hsuffStele :
      (dentBegLotWord evmStele I).toNat ≤ (dentLotOneWord evmStele I).toNat := by
    simpa [evmStele, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerStele :
      UInt256.ofNat evmStele.executionEnv.source.val ≠ dentGuyWord evmStele I := by
    intro heq
    apply hcaller
    simpa [evmStele, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩ :=
    hcodeSize
  have hticMoveStele : dentTicWord evmCallStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hticMove
    have hmap : σ' = σ'_stele := by simpa [initState] using hpostAccountsCall
    rw [hmap]
    simpa [evmCallStele, dentTicWord, packedSlot, hcallEnv] using hzero
  have haddOverflowStele :
      2 ^ 48 ≤
        (dentNow48Word (dentAfterGuyStore evmCallStele I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmCallStele I) I)).toNat := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hcallEnv, httl] using haddOverflow
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have hstatic := permSplit_false hp
      (flopperDentX_moveSuccessTicNonzeroToTailSplit
        (g := Sat256.ofUInt256 g) hticMove rd2545)
    have hsource := (flopperDentBodyReturns_success_moveCallerNe_ticNonzeroSplit
        evmStele evmCallStele I out
        (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
        hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
        hcallerStele
        (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
        hcallStele hticMoveStele).2 hp
    exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_addOverflow_moveCallerNe_ticNonzero (hperm := hperm)
      evmStele evmCallStele I out
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
      hcallerStele
      (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
      hcallStele hticMoveStele haddOverflowStele
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_moveSuccessTicNonzeroToTail
      (g := Sat256.ofUInt256 g) hperm hticMove rd2545
  have hrev :=
    flopperDentX_addOverflowFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddOverflow rd2889
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreSuccessMoveCallerNeTicNonzero
    {σ σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I ≠ ⟨0⟩)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
          (dentRuntimeTtlWord I.codeOwner (dentRuntimeAfterGuyMap I.codeOwner σ' I) I).toNat <
        2 ^ 48)
    (rd2545 : RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        solcAddressSlotWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out σ' k C)
    (hcall :
      typedCallViaEVM fork config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let σ'_stele := σ'
  let A'_stele := A'
  have hcallSteleRaw := hcall
  have hpostAccountsCall : σ' = σ'_stele := rfl
  let evmCallStele : EVM.State :=
    { evmStele with accountMap := σ'_stele, substate := A'_stele }
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hsrcEq : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    simpa [solcSourceWord] using solcSource_ofNat I
  have hcallStele :
      typedCallViaEVM fork config evmStele
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address evmStele.executionEnv.source,
          .address (AccountAddress.ofNat
            (solcAddressSlotWord packedSlot σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true, evmCallStele, out) true := by
    simpa [evmStele, evmCallStele, packedSlot, hsrcEq] using
      hcallSteleRaw
  have hcallEnv : evmCallStele.executionEnv = I := by
    have h := typedCallViaEVM_executionEnv_eq hcallStele
    simpa [evmStele, initState] using h
  have hAfterGuy :=
    dentRuntimeAfterGuyMap_eq_afterGuyStore
      (I := I) hpostAccountsCall hcallEnv
  have httl :=
    dentRuntimeTtlWord_afterGuy_eq (I := I) hAfterGuy hcallEnv
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidStele : dentBidWord I = dentBidStoredWord evmStele I := by
    simpa [evmStele, dentBidStoredWord, initState] using hbid
  have hlotLtStele :
      (dentLotWord I).toNat < (dentLotStoredWord evmStele I).toNat := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotLt
  have hbegFitStele :
      (dentBegWord evmStele).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmStele, dentBegWord, initState] using hbegFit
  have hlotOneFitStele :
      (dentLotStoredWord evmStele I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmStele, dentLotStoredWord, initState] using hlotOneFit
  have hsuffStele :
      (dentBegLotWord evmStele I).toNat ≤ (dentLotOneWord evmStele I).toNat := by
    simpa [evmStele, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerStele :
      UInt256.ofNat evmStele.executionEnv.source.val ≠ dentGuyWord evmStele I := by
    intro heq
    apply hcaller
    simpa [evmStele, dentGuyWord, initState, packedSlot] using heq
  have hcodeSizeStele :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩ :=
    hcodeSize
  have hticMoveStele : dentTicWord evmCallStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hticMove
    have hmap : σ' = σ'_stele := by simpa [initState] using hpostAccountsCall
    rw [hmap]
    simpa [evmCallStele, dentTicWord, packedSlot, hcallEnv] using hzero
  have haddFitStele :
      (dentNow48Word (dentAfterGuyStore evmCallStele I)).toNat +
          (dentTtlWord (dentAfterLotStore (dentAfterGuyStore evmCallStele I) I)).toNat <
        2 ^ 48 := by
    simpa [dentNow48Word, dentTimestampWord, dentAfterGuyStore, storageStore_executionEnv,
      hcallEnv, httl] using haddFit
  by_cases hperm : I.perm = true
  swap
  · have hp : I.perm = false := by simpa using hperm
    have hstatic := permSplit_false hp
      (flopperDentX_moveSuccessTicNonzeroToTailSplit
        (g := Sat256.ofUInt256 g) hticMove rd2545)
    have hsource := (flopperDentBodyReturns_success_moveCallerNe_ticNonzeroSplit
        evmStele evmCallStele I out
        (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
        hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
        hcallerStele
        (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
        hcallStele hticMoveStele).2 hp
    exact hstatic.reEquivStaticHalt hcode hdispatch hdecode hsource
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        (.returned
          { contract := contract
            locals := dentMoveTicLocals evmStele (dentAfterGuyStore evmCallStele I) I }
          (dentPostState (dentAfterGuyStore evmCallStele I) I)
          none) := by
    exact flopperDentBodyReturns_success_moveCallerNe_ticNonzero (hperm := hperm)
      evmStele evmCallStele I out
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele hlotLtStele hbegFitStele hlotOneFitStele hsuffStele
      hcallerStele
      (by simpa [evmStele, dentVatWord, initState] using hcodeSizeStele)
      hcallStele hticMoveStele haddFitStele
  obtain ⟨_, _, _, rd2889⟩ :=
    flopperDentX_moveSuccessTicNonzeroToTail
      (g := Sat256.ofUInt256 g) hperm hticMove rd2545
  have hret :=
    flopperDentX_successFromTailAw8
      (g := Sat256.ofUInt256 g) hperm haddFit rd2889
  have hpostAccounts :=
    dentRuntimeTailSuccessAccountMap_afterGuy_eq_postState
      (I := I) hAfterGuy hcallEnv haddFit
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simpa [evmCallStele] using hpostAccounts)
    (by
      simpa [dentTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperDentBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact (flopperDentX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_dent_none_short hsz4 hshort)

theorem flopperDentBodyCoreNotLive
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveStele : dentLiveWord evmStele ≠ ⟨1⟩ := by
    intro hbad
    apply hlive
    simpa [evmStele, dentLiveWord, initState] using hbad
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_notLive evmStele I
      (by simpa [evmStele, initState] using hwv) hliveStele
  have hrev :=
    flopperDentX_notLive (g := Sat256.ofUInt256 g) hlive
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreGuyNotSet
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I = ⟨0⟩ := by
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hguy
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_guyNotSet evmStele I
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele
  have hrev :=
    flopperDentX_guyNotSet (g := Sat256.ofUInt256 g) hlive hguy
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreTicFinished
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticNe : uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticLe :
      (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticNeStele : dentTicWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hticNe
    simpa [evmStele, dentTicWord, initState, packedSlot] using hzero
  have hticLeStele : (dentTicWord evmStele I).toNat ≤ (dentTimestampWord evmStele).toNat := by
    simpa [evmStele, dentTicWord, dentTimestampWord, initState, packedSlot]
      using hticLe
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_ticFinished evmStele I
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele
      hticNeStele hticLeStele
  have hrev :=
    flopperDentX_ticFinished (g := Sat256.ofUInt256 g) hlive hguy hticNe hticLe
      (flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach)
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

set_option maxHeartbeats 1000000 in
theorem flopperDentBodyCoreEndFinished
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendLe :
      (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let id := dentIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState]
          using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState] using hzero
  have hendLeStele : (dentEndWord evmStele I).toNat ≤ (dentTimestampWord evmStele).toNat := by
    simpa [evmStele, dentEndWord, dentTimestampWord, initState]
      using hendLe
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_endFinished evmStele I
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele
      hticOkStele hendLeStele
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev fork flopperBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
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
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I ≠ solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      config.externalABI.decodeCalldata? (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD fork flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveStele : dentLiveWord evmStele = ⟨1⟩ := by
    simpa [evmStele, dentLiveWord, initState] using hlive
  have hguyStele : dentGuyWord evmStele I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmStele, dentGuyWord, initState, packedSlot] using hzero
  have hticOkStele :
      (dentTimestampWord evmStele).toNat < (dentTicWord evmStele I).toNat ∨
        dentTicWord evmStele I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmStele, dentTimestampWord, dentTicWord, initState] using hgt
    | inr hzero =>
        right
        simpa [evmStele, dentTicWord, initState] using hzero
  have hendGtStele : (dentTimestampWord evmStele).toNat < (dentEndWord evmStele I).toNat := by
    simpa [evmStele, dentEndWord, dentTimestampWord, initState] using hendGt
  have hbidStele : dentBidWord I ≠ dentBidStoredWord evmStele I := by
    intro heq
    apply hbid
    simpa [evmStele, dentBidStoredWord, initState] using heq
  have hbody :
      ExecTransitionBody fork config contract evmStele (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_bidMismatch evmStele I
      (by simpa [evmStele, initState] using hwv) hliveStele hguyStele hticOkStele
      hendGtStele hbidStele
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨memBid, _, _, hmemBid, hreadBid, rd2099⟩ :=
    flopperDentX_toBidEqGuardFromDecoded hlive hguy hticOk hendGt hdecoded
  have hrev := flopperDentX_bidMismatchFromGuard hbid hmemBid hreadBid rd2099
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

end Benchmarks.Dss.Flopper
