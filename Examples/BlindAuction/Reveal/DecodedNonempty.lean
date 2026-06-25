import Examples.BlindAuction.Reveal.DecodedNonemptyRun

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

attribute [local irreducible] RevealLoopRunFromStart

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_decoded_nonempty_bids
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {callargs : Store} {values fakes secrets : List Value}
    {valuesLenWord fakesLenWord secretsLenWord : UInt256}
    (hcode : I.code = blindAuctionBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hwv : I.weiValue = ⟨0⟩)
    (hvaluesGet : callargs.get? "values" = some (.array values))
    (hfakesGet : callargs.get? "fakes" = some (.array fakes))
    (hsecretsGet : callargs.get? "secrets" = some (.array secrets))
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
    (hvaluesLenMax : UInt256.gt valuesLenWord revealMaxU64 = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hafter :
      (revealScratchBiddingEndWord σ_evm I).toNat <
        (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat <
        (revealScratchRevealEndWord σ_evm I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ_evm I = valuesLenWord)
    (hfakesEq : revealScratchBidsLengthWord σ_evm I = fakesLenWord)
    (hsecretsEq : revealScratchBidsLengthWord σ_evm I = secretsLenWord)
    (h963 : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨963⟩
      [revealScratchRevealEndWord σ_evm I, revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd963⟩ := h963
  let evmSolm : EVM.State :=
    initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
    simpa [evmSolm, initState] using hwv
  have hbiddingAbsent : callargs.get? biddingEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hrevealAbsent : callargs.get? revealEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hbidsEq := revealScratchBidsLengthWord_accountMapEquiv hAccounts I
  have hafterBody :
      (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
    change (revealScratchBiddingEndWord σ_solm I).toNat <
      (revealScratchTimestampWord I).toNat
    rw [← revealScratchBiddingEndWord_accountMapEquiv hAccounts I]
    exact hafter
  have hbeforeBody :
      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat := by
    change (revealScratchTimestampWord I).toNat <
      (revealScratchRevealEndWord σ_solm I).toNat
    rw [← revealScratchRevealEndWord_accountMapEquiv hAccounts I]
    exact hbefore
  have hlenBody :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
        (bidsBase (.address evmSolm.executionEnv.source)) =
          revealScratchBidsLengthWord σ_solm I := by
    rfl
  have hbidsHash := revealScratchBidsMappingBaseKeccak I
  obtain ⟨k1014, C1014, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit
      (cA := cA) (σ := σ_evm) (I := I)
      (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀
        (Sat256.ofUInt256 g) A I)
      rd963 hvaluesEq hfakesEq hsecretsEq hbidsHash
  let loopLen : UInt256 := revealScratchBidsLengthWord σ_evm I
  let initCursor : RevealLoopCursor :=
    { idx := ⟨0⟩,
      refund := ⟨0⟩,
      mem := revealScratchBidsHashMem I,
      aw := UInt256.ofNat 3,
      acc := (cA, σ_evm),
      fp := ⟨128⟩,
      haw := by decide,
      hawSmall := by decide,
      hfpLoad := revealScratchBidsHashMem_mload64 I,
      hfpRead := revealScratchBidsHashMem_read64 I,
      hmem96 := by
        rw [revealScratchBidsHashMem_size],
      hmemle := by
        rw [revealScratchBidsHashMem_size]
        decide,
      hgap := by
        rw [revealScratchBidsHashMem_size]
        change 64 < USize.size
        exact lt_usize 64 (by norm_num),
      hfpIdx := by decide }
  let Inv : ℕ → RevealLoopCursor → Store → EVM.State → Prop :=
    RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A
  have hinitInv :
      Inv loopLen.toNat initCursor
        (scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩) evmSolm := by
    refine
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
    · exact scratch_revealLoopStore_i_get callargs loopLen ⟨0⟩ ⟨0⟩
    · exact scratch_revealLoopStore_length_get callargs loopLen ⟨0⟩ ⟨0⟩
    · exact scratch_revealLoopStore_refund_get callargs loopLen ⟨0⟩ ⟨0⟩
    · exact scratch_revealLoopStore_bids_none
        (callargs := callargs) (len := loopLen) (refund := ⟨0⟩)
        (i := ⟨0⟩) (by rw [hstore]; simp)
    · exact scratch_revealLoopStore_values_get
        (callargs := callargs) (len := loopLen) (refund := ⟨0⟩)
        (i := ⟨0⟩) hvaluesGet
    · exact scratch_revealLoopStore_fakes_get
        (callargs := callargs) (len := loopLen) (refund := ⟨0⟩)
        (i := ⟨0⟩) hfakesGet
    · exact scratch_revealLoopStore_secrets_get
        (callargs := callargs) (len := loopLen) (refund := ⟨0⟩)
        (i := ⟨0⟩) hsecretsGet
    · simp [loopLen, initCursor]
    · simp [loopLen, initCursor]
    · simp [evmSolm, initState]
    · simp [evmSolm, initState]
    · simp [evmSolm, initState]
    · simp [evmSolm, initState]
    · simp [evmSolm, initState, initCursor]
    · simp [evmSolm, initState]
    · simpa [evmSolm, initState, initCursor] using hAccounts
  have hloopRun :
      ∀ {revealEnd biddingEnd secretsEnd fakesEnd valuesEnd sel : UInt256},
        secretsEnd = ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩ →
        fakesEnd = ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩ →
        valuesEnd = ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩ →
        loopLen = valuesLenWord →
        loopLen = fakesLenWord →
        loopLen = secretsLenWord →
        values.length = valuesLenWord.toNat →
        fakes.length = fakesLenWord.toNat →
        secrets.length = secretsLenWord.toNat →
        UInt256.gt valuesLenWord revealMaxU64 = ⟨0⟩ →
        RevealLoopRunFromStart I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) σ₀ gh bl A loopLen
          revealEnd biddingEnd secretsLenWord secretsEnd fakesLenWord fakesEnd
          valuesLenWord valuesEnd sel values fakes secrets := by
    intro revealEnd biddingEnd secretsEnd fakesEnd valuesEnd sel hsecretsEnd hfakesEnd
      hvaluesEnd hvaluesEq' hfakesEq' hsecretsEq' hvaluesListLen' hfakesListLen'
      hsecretsListLen' hvaluesLenMax'
    exact
      scratch_revealLoop_fromLoopStart_or_revert
        (I := I) (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
        (loopLen := loopLen) (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLenWord := secretsLenWord) (secretsEnd := secretsEnd)
        (fakesLenWord := fakesLenWord) (fakesEnd := fakesEnd)
        (valuesLenWord := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
        (values := values) (fakes := fakes) (secrets := secrets) (callargs := callargs)
        hsize hperm hdec hstore hsecretsEnd hfakesEnd hvaluesEnd
        hvaluesEq' hfakesEq' hsecretsEq'
        hvaluesListLen' hfakesListLen' hsecretsListLen' hvaluesLenMax'
  exact
    scratch_blindAuctionReveal_nonempty_fromLoopStart
      (I := I) (g := g)
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (callargs := callargs)
      (values := values) (fakes := fakes) (secrets := secrets)
      (loopLen := loopLen)
      (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord)
      (valuesLenWord := valuesLenWord)
      (initCursor := initCursor) (evmSolm := evmSolm)
      (k1014 := k1014) (C1014 := C1014)
      hcode hperm hd hdec hstore rfl
      hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
      hvaluesGet hfakesGet hsecretsGet hlenBody hbidsEq
      rfl
      (by simpa [loopLen] using hvaluesEq)
      (by simpa [loopLen] using hfakesEq)
      (by simpa [loopLen] using hsecretsEq)
      hvaluesListLen hfakesListLen hsecretsListLen
      hvaluesLenMax hloopRun
      (by simpa [Inv] using hinitInv)
      (by
        simpa [loopLen, initCursor, scratch_revealEvmLoopStack]
          using rd1014)

end BlindAuction
