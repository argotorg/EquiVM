import Examples.BlindAuction.Reveal.DecodedEmpty
import Examples.BlindAuction.Reveal.DecodedNonempty

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_decoded_times_lengths_ok
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
    (h887 : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨887⟩
      (revealDecodedStack I valuesLenWord ((⟨4⟩ + revealValuesOffsetWord I) + ⟨32⟩)
        fakesLenWord ((⟨4⟩ + revealFakesOffsetWord I) + ⟨32⟩)
        secretsLenWord ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨32⟩))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd887⟩ := h887
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
  have h963 :=
    blindAuctionRevealX_from887_afterTimeGuards
      (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀
        (Sat256.ofUInt256 g) A I)
      rd887 hafter hbefore
  rcases h963 with ⟨_, _, rd963⟩
  by_cases hbidsZero :
      revealScratchBidsLengthWord σ_evm I = ⟨0⟩
  · exact scratch_blindAuctionReveal_decoded_empty_bids
      (I := I) (g := g)
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
      (valuesLenWord := valuesLenWord)
      (fakesLenWord := fakesLenWord)
      (secretsLenWord := secretsLenWord)
      hcode hperm hd hdec hwv
      hvaluesGet hfakesGet hsecretsGet
      hvaluesListLen hfakesListLen hsecretsListLen hAccounts
      hafter hbefore hvaluesEq hfakesEq hsecretsEq hbidsZero
      ⟨_, _, rd963⟩
  · exact scratch_blindAuctionReveal_decoded_nonempty_bids
      (I := I) (g := g)
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
      (valuesLenWord := valuesLenWord)
      (fakesLenWord := fakesLenWord)
      (secretsLenWord := secretsLenWord)
      hcode hsize hperm hd hdec hstore hwv
      hvaluesGet hfakesGet hsecretsGet
      hvaluesListLen hfakesListLen hsecretsListLen hvaluesLenMax hAccounts
      hafter hbefore hvaluesEq hfakesEq hsecretsEq
      ⟨_, _, rd963⟩

end BlindAuction
