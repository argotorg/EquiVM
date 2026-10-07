import Examples.BlindAuction.Reveal.DecodedLengthOk

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_decoded_ok_from1806
    {σ σ₀ A I} {g : UInt256}
    {callargs : Store}
    (hcode : I.code = blindAuctionBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hwv : I.weiValue = ⟨0⟩)
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hhead : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor blindAuctionConfig blindAuctionContract
      σ σ₀ g A I := by
  obtain ⟨_, _, rd1806⟩ := hhead
  obtain ⟨values, fakes, secrets, hstore, hguards⟩ :=
    blindAuctionDecode_reveal_guard_facts hcalldataSign hdec
  rcases hguards with ⟨hvaluesGuards, hfakesGuards, hsecretsGuards⟩
  rcases hvaluesGuards with
    ⟨valuesLenWord, hvaluesListLen, hvaluesGt, hvaluesStart, hvaluesLenLoad,
      hvaluesLenMax, hvaluesEnd⟩
  rcases hfakesGuards with
    ⟨fakesLenWord, hfakesListLen, hfakesGt, hfakesStart, hfakesLenLoad,
      hfakesLenMax, hfakesEnd⟩
  rcases hsecretsGuards with
    ⟨secretsLenWord, hsecretsListLen, hsecretsGt, hsecretsStart,
      hsecretsLenLoad, hsecretsLenMax, hsecretsEnd⟩
  have hvaluesGet : callargs.get? "values" = some (.array values) := by
    rw [hstore, store_get_ne, store_get_ne, store_get_self]
    · decide
    · decide
  have hfakesGet : callargs.get? "fakes" = some (.array fakes) := by
    rw [hstore, store_get_ne, store_get_self]
    decide
  have hsecretsGet : callargs.get? "secrets" = some (.array secrets) := by
    rw [hstore, store_get_self]
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887
      (ee := I) (g := Sat256.ofUInt256 g)
      rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax hvaluesEnd
      hfakesGt hfakesStart hfakesLenLoad hfakesLenMax hfakesEnd
      hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax hsecretsEnd
  let evmSolm : EVM.State :=
    initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
    simpa [evmSolm, initState] using hwv
  have hbiddingAbsent : callargs.get? biddingEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hrevealAbsent : callargs.get? revealEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hbidsHash := revealScratchBidsMappingBaseKeccak I
  by_cases hafter :
      (revealScratchBiddingEndWord σ I).toNat <
        (revealScratchTimestampWord I).toNat
  · by_cases hbefore :
        (revealScratchTimestampWord I).toNat <
          (revealScratchRevealEndWord σ I).toNat
    · have hafterBody :
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
            (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
        change (revealScratchBiddingEndWord σ I).toNat <
          (revealScratchTimestampWord I).toNat
        exact hafter
      have hbeforeBody :
          (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
            (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat := by
        change (revealScratchTimestampWord I).toNat <
          (revealScratchRevealEndWord σ I).toNat
        exact hbefore
      have hlenBody :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (bidsBase (.address evmSolm.executionEnv.source)) =
              revealScratchBidsLengthWord σ I := by
        rfl
      by_cases hvaluesEq :
          revealScratchBidsLengthWord σ I = valuesLenWord
      · by_cases hfakesEq :
            revealScratchBidsLengthWord σ I = fakesLenWord
        · by_cases hsecretsEq :
              revealScratchBidsLengthWord σ I = secretsLenWord
          · exact scratch_blindAuctionReveal_decoded_times_lengths_ok
              (I := I) (g := g)
              (σ := σ)  (σ₀ := σ₀) (A := A)
              (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
              (valuesLenWord := valuesLenWord)
              (fakesLenWord := fakesLenWord)
              (secretsLenWord := secretsLenWord)
              hcode hsize hperm hd hdec hstore hwv
              hvaluesGet hfakesGet hsecretsGet
              hvaluesListLen hfakesListLen hsecretsListLen hvaluesLenMax
              hafter hbefore hvaluesEq hfakesEq hsecretsEq
              ⟨_, _, rd887⟩
          · have hrev :=
              blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
                (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
              rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
              hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
              hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
              hsecretsEnd hafter hbefore hvaluesEq hfakesEq hsecretsEq hbidsHash
            have hsecretsNeNat :
                secrets.length ≠ (revealScratchBidsLengthWord σ I).toNat := by
              intro hnat
              apply hsecretsEq
              apply u256_inj
              omega
            have hbody :
                ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                  callargs revealTransition.body .reverted := by
              exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
                evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
                hbeforeBody hlenBody (Or.inr (Or.inr hsecretsNeNat))
            exact hrev.reEquivExecutionRevert hcode hd hdec hbody
        · have hrev :=
            blindAuctionRevealDecodeArrays1806_fakesLengthMismatch_reverts
              (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
              rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
              hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
              hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
              hsecretsEnd hafter hbefore hvaluesEq hfakesEq hbidsHash
          have hfakesNeNat :
              fakes.length ≠ (revealScratchBidsLengthWord σ I).toNat := by
            intro hnat
            apply hfakesEq
            apply u256_inj
            omega
          have hbody :
              ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                callargs revealTransition.body .reverted := by
            exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
              evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
              hbeforeBody hlenBody (Or.inr (Or.inl hfakesNeNat))
          exact hrev.reEquivExecutionRevert hcode hd hdec hbody
      · have hrev :=
          blindAuctionRevealDecodeArrays1806_valuesLengthMismatch_reverts
            (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
            rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax hvaluesEnd
            hfakesGt hfakesStart hfakesLenLoad hfakesLenMax hfakesEnd
            hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax hsecretsEnd
            hafter hbefore hvaluesEq hbidsHash
        have hvaluesNeNat :
            values.length ≠ (revealScratchBidsLengthWord σ I).toNat := by
          intro hnat
          apply hvaluesEq
          apply u256_inj
          omega
        have hbody :
            ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
              callargs revealTransition.body .reverted := by
          exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
            evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
            hbeforeBody hlenBody (Or.inl hvaluesNeNat)
        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
    · have hrev := blindAuctionRevealX_from887_tooLate
          (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
          (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
          rd887 hafter (Nat.le_of_not_gt hbefore)
      have hafterBody :
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
            (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
        change (revealScratchBiddingEndWord σ I).toNat <
          (revealScratchTimestampWord I).toNat
        exact hafter
      have hlateBody :
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat ≤
            (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
        change (revealScratchRevealEndWord σ I).toNat ≤
          (revealScratchTimestampWord I).toNat
        exact Nat.le_of_not_gt hbefore
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
            callargs revealTransition.body .reverted := by
        exact blindAuctionRevealBodyReverts_tooLate hwvSolm hbiddingAbsent
          hrevealAbsent hafterBody hlateBody
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
  · have hrev := blindAuctionRevealX_from887_tooEarly
        (σ := σ) (I := I) (g := Sat256.ofUInt256 g)
        (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
        rd887 (Nat.le_of_not_gt hafter)
    have htimeBody :
        (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat ≤
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat := by
      change (revealScratchTimestampWord I).toNat ≤
        (revealScratchBiddingEndWord σ I).toNat
      exact Nat.le_of_not_gt hafter
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
          callargs revealTransition.body .reverted := by
      exact blindAuctionRevealBodyReverts_tooEarly hwvSolm hbiddingAbsent htimeBody
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
