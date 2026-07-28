import Examples.BlindAuction.Reveal.PostLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_nonempty_fromLoopResult
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {callargs : Store} {values fakes secrets : List Value}
    {loopLen secretsLenWord fakesLenWord valuesLenWord : UInt256}
    (hcode : I.code = blindAuctionBytecode)
    (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hperm : I.perm = true)
    (evmSolm : EVM.State)
    (hevmSolm : evmSolm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩)
    (hafterBody :
      (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat)
    (hbeforeBody :
      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbiddingAbsent : callargs.get? biddingEndRef.base = none)
    (hrevealAbsent : callargs.get? revealEndRef.base = none)
    (hvaluesGet : callargs.get? "values" = some (.array values))
    (hfakesGet : callargs.get? "fakes" = some (.array fakes))
    (hsecretsGet : callargs.get? "secrets" = some (.array secrets))
    (hlenBody :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
        (bidsBase (.address evmSolm.executionEnv.source)) = revealScratchBidsLengthWord σ_solm I)
    (hbidsEq : revealScratchBidsLengthWord σ_evm I = revealScratchBidsLengthWord σ_solm I)
    (hloopLen : loopLen = revealScratchBidsLengthWord σ_evm I)
    (hvaluesEq : loopLen = valuesLenWord)
    (hfakesEq : loopLen = fakesLenWord)
    (hsecretsEq : loopLen = secretsLenWord)
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
    (hloopResult :
      (∃ aDone LDone evmDone kDone CDone,
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract,
            locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmSolm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := LDone } evmDone) ∧
        RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A 0 aDone LDone evmDone ∧
        RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1331⟩
          (scratch_revealEvmLoopStack aDone.idx aDone.refund loopLen
            (revealScratchRevealEndWord σ_evm I)
            (revealScratchBiddingEndWord σ_evm I)
            secretsLenWord (⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
            fakesLenWord (⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
            valuesLenWord (⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
            (blindAuctionSelWord I))
          aDone.mem aDone.aw ByteArray.empty aDone.acc kDone CDone)
      ∨
      (ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract,
            locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmSolm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted ∧
        RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hloopResult with hdone | hrevLoop
  · rcases hdone with
      ⟨aDone, LDone, evmDone, kDone, CDone, hloop, hInvDone, rd1331⟩
    exact
      scratch_blindAuctionReveal_postLoop_fromDone
        (I := I) (g := g)
        (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
        (callargs := callargs)
        (values := values) (fakes := fakes) (secrets := secrets)
        (loopLen := loopLen)
        (secretsLenWord := secretsLenWord)
        (fakesLenWord := fakesLenWord)
        (valuesLenWord := valuesLenWord)
        (aDone := aDone) (LDone := LDone) (evmDone := evmDone)
        (kDone := kDone) (CDone := CDone)
        hcode hd hdec hstore hperm evmSolm hevmSolm
        hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        hvaluesGet hfakesGet hsecretsGet hlenBody hbidsEq
        hloopLen hvaluesEq hfakesEq hsecretsEq
        hvaluesListLen hfakesListLen hsecretsListLen
        hloop hInvDone rd1331
  · have hbodyLoop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract,
            locals :=
              scratch_revealLoopStore callargs (revealScratchBidsLengthWord σ_solm I)
                ⟨0⟩ ⟨0⟩ } evmSolm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted := by
      rw [← hbidsEq, ← hloopLen]
      exact hrevLoop.1
    have hvaluesLenBody :
        values.length = (revealScratchBidsLengthWord σ_solm I).toNat := by
      rw [hvaluesListLen, ← hvaluesEq, hloopLen, hbidsEq]
    have hfakesLenBody :
        fakes.length = (revealScratchBidsLengthWord σ_solm I).toNat := by
      rw [hfakesListLen, ← hfakesEq, hloopLen, hbidsEq]
    have hsecretsLenBody :
        secrets.length = (revealScratchBidsLengthWord σ_solm I).toNat := by
      rw [hsecretsListLen, ← hsecretsEq, hloopLen, hbidsEq]
    have hbodyRev :
        ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
          callargs revealTransition.body .reverted := by
      exact scratch_blindAuctionRevealBodyReverts_fromLoopRevertOfLocals
        evmSolm callargs values fakes secrets
        (revealScratchBidsLengthWord σ_solm I)
        hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by
          rw [hstore]
          simp)
        hvaluesGet hfakesGet hsecretsGet hlenBody
        hvaluesLenBody hfakesLenBody hsecretsLenBody hbodyLoop
    have hbodyRevInit :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          callargs revealTransition.body .reverted := by
      rw [← hevmSolm]
      exact hbodyRev
    exact hrevLoop.2.reEquivExecutionRevert hcode hd hdec hbodyRevInit

end BlindAuction
