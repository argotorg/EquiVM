import Examples.BlindAuction.Reveal.PostLoop

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_nonempty_fromLoopResult
    {σ σ₀ A I} {g : UInt256}
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
    (evmStele : EVM.State)
    (hevmStele : evmStele = initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (hwvStele : evmStele.executionEnv.weiValue = ⟨0⟩)
    (hafterBody :
      (Stele.EVM.storageLoad evmStele evmStele.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evmStele.executionEnv.header.timestamp).toNat)
    (hbeforeBody :
      (UInt256.ofNat evmStele.executionEnv.header.timestamp).toNat <
        (Stele.EVM.storageLoad evmStele evmStele.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbiddingAbsent : callargs.get? biddingEndRef.base = none)
    (hrevealAbsent : callargs.get? revealEndRef.base = none)
    (hvaluesGet : callargs.get? "values" = some (.array values))
    (hfakesGet : callargs.get? "fakes" = some (.array fakes))
    (hsecretsGet : callargs.get? "secrets" = some (.array secrets))
    (hlenBody :
      Stele.EVM.storageLoad evmStele evmStele.executionEnv.codeOwner
        (bidsBase (.address evmStele.executionEnv.source)) = revealScratchBidsLengthWord σ I)
    (hloopLen : loopLen = revealScratchBidsLengthWord σ I)
    (hvaluesEq : loopLen = valuesLenWord)
    (hfakesEq : loopLen = fakesLenWord)
    (hsecretsEq : loopLen = secretsLenWord)
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
    (hloopResult :
      (∃ aDone LDone evmDone kDone CDone,
        ExecForLoop fork blindAuctionConfig
          { contract := blindAuctionContract,
            locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmStele
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := LDone } evmDone) ∧
        RevealLoopInv loopLen values fakes secrets I σ₀ A 0 aDone LDone evmDone ∧
        RD fork blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1331⟩
          (scratch_revealEvmLoopStack aDone.idx aDone.refund loopLen
            (revealScratchRevealEndWord σ I)
            (revealScratchBiddingEndWord σ I)
            secretsLenWord (⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
            fakesLenWord (⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
            valuesLenWord (⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
            (blindAuctionSelWord I))
          aDone.mem aDone.aw ByteArray.empty aDone.acc kDone CDone)
      ∨
      (ExecForLoop fork blindAuctionConfig
          { contract := blindAuctionContract,
            locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmStele
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted ∧
        RDrev fork blindAuctionBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      ∨
      (ExecForLoop fork blindAuctionConfig
          { contract := blindAuctionContract,
            locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmStele
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .staticViolation ∧
        RDstatic fork blindAuctionBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I))) :
    runtimeRefinementFor fork blindAuctionConfig blindAuctionContract
      σ σ₀ g A I := by
  rcases hloopResult with hdone | hrevLoop | hstLoop
  · rcases hdone with
      ⟨aDone, LDone, evmDone, kDone, CDone, hloop, hInvDone, rd1331⟩
    exact
      scratch_blindAuctionReveal_postLoop_fromDone
        (I := I) (g := g)
        (σ := σ)  (σ₀ := σ₀) (A := A)
        (callargs := callargs)
        (values := values) (fakes := fakes) (secrets := secrets)
        (loopLen := loopLen)
        (secretsLenWord := secretsLenWord)
        (fakesLenWord := fakesLenWord)
        (valuesLenWord := valuesLenWord)
        (aDone := aDone) (LDone := LDone) (evmDone := evmDone)
        (kDone := kDone) (CDone := CDone)
        hcode hd hdec hstore evmStele hevmStele
        hwvStele hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        hvaluesGet hfakesGet hsecretsGet hlenBody
        hloopLen hvaluesEq hfakesEq hsecretsEq
        hvaluesListLen hfakesListLen hsecretsListLen
        hloop hInvDone rd1331
  · have hbodyLoop :
        ExecForLoop fork blindAuctionConfig
          { contract := blindAuctionContract,
            locals :=
              scratch_revealLoopStore callargs (revealScratchBidsLengthWord σ I)
                ⟨0⟩ ⟨0⟩ } evmStele
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted := by
      rw [← hloopLen]
      exact hrevLoop.1
    have hvaluesLenBody :
        values.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hvaluesListLen, ← hvaluesEq, hloopLen]
    have hfakesLenBody :
        fakes.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hfakesListLen, ← hfakesEq, hloopLen]
    have hsecretsLenBody :
        secrets.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hsecretsListLen, ← hsecretsEq, hloopLen]
    have hbodyRev :
        ExecTransitionBody fork blindAuctionConfig blindAuctionContract evmStele
          callargs revealTransition.body .reverted := by
      exact scratch_blindAuctionRevealBodyReverts_fromLoopRevertOfLocals
        evmStele callargs values fakes secrets
        (revealScratchBidsLengthWord σ I)
        hwvStele hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by
          rw [hstore]
          simp)
        hvaluesGet hfakesGet hsecretsGet hlenBody
        hvaluesLenBody hfakesLenBody hsecretsLenBody hbodyLoop
    have hbodyRevInit :
        ExecTransitionBody fork blindAuctionConfig blindAuctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          callargs revealTransition.body .reverted := by
      rw [← hevmStele]
      exact hbodyRev
    exact hrevLoop.2.reEquivExecutionRevert hcode hd hdec hbodyRevInit
  · have hbodyLoop :
        ExecForLoop fork blindAuctionConfig
          { contract := blindAuctionContract,
            locals :=
              scratch_revealLoopStore callargs (revealScratchBidsLengthWord σ I)
                ⟨0⟩ ⟨0⟩ } evmStele
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .staticViolation := by
      rw [← hloopLen]
      exact hstLoop.1
    have hvaluesLenBody :
        values.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hvaluesListLen, ← hvaluesEq, hloopLen]
    have hfakesLenBody :
        fakes.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hfakesListLen, ← hfakesEq, hloopLen]
    have hsecretsLenBody :
        secrets.length = (revealScratchBidsLengthWord σ I).toNat := by
      rw [hsecretsListLen, ← hsecretsEq, hloopLen]
    have hbodySt :
        ExecTransitionBody fork blindAuctionConfig blindAuctionContract evmStele
          callargs revealTransition.body .staticViolation := by
      exact scratch_blindAuctionRevealBodyStatic_fromLoopStaticOfLocals
        evmStele callargs values fakes secrets
        (revealScratchBidsLengthWord σ I)
        hwvStele hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by
          rw [hstore]
          simp)
        hvaluesGet hfakesGet hsecretsGet hlenBody
        hvaluesLenBody hfakesLenBody hsecretsLenBody hbodyLoop
    have hbodyStInit :
        ExecTransitionBody fork blindAuctionConfig blindAuctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          callargs revealTransition.body .staticViolation := by
      rw [← hevmStele]
      exact hbodySt
    exact hstLoop.2.reEquivStaticHalt hcode hd hdec hbodyStInit

end BlindAuction
