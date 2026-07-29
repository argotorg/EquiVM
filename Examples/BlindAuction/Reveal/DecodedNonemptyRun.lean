import Examples.BlindAuction.Reveal.DecodedNonemptyLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_nonempty_fromLoopStart
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {callargs : Store} {values fakes secrets : List Value}
    {loopLen secretsLenWord fakesLenWord valuesLenWord : UInt256}
    {initCursor : RevealLoopCursor} {evmSolm : EVM.State} {k1014 C1014 : ℕ}
    (hcode : I.code = blindAuctionBytecode)
    (hperm : I.perm = true)
    (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
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
    (hvaluesLenMax : UInt256.gt valuesLenWord revealMaxU64 = ⟨0⟩)
    (hloopRun :
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
          valuesLenWord valuesEnd sel values fakes secrets)
    (hinitInv :
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A loopLen.toNat initCursor
        (scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩) evmSolm)
    (rd1014 :
      RD blindAuctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1014⟩
        (scratch_revealEvmLoopStack initCursor.idx initCursor.refund loopLen
          (revealScratchRevealEndWord σ_evm I)
          (revealScratchBiddingEndWord σ_evm I)
          secretsLenWord (⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
          fakesLenWord (⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
          valuesLenWord (⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
          (blindAuctionSelWord I))
        initCursor.mem initCursor.aw ByteArray.empty initCursor.acc k1014 C1014) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hloopResult :
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
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) := by
    exact
      hloopRun rfl rfl rfl hvaluesEq hfakesEq hsecretsEq
        hvaluesListLen hfakesListLen hsecretsListLen hvaluesLenMax
        loopLen.toNat initCursor
      (scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩) evmSolm
      hinitInv k1014 C1014 rd1014
  exact
    scratch_blindAuctionReveal_nonempty_fromLoopResult
      (I := I) (g := g)
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (callargs := callargs)
      (values := values) (fakes := fakes) (secrets := secrets)
      (loopLen := loopLen)
      (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord)
      (valuesLenWord := valuesLenWord)
      hcode hd hdec hstore hperm evmSolm hevmSolm
      hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
      hvaluesGet hfakesGet hsecretsGet hlenBody hbidsEq
      hloopLen hvaluesEq hfakesEq hsecretsEq
      hvaluesListLen hfakesListLen hsecretsListLen
      hloopResult

end BlindAuction
