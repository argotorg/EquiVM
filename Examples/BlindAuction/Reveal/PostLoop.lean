import Examples.BlindAuction.Reveal.PostLoopBranches
import Lean.Elab.Tactic.AsAuxLemma

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_postLoop_fromDone
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {callargs : Store} {values fakes secrets : List Value}
    {loopLen secretsLenWord fakesLenWord valuesLenWord : UInt256}
    {aDone : RevealLoopCursor} {LDone : Store} {evmDone : EVM.State}
    {kDone CDone : ℕ}
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
    (hloop :
      ExecForLoop blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmSolm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok { contract := blindAuctionContract, locals := LDone } evmDone))
    (hInvDone : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A 0 aDone LDone evmDone)
    (rd1331 :
      RD blindAuctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1331⟩
        (scratch_revealEvmLoopStack aDone.idx aDone.refund loopLen
          (revealScratchRevealEndWord σ_evm I)
          (revealScratchBiddingEndWord σ_evm I)
          secretsLenWord (⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
          fakesLenWord (⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
          valuesLenWord (⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
          (blindAuctionSelWord I))
        aDone.mem aDone.aw ByteArray.empty aDone.acc kDone CDone) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hInvDone with
    ⟨_hiDone, _hlenDone, hrefundDone, _hbidsDone, _hvaluesDone,
      _hfakesDone, _hsecretsDone, _hvariantDone, _hidxLeDone,
      henvDone, hσ0Done, hghDone, hblDone, hcreatedDone,
      hsubDone, haccountsDone⟩
  have hlenBodyLoop :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
        (bidsBase (.address evmSolm.executionEnv.source)) = loopLen := by
    rw [hlenBody, ← hbidsEq, ← hloopLen]
  have hvaluesLenLoop : values.length = loopLen.toNat := by
    rw [hvaluesListLen, ← hvaluesEq]
  have hfakesLenLoop : fakes.length = loopLen.toNat := by
    rw [hfakesListLen, ← hfakesEq]
  have hsecretsLenLoop : secrets.length = loopLen.toNat := by
    rw [hsecretsListLen, ← hsecretsEq]
  obtain ⟨gasArg, k1349, C1349, rd1349⟩ :=
    scratch_blindAuctionRevealX_loopExit_toCall
      (I := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (acc := aDone.acc) (mem := aDone.mem) (aw := aDone.aw)
      (rdata := ByteArray.empty) (k := kDone) (C := CDone)
      (i := aDone.idx) (refund := aDone.refund) (len := loopLen)
      (revealEnd := revealScratchRevealEndWord σ_evm I)
      (biddingEnd := revealScratchBiddingEndWord σ_evm I)
      (secretsLen := secretsLenWord)
      (secretsEnd := ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
      (fakesLen := fakesLenWord)
      (fakesEnd := ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
      (valuesLen := valuesLenWord)
      (valuesEnd := ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
      (sel := blindAuctionSelWord I) (freePtr := aDone.fp)
      (by simpa using rd1331)
      aDone.hfpLoad
      (scratch_reveal_aw_mload64_of_ge3 aDone.haw)
  have hawCall : UInt256.ofNat
      (MachineState.M
        (MachineState.M aDone.aw.toNat aDone.fp.toNat
          (⟨0⟩ : UInt256).toNat)
        aDone.fp.toNat (⟨0⟩ : UInt256).toNat) = aDone.aw :=
    scratch_reveal_aw_call_empty aDone.aw aDone.fp
  by_cases hdepthEq : I.depth = 1024
  · exact scratch_blindAuctionReveal_postLoop_callDepth_fromCall
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
      (loopLen := loopLen) (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
      (aDone := aDone) (LDone := LDone) (evmSolm := evmSolm) (evmDone := evmDone)
      (gasArg := gasArg) (k1349 := k1349) (C1349 := C1349)
      hcode hd hdec hstore hperm hevmSolm hwvSolm hafterBody hbeforeBody
      hbiddingAbsent hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop
      hvaluesLenLoop hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop rd1349
      hawCall hdepthEq
  · have hdepthLt : I.depth.val < 1024 := by
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      have hneVal : I.depth.val ≠ 1024 := by
        intro hv
        exact hdepthEq (Fin.ext hv)
      omega
    by_cases hbalance :
        aDone.refund ≤
          (aDone.acc.2.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
    · exact scratch_blindAuctionReveal_postLoop_callMade_fromCall
        (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g)
        (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
        (loopLen := loopLen) (secretsLenWord := secretsLenWord)
        (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
        (aDone := aDone) (LDone := LDone) (evmSolm := evmSolm) (evmDone := evmDone)
        (gasArg := gasArg) (k1349 := k1349) (C1349 := C1349)
        hcode hd hdec hstore hperm hevmSolm hwvSolm hafterBody hbeforeBody
        hbiddingAbsent hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop
        hvaluesLenLoop hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop rd1349
        hawCall hσ0Done hghDone hblDone hcreatedDone hsubDone haccountsDone hdepthLt
        hdepthEq hbalance
    · exact scratch_blindAuctionReveal_postLoop_callInsufficient_fromCall
        (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g)
        (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
        (loopLen := loopLen) (secretsLenWord := secretsLenWord)
        (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
        (aDone := aDone) (LDone := LDone) (evmSolm := evmSolm) (evmDone := evmDone)
        (gasArg := gasArg) (k1349 := k1349) (C1349 := C1349)
        hcode hd hdec hstore hperm hevmSolm hwvSolm hafterBody hbeforeBody
        hbiddingAbsent hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop
        hvaluesLenLoop hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop rd1349
        hawCall hσ0Done hghDone hblDone hcreatedDone hsubDone haccountsDone hdepthLt
        hbalance

end BlindAuction
