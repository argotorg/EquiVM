import Examples.BlindAuction.Reveal.Body
import Lean.Elab.Tactic.AsAuxLemma

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

section Branches

variable {cA : Batteries.RBSet AccountAddress compare}
variable {gh : BlockHeader} {bl : ProcessedBlocks}
variable {σ_evm σ_solm σ₀ : AccountMap} {A : Substate}
variable {I : ExecutionEnv} {g : UInt256}
variable {callargs : Store} {values fakes secrets : List Value}
variable {loopLen secretsLenWord fakesLenWord valuesLenWord : UInt256}
variable {aDone : RevealLoopCursor} {LDone : Store}
variable {evmSolm evmDone : EVM.State}
variable {gasArg : UInt256} {k1349 C1349 : ℕ}

variable (hcode : I.code = blindAuctionBytecode)
variable (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
variable (hdec :
  decodeCalldata (revealTransition.params.map Param.name)
    (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
variable (hstore :
  callargs =
    (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
      "secrets" (.array secrets))
variable (hperm : I.perm = true)
variable (hevmSolm : evmSolm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
variable (hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩)
variable (hafterBody :
  (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
    (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat)
variable (hbeforeBody :
  (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat)
variable (hbiddingAbsent : callargs.get? biddingEndRef.base = none)
variable (hrevealAbsent : callargs.get? revealEndRef.base = none)
variable (hvaluesGet : callargs.get? "values" = some (.array values))
variable (hfakesGet : callargs.get? "fakes" = some (.array fakes))
variable (hsecretsGet : callargs.get? "secrets" = some (.array secrets))
variable (hlenBodyLoop :
  Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
    (bidsBase (.address evmSolm.executionEnv.source)) = loopLen)
variable (hvaluesLenLoop : values.length = loopLen.toNat)
variable (hfakesLenLoop : fakes.length = loopLen.toNat)
variable (hsecretsLenLoop : secrets.length = loopLen.toNat)
variable (hrefundDone :
  LDone.get? "refund" = some (.int (Int.ofNat aDone.refund.toNat)))
variable (henvDone : evmDone.executionEnv = I)
variable (hloop :
  ExecForLoop blindAuctionConfig
    { contract := blindAuctionContract,
      locals := scratch_revealLoopStore callargs loopLen ⟨0⟩ ⟨0⟩ } evmSolm
    (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
    scratch_revealLoopBodyStmts
    (.ok { contract := blindAuctionContract, locals := LDone } evmDone))
variable (rd1349 :
  RD blindAuctionBytecode I (Sat256.ofUInt256 g)
    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1349⟩
    [gasArg, revealScratchSenderWord I, aDone.refund, aDone.fp, ⟨0⟩, aDone.fp, ⟨0⟩,
      aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund, loopLen,
      revealScratchRevealEndWord σ_evm I, revealScratchBiddingEndWord σ_evm I,
      secretsLenWord, ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩,
      fakesLenWord, ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩,
      valuesLenWord, ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩,
      blindAuctionSelWord I]
    aDone.mem aDone.aw ByteArray.empty aDone.acc k1349 C1349)
variable (hawCall : UInt256.ofNat
  (MachineState.M
    (MachineState.M aDone.aw.toNat aDone.fp.toNat
      (⟨0⟩ : UInt256).toNat)
    aDone.fp.toNat (⟨0⟩ : UInt256).toNat) = aDone.aw)

include hcode hd hdec hstore hperm hevmSolm hwvSolm hafterBody hbeforeBody
  hbiddingAbsent hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop
  hvaluesLenLoop hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop rd1349
  hawCall

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_postLoop_callDepth_fromCall
    (hdepthEq : I.depth = 1024) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨k1350, C1350, rd1350₀⟩ :=
    RD.callValueDepthLimitEmptyInOut rd1349 hperm (by decide) hdepthEq (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aDone.aw.toNat aDone.fp.toNat 0) aDone.fp.toNat 0) =
          aDone.aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  have rd1350 : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
      [⟨0⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund,
        loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      aDone.mem aDone.aw ByteArray.empty aDone.acc k1350 C1350 := by
    simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀
  let evmSFail : EVM.State :=
    { evmDone with
      substate := (evmDone.addAccessedAccount
        (EVM.address evmDone.executionEnv.source)).substate }
  have hcallS :
      callViaEVM evmDone (EVM.address evmDone.executionEnv.source)
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (false, evmSFail, ByteArray.empty) := by
    apply callViaEVM.callNotMade
    · rfl
    · rfl
    · rintro ⟨_, hdepthNe⟩
      exact hdepthNe (by simpa [henvDone] using hdepthEq)
  have hbody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
        callargs revealTransition.body .reverted := by
    exact scratch_blindAuctionRevealBodyReverts_callFailure_fromLoopOfLocals
      evmSolm evmDone evmSFail callargs LDone values fakes secrets
      loopLen aDone.refund ByteArray.empty
      hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
      (by rw [hstore]; simp) hvaluesGet hfakesGet hsecretsGet
      hlenBodyLoop hvaluesLenLoop hfakesLenLoop hsecretsLenLoop
      hrefundDone hloop hcallS
  obtain ⟨k1405, C1405, rd1405⟩ : ∃ k' C',
      RD blindAuctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1405⟩
        [⟨0⟩, aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
          revealScratchBiddingEndWord σ_evm I, secretsLenWord,
          ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
          ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
          ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
        aDone.mem aDone.aw ByteArray.empty aDone.acc k' C' := by
    refine ⟨_, _, evm_run rd1350 with [
      swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
      jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
      jumpdest, pop, pop, swap1, pop]⟩
  have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have rd1410 := evm_run rd1405 with [
      dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
    exact RD.rev _ rd1410 (by decide)
      (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
      (by evm_ov)
  exact hrev.reEquivExecutionRevert hcode hd hdec (by
    rw [hevmSolm] at hbody
    exact hbody)

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_postLoop_callInsufficient_fromCall
    (hσ0Done : evmDone.σ₀ = σ₀)
    (hghDone : evmDone.genesisBlockHeader = gh)
    (hblDone : evmDone.blocks = bl)
    (hcreatedDone : evmDone.createdAccounts = aDone.acc.1)
    (hsubDone : evmDone.substate = A)
    (haccountsDone : accountMapEquiv aDone.acc.2 evmDone.accountMap)
    (hdepthLt : I.depth.val < 1024)
    (hbalance :
      ¬ aDone.refund ≤ (aDone.acc.2.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨k1350, C1350, rd1350₀⟩ :=
    RD.callValueInsufficientBalanceEmptyInOut rd1349 hperm (by decide) hbalance hdepthLt
      (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aDone.aw.toNat aDone.fp.toNat 0) aDone.fp.toNat 0) =
          aDone.aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  have rd1350 : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
      [⟨0⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund,
        loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      aDone.mem aDone.aw ByteArray.empty aDone.acc k1350 C1350 := by
    simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀
  let evmEDone : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := aDone.acc.2,
      createdAccounts := aDone.acc.1 }
  have hAddressId (a : AccountAddress) : EVM.address a = a := by
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt a.isLt
  have hTargetEq :
      AccountAddress.ofUInt256 (revealScratchSenderWord I) =
        EVM.address evmDone.executionEnv.source := by
    calc
      AccountAddress.ofUInt256 (revealScratchSenderWord I) = I.source := by
        simpa [revealScratchSenderWord] using accountAddress_roundtrip I.source
      _ = EVM.address evmDone.executionEnv.source := by
        simp [henvDone, hAddressId]
  have htransport
      {evmECall : EVM.State} {z : Bool} {out : ByteArray}
      (hcallE :
        callViaEVM evmEDone
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (Int.ofNat aDone.refund.toNat) ByteArray.empty
          (z, evmECall, out)) :
      ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
        callViaEVM evmDone
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (Int.ofNat aDone.refund.toNat) ByteArray.empty
          (z,
            { evmDone with
              accountMap := σ'_solm,
              substate := A'_solm,
              createdAccounts := evmECall.createdAccounts },
            out) ∧
        accountMapEquiv evmECall.accountMap σ'_solm := by
    exact callViaEVM_accountMapEquiv
      (storage := blindAuctionConfig.storage)
      (evm_solm := evmDone) hcallE
      (by simpa [evmEDone] using haccountsDone)
      (by simpa [evmEDone, initState] using hσ0Done.symm)
      (by simpa [evmEDone, initState] using hcreatedDone)
      (by simpa [evmEDone, initState] using hghDone)
      (by simpa [evmEDone, initState] using hblDone)
      (by simpa [evmEDone, initState] using hsubDone)
      (by simpa [evmEDone, initState] using henvDone)
  let evmEFail : EVM.State :=
    { evmEDone with
      substate := (evmEDone.addAccessedAccount
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))).substate }
  have hcallE :
      callViaEVM evmEDone
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (false, evmEFail, ByteArray.empty) := by
    apply callViaEVM.callNotMade
    · rfl
    · rfl
    · rintro ⟨hvalueBal, _⟩
      rw [wordOfInt_ofNat_toNat] at hvalueBal
      exact hbalance (by simpa [evmEDone, initState] using hvalueBal)
  obtain ⟨σ'_solm, A'_solm, hcallSRaw, _hPostAccounts⟩ :=
    htransport hcallE
  let evmSFail : EVM.State :=
    { evmDone with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := evmEFail.createdAccounts }
  have hcallS :
      callViaEVM evmDone (EVM.address evmDone.executionEnv.source)
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (false, evmSFail, ByteArray.empty) := by
    simpa [evmSFail, hTargetEq] using hcallSRaw
  have hbody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
        callargs revealTransition.body .reverted := by
    exact
      scratch_blindAuctionRevealBodyReverts_callFailure_fromLoopOfLocals
        evmSolm evmDone evmSFail callargs LDone values fakes secrets
        loopLen aDone.refund ByteArray.empty
        hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by rw [hstore]; simp) hvaluesGet hfakesGet hsecretsGet
        hlenBodyLoop hvaluesLenLoop hfakesLenLoop hsecretsLenLoop
        hrefundDone hloop hcallS
  obtain ⟨k1405, C1405, rd1405⟩ : ∃ k' C',
      RD blindAuctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1405⟩
        [⟨0⟩, aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
          revealScratchBiddingEndWord σ_evm I, secretsLenWord,
          ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
          ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
          ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
        aDone.mem aDone.aw ByteArray.empty aDone.acc k' C' := by
    refine ⟨_, _, evm_run rd1350 with [
      swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
      jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
      jumpdest, pop, pop, swap1, pop]⟩
  have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have rd1410 := evm_run rd1405 with [
      dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
    exact RD.rev _ rd1410 (by decide)
      (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
      (by evm_ov)
  exact hrev.reEquivExecutionRevert hcode hd hdec (by
    rw [hevmSolm] at hbody
    exact hbody)

omit hcode hd hdec hstore hevmSolm hwvSolm hafterBody hbeforeBody hbiddingAbsent
  hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop hvaluesLenLoop
  hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop in
theorem scratch_blindAuctionReveal_postLoop_callMade_step
    (hdepthLt : I.depth.val < 1024)
    (hbalance :
      aDone.refund ≤ (aDone.acc.2.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas : UInt256) (k1350 C1350 : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes aDone.acc.1
          gh bl aDone.acc.2 σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute aDone.acc.2 (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) aDone.refund aDone.refund
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ out.size < UInt256.size
      ∧ RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), aDone.fp, aDone.refund,
            revealScratchSenderWord I, ⟨0⟩, aDone.refund, loopLen,
            revealScratchRevealEndWord σ_evm I, revealScratchBiddingEndWord σ_evm I,
            secretsLenWord, ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
            ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
            ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
          aDone.mem aDone.aw out (cA', σ') k1350 C1350 := by
  obtain ⟨cA', σ', z, out, A_in, callGas, k1350, C1350, hThetaRaw, rd1350₀,
      houtSize⟩ :=
    RD.callValueMadeEmptyInOut rd1349 (by decide) hperm hbalance hdepthLt (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aDone.aw.toNat aDone.fp.toNat 0) aDone.fp.toNat 0) =
          aDone.aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  refine ⟨cA', σ', z, out, A_in, callGas, k1350, C1350, ?_, houtSize, ?_⟩
  · simpa [initState] using hThetaRaw
  · simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀

omit hcode hd hdec hstore hperm hevmSolm hwvSolm hafterBody hbeforeBody hbiddingAbsent
  hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop hvaluesLenLoop
  hfakesLenLoop hsecretsLenLoop hrefundDone henvDone hloop rd1349 hawCall in
theorem scratch_blindAuctionReveal_postLoop_postCallNonempty
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {out : ByteArray} {k C : ℕ} {z : UInt256}
    (rd : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
      [z, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund,
        loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      aDone.mem aDone.aw out (cA', σ') k C)
    (ho0 : out.size ≠ 0) (hosz : out.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1405⟩
      [z, aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      mem' aw' out (cA', σ') k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd1359₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd1359 := rd1359₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat out.size = rdsz from rfl, heq0] at rd1359
  have rd1363 := evm_run rd1359 with [push2 ⟨1395⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let aw1 : UInt256 :=
    UInt256.ofNat (MachineState.M aDone.aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add aDone.fp rounded)).write 0 aDone.mem 64 32
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M aw1.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd1381 := evm_run rd1363 with [
    push1 ⟨64⟩,
    raw mload (Cₘ aw1 - Cₘ aDone.aw) aDone.fp aw1 (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, aw1])
      aDone.hfpLoad (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem2 aw2 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2])
      (by rfl) (by rfl) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 aDone.fp.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat aDone.fp.toNat 32)
  have rd1384 := evm_run rd1381 with [
    returndatasize, dup3,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem3 aw3 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3])
      (by rfl) (by rfl) (by evm_ov)]
  have rd1390 := evm_run rd1384 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := aDone.fp + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat out.size
  have hcopyLen_toNat : copyLen.toNat = out.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := out.write 0 mem3 copyDest.toNat copyLen.toNat
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat copyDest.toNat copyLen.toNat)
  have rd1391 := RD.returndatacopy
    (Cₘ aw4 - Cₘ aw3) mem4 aw4
    rd1390 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen, aw4,
        hcopyLen_toNat])
    (by rfl) (by rfl) (by evm_ov)
  have rd1400 := evm_run rd1391 with [push2 ⟨1400⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd1400 with [pop, pop, swap1, pop]⟩

omit hperm henvDone rd1349 hawCall in
theorem scratch_blindAuctionReveal_postLoop_callMade_failure
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {out : ByteArray} {k1350 C1350 : ℕ} {evmSCall : EVM.State}
    (houtSize : out.size < UInt256.size)
    (rd1350 : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
      [⟨0⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund,
        loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      aDone.mem aDone.aw out (cA', σ') k1350 C1350)
    (hcallS :
      callViaEVM evmDone (EVM.address evmDone.executionEnv.source)
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (false, evmSCall, out)) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract
        evmSolm callargs revealTransition.body .reverted := by
    exact
      scratch_blindAuctionRevealBodyReverts_callFailure_fromLoopOfLocals
        evmSolm evmDone evmSCall callargs LDone values fakes secrets
        loopLen aDone.refund out
        hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by rw [hstore]; simp) hvaluesGet hfakesGet hsecretsGet
        hlenBodyLoop hvaluesLenLoop hfakesLenLoop hsecretsLenLoop
        hrefundDone hloop hcallS
  by_cases hout0 : out.size = 0
  · as_aux_lemma =>
    have houtEmpty : out = ByteArray.empty := by
      apply ByteArray.ext
      change out.data = #[]
      exact Array.eq_empty_of_size_eq_zero (by
        change out.size = 0
        exact hout0)
    obtain ⟨k1405, C1405, rd1405⟩ : ∃ k' C',
        RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1405⟩
          [⟨0⟩, aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
            revealScratchBiddingEndWord σ_evm I, secretsLenWord,
            ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
            ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
            ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
          aDone.mem aDone.aw ByteArray.empty (cA', σ') k' C' := by
      have rd1350Empty : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
          [⟨0⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩,
            aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
            revealScratchBiddingEndWord σ_evm I, secretsLenWord,
            ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
            ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
            ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
          aDone.mem aDone.aw ByteArray.empty (cA', σ') k1350 C1350 := by
        simpa [houtEmpty] using rd1350
      refine ⟨_, _, evm_run rd1350Empty with [
        swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq,
        push2 ⟨1395⟩, jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩,
        swap2, pop, jumpdest, pop, pop, swap1, pop]⟩
    have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      have rd1410 := evm_run rd1405 with [
        dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
      exact RD.rev _ rd1410 (by decide)
        (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
        (by evm_ov)
    exact hrev.reEquivExecutionRevert hcode hd hdec (by
      rw [hevmSolm] at hbody
      exact hbody)
  · as_aux_lemma =>
    obtain ⟨mem1405, aw1405, k1405, C1405, rd1405⟩ :=
      scratch_blindAuctionReveal_postLoop_postCallNonempty
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (loopLen := loopLen)
        (secretsLenWord := secretsLenWord) (fakesLenWord := fakesLenWord)
        (valuesLenWord := valuesLenWord) (aDone := aDone)
        (cA' := cA') (σ' := σ') (out := out) (k := k1350) (C := C1350)
        (z := ⟨0⟩) rd1350 hout0 houtSize
    have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      have rd1410 := evm_run rd1405 with [
        dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
      exact RD.rev _ rd1410 (by decide)
        (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
        (by evm_ov)
    exact hrev.reEquivExecutionRevert hcode hd hdec (by
      rw [hevmSolm] at hbody
      exact hbody)

omit hperm henvDone rd1349 hawCall in
theorem scratch_blindAuctionReveal_postLoop_callMade_success
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {out : ByteArray} {k1350 C1350 : ℕ} {evmSCall : EVM.State}
    (houtSize : out.size < UInt256.size)
    (hCreated : cA' = evmSCall.createdAccounts)
    (hAccounts : accountMapEquiv σ' evmSCall.accountMap)
    (rd1350 : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
      [⟨1⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩, aDone.refund,
        loopLen, revealScratchRevealEndWord σ_evm I,
        revealScratchBiddingEndWord σ_evm I, secretsLenWord,
        ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
        ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
        ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
      aDone.mem aDone.aw out (cA', σ') k1350 C1350)
    (hcallS :
      callViaEVM evmDone (EVM.address evmDone.executionEnv.source)
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (true, evmSCall, out)) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract
        evmSolm callargs revealTransition.body
        (.returned
          ({ contract := blindAuctionContract,
             locals := scratch_revealCallStoreOf LDone true out } :
            Frame)
          evmSCall none) := by
    exact
      scratch_blindAuctionRevealBodyReturns_callSuccess_fromLoopOfLocals
        evmSolm evmDone evmSCall callargs LDone values fakes secrets
        loopLen aDone.refund out
        hwvSolm hafterBody hbeforeBody hbiddingAbsent hrevealAbsent
        (by rw [hstore]; simp) hvaluesGet hfakesGet hsecretsGet
        hlenBodyLoop hvaluesLenLoop hfakesLenLoop hsecretsLenLoop
        hrefundDone hloop hcallS
  by_cases hout0 : out.size = 0
  · as_aux_lemma =>
    have houtEmpty : out = ByteArray.empty := by
      apply ByteArray.ext
      change out.data = #[]
      exact Array.eq_empty_of_size_eq_zero (by
        change out.size = 0
        exact hout0)
    obtain ⟨k1405, C1405, rd1405⟩ : ∃ k' C',
        RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1405⟩
          [⟨1⟩, aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
            revealScratchBiddingEndWord σ_evm I, secretsLenWord,
            ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
            ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
            ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
          aDone.mem aDone.aw ByteArray.empty (cA', σ') k' C' := by
      have rd1350Empty : RD blindAuctionBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1350⟩
          [⟨1⟩, aDone.fp, aDone.refund, revealScratchSenderWord I, ⟨0⟩,
            aDone.refund, loopLen, revealScratchRevealEndWord σ_evm I,
            revealScratchBiddingEndWord σ_evm I, secretsLenWord,
            ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩, fakesLenWord,
            ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩, valuesLenWord,
            ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩, ⟨276⟩, blindAuctionSelWord I]
          aDone.mem aDone.aw ByteArray.empty (cA', σ') k1350 C1350 := by
        simpa [houtEmpty] using rd1350
      refine ⟨_, _, evm_run rd1350Empty with [
        swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq,
        push2 ⟨1395⟩, jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩,
        swap2, pop, jumpdest, pop, pop, swap1, pop]⟩
    have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA', σ') ByteArray.empty := by
      have rd1413 := evm_run rd1405 with [
        dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
      have rd276 := evm_run rd1413 with [
        jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
        jump (by jump_dest), jumpdest]
      exact rd276.stop (by decide) (by evm_ov)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
      (by
        rw [hevmSolm] at hbody
        exact hbody)
      hCreated
      hAccounts
      (returnEquiv.fallthrough rfl rfl (by decide +native))
  · as_aux_lemma =>
    obtain ⟨mem1405, aw1405, k1405, C1405, rd1405⟩ :=
      scratch_blindAuctionReveal_postLoop_postCallNonempty
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (loopLen := loopLen)
        (secretsLenWord := secretsLenWord) (fakesLenWord := fakesLenWord)
        (valuesLenWord := valuesLenWord) (aDone := aDone)
        (cA' := cA') (σ' := σ') (out := out) (k := k1350) (C := C1350)
        (z := ⟨1⟩) rd1350 hout0 houtSize
    have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA', σ') ByteArray.empty := by
      have rd1413 := evm_run rd1405 with [
        dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
      have rd276 := evm_run rd1413 with [
        jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
        jump (by jump_dest), jumpdest]
      exact rd276.stop (by decide) (by evm_ov)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
      (by
        rw [hevmSolm] at hbody
        exact hbody)
      hCreated
      hAccounts
      (returnEquiv.fallthrough rfl rfl (by decide +native))

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_postLoop_callMade_fromCall
    (hσ0Done : evmDone.σ₀ = σ₀)
    (hghDone : evmDone.genesisBlockHeader = gh)
    (hblDone : evmDone.blocks = bl)
    (hcreatedDone : evmDone.createdAccounts = aDone.acc.1)
    (hsubDone : evmDone.substate = A)
    (haccountsDone : accountMapEquiv aDone.acc.2 evmDone.accountMap)
    (hdepthLt : I.depth.val < 1024)
    (hdepthNe : ¬ I.depth = 1024)
    (hbalance :
      aDone.refund ≤ (aDone.acc.2.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨cA', σ', z, out, A_in, callGas, k1350, C1350,
      hTheta, houtSize, rd1350⟩ :=
    scratch_blindAuctionReveal_postLoop_callMade_step
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (loopLen := loopLen) (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
      (aDone := aDone) (gasArg := gasArg) (k1349 := k1349) (C1349 := C1349)
      hperm rd1349 hawCall hdepthLt hbalance
  let evmEDone : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := aDone.acc.2,
      createdAccounts := aDone.acc.1 }
  have hAddressId (a : AccountAddress) : EVM.address a = a := by
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt a.isLt
  have hTargetEq :
      AccountAddress.ofUInt256 (revealScratchSenderWord I) =
        EVM.address evmDone.executionEnv.source := by
    calc
      AccountAddress.ofUInt256 (revealScratchSenderWord I) = I.source := by
        simpa [revealScratchSenderWord] using accountAddress_roundtrip I.source
      _ = EVM.address evmDone.executionEnv.source := by
        simp [henvDone, hAddressId]
  have htransport
      {evmECall : EVM.State} {z' : Bool} {out' : ByteArray}
      (hcallE :
        callViaEVM evmEDone
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (Int.ofNat aDone.refund.toNat) ByteArray.empty
          (z', evmECall, out')) :
      ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
        callViaEVM evmDone
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (Int.ofNat aDone.refund.toNat) ByteArray.empty
          (z',
            { evmDone with
              accountMap := σ'_solm,
              substate := A'_solm,
              createdAccounts := evmECall.createdAccounts },
            out') ∧
        accountMapEquiv evmECall.accountMap σ'_solm := by
    exact callViaEVM_accountMapEquiv
      (storage := blindAuctionConfig.storage)
      (evm_solm := evmDone) hcallE
      (by simpa [evmEDone] using haccountsDone)
      (by simpa [evmEDone, initState] using hσ0Done.symm)
      (by simpa [evmEDone, initState] using hcreatedDone)
      (by simpa [evmEDone, initState] using hghDone)
      (by simpa [evmEDone, initState] using hblDone)
      (by simpa [evmEDone, initState] using hsubDone)
      (by simpa [evmEDone, initState] using henvDone)
  obtain ⟨g'', A', hThetaEq⟩ := hTheta
  let evmECall : EVM.State :=
    { evmEDone with
      accountMap := σ',
      substate := A',
      createdAccounts := cA' }
  have hcallE :
      callViaEVM evmEDone
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (z, evmECall, out) := by
    refine callViaEVM.callMade
      (valueWord := aDone.refund)
      (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
      ?_ ?_ ?_ ?_ ?_
    · exact (wordOfInt_ofNat_toNat aDone.refund).symm
    · refine ⟨callGas, A_in, ?_⟩
      simpa [evmEDone, evmECall, initState, hperm,
        revealScratchSenderWord, accountAddress_roundtrip] using hThetaEq
    · simp [evmECall]
    · simpa [evmEDone, initState] using hbalance
    · intro hd'
      exact hdepthNe (by simpa [evmEDone, initState] using hd')
  obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
    htransport hcallE
  let evmSCall : EVM.State :=
    { evmDone with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := evmECall.createdAccounts }
  have hcallS :
      callViaEVM evmDone (EVM.address evmDone.executionEnv.source)
        (Int.ofNat aDone.refund.toNat) ByteArray.empty
        (z, evmSCall, out) := by
    simpa [evmSCall, hTargetEq] using hcallSRaw
  cases z
  · exact scratch_blindAuctionReveal_postLoop_callMade_failure
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
      (loopLen := loopLen) (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
      (aDone := aDone) (LDone := LDone) (evmSolm := evmSolm) (evmDone := evmDone)
      (cA' := cA') (σ' := σ') (out := out) (k1350 := k1350) (C1350 := C1350)
      (evmSCall := evmSCall)
      hcode hd hdec hstore hevmSolm hwvSolm hafterBody hbeforeBody hbiddingAbsent
      hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop hvaluesLenLoop
      hfakesLenLoop hsecretsLenLoop hrefundDone hloop houtSize
      (by simpa using rd1350)
      (by simpa using hcallS)
  · have hCreated : cA' = evmSCall.createdAccounts := by
      simp [evmSCall, evmECall]
    have hAccounts : accountMapEquiv σ' evmSCall.accountMap := by
      simpa [evmSCall, evmECall] using hPostAccounts
    exact scratch_blindAuctionReveal_postLoop_callMade_success
      (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (callargs := callargs) (values := values) (fakes := fakes) (secrets := secrets)
      (loopLen := loopLen) (secretsLenWord := secretsLenWord)
      (fakesLenWord := fakesLenWord) (valuesLenWord := valuesLenWord)
      (aDone := aDone) (LDone := LDone) (evmSolm := evmSolm) (evmDone := evmDone)
      (cA' := cA') (σ' := σ') (out := out) (k1350 := k1350) (C1350 := C1350)
      (evmSCall := evmSCall)
      hcode hd hdec hstore hevmSolm hwvSolm hafterBody hbeforeBody hbiddingAbsent
      hrevealAbsent hvaluesGet hfakesGet hsecretsGet hlenBodyLoop hvaluesLenLoop
      hfakesLenLoop hsecretsLenLoop hrefundDone hloop houtSize hCreated hAccounts
      (by simpa using rd1350)
      (by simpa using hcallS)

end Branches

end BlindAuction
