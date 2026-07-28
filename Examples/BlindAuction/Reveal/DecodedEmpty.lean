import Examples.BlindAuction.Reveal.PostLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

set_option maxHeartbeats 10000000 in
theorem scratch_blindAuctionReveal_decoded_empty_bids
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {callargs : Store} {values fakes secrets : List Value}
    {valuesLenWord fakesLenWord secretsLenWord : UInt256}
    (hcode : I.code = blindAuctionBytecode)
    (hperm : I.perm = true)
    (hd : dispatchMsg blindAuctionContract I.calldata = some revealTransition)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hwv : I.weiValue = ⟨0⟩)
    (hvaluesGet : callargs.get? "values" = some (.array values))
    (hfakesGet : callargs.get? "fakes" = some (.array fakes))
    (hsecretsGet : callargs.get? "secrets" = some (.array secrets))
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
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
    (hbidsZero : revealScratchBidsLengthWord σ_evm I = ⟨0⟩)
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
  have hvaluesWordZero : valuesLenWord = ⟨0⟩ := by
    rw [← hvaluesEq, hbidsZero]
  have hfakesWordZero : fakesLenWord = ⟨0⟩ := by
    rw [← hfakesEq, hbidsZero]
  have hsecretsWordZero : secretsLenWord = ⟨0⟩ := by
    rw [← hsecretsEq, hbidsZero]
  have hvaluesLenZero : values.length = 0 := by
    rw [hvaluesListLen, hvaluesWordZero]
    rfl
  have hfakesLenZero : fakes.length = 0 := by
    rw [hfakesListLen, hfakesWordZero]
    rfl
  have hsecretsLenZero : secrets.length = 0 := by
    rw [hsecretsListLen, hsecretsWordZero]
    rfl
  have hvaluesNil : values = [] :=
    List.eq_nil_of_length_eq_zero hvaluesLenZero
  have hfakesNil : fakes = [] :=
    List.eq_nil_of_length_eq_zero hfakesLenZero
  have hsecretsNil : secrets = [] :=
    List.eq_nil_of_length_eq_zero hsecretsLenZero
  have hvaluesGetEmpty :
      callargs.get? "values" = some (.array []) := by
    simpa [hvaluesNil] using hvaluesGet
  have hfakesGetEmpty :
      callargs.get? "fakes" = some (.array []) := by
    simpa [hfakesNil] using hfakesGet
  have hsecretsGetEmpty :
      callargs.get? "secrets" = some (.array []) := by
    simpa [hsecretsNil] using hsecretsGet
  have hcallargsEmpty : callargs = revealEmptyStore :=
    blindAuctionDecode_reveal_callargs_empty_eq hdec hvaluesGetEmpty
      hfakesGetEmpty hsecretsGetEmpty
  have hlenZeroBody :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
        (bidsBase (.address evmSolm.executionEnv.source)) = ⟨0⟩ := by
    rw [hlenBody, ← hbidsEq, hbidsZero]
  by_cases hdepthEq : I.depth = 1024
  · obtain ⟨_, _, rd1350⟩ :=
      blindAuctionRevealX_from963_empty_callDepth
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g)
          hdepthEq
          (by
            simpa [hvaluesWordZero, hfakesWordZero, hsecretsWordZero]
              using rd963)
          hbidsZero hbidsHash
    let evmSFail : EVM.State :=
      { evmSolm with
        substate := (evmSolm.addAccessedAccount
          (EVM.address evmSolm.executionEnv.source)).substate }
    have hcallS :
        callViaEVM evmSolm (EVM.address evmSolm.executionEnv.source)
          0 ByteArray.empty (false, evmSFail, ByteArray.empty) := by
      apply callViaEVM.callNotMade
      · rfl
      · rfl
      · rintro ⟨_, hdepthNe⟩
        exact hdepthNe (by
          simpa [evmSolm, initState] using hdepthEq)
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
          callargs revealTransition.body .reverted := by
      have hbodyEmpty :
          ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
            revealEmptyStore revealTransition.body .reverted :=
        blindAuctionRevealBodyReverts_empty_callFailure evmSolm evmSFail
          ByteArray.empty hwvSolm hafterBody hbeforeBody hlenZeroBody
          hcallS
      simpa [hcallargsEmpty] using hbodyEmpty
    have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I) :=
      blindAuctionRevealX_postCallEmpty_failure_revert
        (by simpa using rd1350)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody
  · have hdepthLt : I.depth.val < 1024 := by
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      have hneVal : I.depth.val ≠ 1024 := by
        intro hv
        exact hdepthEq (Fin.ext hv)
      omega
    obtain ⟨cA', σ', z, out, A_in, callGas, _, _, hTheta,
        houtSize, rd1350⟩ :=
      blindAuctionRevealX_from963_empty_callMade
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g)
          hdepthLt
          (by
            simpa [hvaluesWordZero, hfakesWordZero, hsecretsWordZero]
              using rd963)
          hbidsZero hbidsHash
    rcases hTheta with ⟨g'', A', hThetaEq⟩
    let evmECall : EVM.State :=
      { initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I with
        accountMap := σ',
        substate := A',
        createdAccounts := cA' }
    have hAddressId (a : AccountAddress) : EVM.address a = a := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt a.isLt
    have hcallE :
        callViaEVM
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I)
          (EVM.address I.source) 0 ByteArray.empty
          (z, evmECall, out) := by
      refine callViaEVM.callMade
        (valueWord := (⟨0⟩ : UInt256))
        (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
        wordOfInt_zero.symm ?_ ?_ ?_ ?_
      · refine ⟨callGas, A_in, ?_⟩
        simpa [evmECall, initState, hperm, revealScratchSenderWord,
          hAddressId, accountAddress_roundtrip] using hThetaEq
      · rfl
      · show (⟨0⟩ : UInt256) ≤ _
        exact Fin.zero_le _
      · intro hd'
        apply hdepthEq
        simpa [initState] using hd'
    obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
      callViaEVM_initState_accountMapEquiv
        (storage := blindAuctionConfig.storage) hcallE hAccounts
    let evmSCall : EVM.State :=
      { evmSolm with
        accountMap := σ'_solm,
        substate := A'_solm,
        createdAccounts := evmECall.createdAccounts }
    have hcallS :
        callViaEVM evmSolm (EVM.address evmSolm.executionEnv.source)
          0 ByteArray.empty (z, evmSCall, out) := by
      simpa [evmSolm, evmSCall, evmECall, initState] using hcallSRaw
    cases z
    · have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            evmSolm callargs revealTransition.body .reverted := by
        have hbodyEmpty :
            ExecTransitionBody blindAuctionConfig blindAuctionContract
              evmSolm revealEmptyStore revealTransition.body .reverted :=
          blindAuctionRevealBodyReverts_empty_callFailure evmSolm evmSCall
            out hwvSolm hafterBody hbeforeBody hlenZeroBody hcallS
        simpa [hcallargsEmpty] using hbodyEmpty
      by_cases hout0 : out.size = 0
      · have houtEmpty : out = ByteArray.empty := by
          apply ByteArray.ext
          change out.data = #[]
          exact Array.eq_empty_of_size_eq_zero (by
            change out.size = 0
            exact hout0)
        have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I) :=
          blindAuctionRevealX_postCallEmpty_failure_revert
            (by simpa [houtEmpty] using rd1350)
        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
      · obtain ⟨_, _, _, _, rd1405⟩ :=
          blindAuctionRevealX_postCallNonempty_toRequire
            (by simpa using rd1350) hout0
            houtSize
        have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I) :=
          blindAuctionRevealX_postCallRequire_failure_revert
            (by simpa using rd1405)
        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
    · have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            evmSolm callargs revealTransition.body
          (.returned
            { contract := blindAuctionContract,
              locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
            evmSCall none) := by
        have hbodyEmpty :
            ExecTransitionBody blindAuctionConfig blindAuctionContract
              evmSolm revealEmptyStore revealTransition.body
              (.returned
                { contract := blindAuctionContract,
                  locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
                evmSCall none) :=
          blindAuctionRevealBodyReturns_empty_callSuccess evmSolm
            evmSCall out hwvSolm hafterBody hbeforeBody hlenZeroBody
            hcallS
        simpa [hcallargsEmpty] using hbodyEmpty
      by_cases hout0 : out.size = 0
      · have houtEmpty : out = ByteArray.empty := by
          apply ByteArray.ext
          change out.data = #[]
          exact Array.eq_empty_of_size_eq_zero (by
            change out.size = 0
            exact hout0)
        have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I)
            (cA', σ') ByteArray.empty :=
          blindAuctionRevealX_postCallEmpty_success_stop
            (by simpa [houtEmpty] using rd1350)
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
          hbody
          (by rfl)
          (by
            change accountMapEquiv σ' σ'_solm
            simpa [evmECall] using hPostAccounts)
          (returnEquiv.fallthrough rfl rfl (by native_decide))
      · obtain ⟨_, _, _, _, rd1405⟩ :=
          blindAuctionRevealX_postCallNonempty_toRequire
            (by simpa using rd1350) hout0
            houtSize
        have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀
              (Sat256.ofUInt256 g) A I)
            (cA', σ') ByteArray.empty :=
          blindAuctionRevealX_postCallRequire_success_stop
            (by simpa using rd1405)
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec
          hbody
          (by rfl)
          (by
            change accountMapEquiv σ' σ'_solm
            simpa [evmECall] using hPostAccounts)
          (returnEquiv.fallthrough rfl rfl (by native_decide))

end BlindAuction
