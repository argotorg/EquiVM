import Examples.BlindAuction.Reveal.Loop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000
namespace BlindAuction

/-- `reveal(uint256[],bool[],bytes32[])` body (pc 387) refines its transition. -/
theorem blindAuctionRevealBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨387⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionRevealSelector_size hsel
  have hd := blindAuctionDispatch_reveal (cd := I.calldata) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have _hdecodeEntry :=
      blindAuctionX_reveal_decodeEntry (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hshortHead : I.calldata.size < 100
    · have hdecNone := blindAuctionDecode_reveal_none_short (I := I) hsz hshortHead
      have hslt :
          UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
            ⟨1⟩ := by
        have h :=
          solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
            hsz hshortHead hsize (by omega)
        simpa using h
      have hrev := blindAuctionRevealX_decode_head_revert
        (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
      exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · by_cases hhuge : 2 ^ 255 + 4 ≤ I.calldata.size
      · have hdecNone := blindAuctionDecode_reveal_none_huge (I := I) hhuge
        have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨1⟩ := by
          have h :=
            solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
              hhuge hsize (by omega)
          simpa using h
        have hrev := blindAuctionRevealX_decode_head_revert
          (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        exact hrev.reEquivDecodingFailed hcode hd hdecNone
      · have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨0⟩ := by
          have h :=
            solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
              (by omega) (by omega) hsize
          simpa using h
        obtain ⟨k1806, C1806, rd1806⟩ :=
          blindAuctionRevealX_decode_head_ok (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        by_cases hcalldataSign : I.calldata.size < 2 ^ 255
        · by_cases hdecNone :
              decodeCalldata (revealTransition.params.map Param.name)
                (transitionSignature revealTransition).paramTypes I.calldata = none
          · have hrev :=
              scratch_blindAuctionRevealDecode1806_none_reverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 (by omega)
                hcalldataSign hdecNone
            exact hrev.reEquivDecodingFailed hcode hd hdecNone
          · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
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
              initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
              simpa [evmSolm, initState] using hwv
            have hbiddingAbsent : callargs.get? biddingEndRef.base = none :=
              blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
            have hrevealAbsent : callargs.get? revealEndRef.base = none :=
              blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
            have hbidsEq := revealScratchBidsLengthWord_accountMapEquiv hAccounts I
            have hbiddingEq := revealScratchBiddingEndWord_accountMapEquiv hAccounts I
            have hrevealEq := revealScratchRevealEndWord_accountMapEquiv hAccounts I
            have hbidsHash := revealScratchBidsMappingBaseKeccak I
            by_cases hafter :
                (revealScratchBiddingEndWord σ_evm I).toNat <
                  (revealScratchTimestampWord I).toNat
            · by_cases hbefore :
                  (revealScratchTimestampWord I).toNat <
                    (revealScratchRevealEndWord σ_evm I).toNat
              · have hafterBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchBiddingEndWord σ_solm I).toNat <
                    (revealScratchTimestampWord I).toNat
                  rw [← hbiddingEq]
                  exact hafter
                have hbeforeBody :
                    (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat <
                      (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat := by
                  change (revealScratchTimestampWord I).toNat <
                    (revealScratchRevealEndWord σ_solm I).toNat
                  rw [← hrevealEq]
                  exact hbefore
                have hlenBody :
                    Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                      (bidsBase (.address evmSolm.executionEnv.source)) =
                        revealScratchBidsLengthWord σ_solm I := by
                  rfl
                by_cases hvaluesEq :
                    revealScratchBidsLengthWord σ_evm I = valuesLenWord
                · by_cases hfakesEq :
                      revealScratchBidsLengthWord σ_evm I = fakesLenWord
                  · by_cases hsecretsEq :
                        revealScratchBidsLengthWord σ_evm I = secretsLenWord
                    · have h963 :=
                        blindAuctionRevealX_from887_afterTimeGuards
                          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀
                            (Sat256.ofUInt256 g) A I)
                          rd887 hafter hbefore
                      rcases h963 with ⟨_, _, rd963⟩
                      by_cases hbidsZero :
                          revealScratchBidsLengthWord σ_evm I = ⟨0⟩
                      · have hvaluesWordZero : valuesLenWord = ⟨0⟩ := by
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
                              hout255, rd1350⟩ :=
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
                                  (lt_size_of_lt_sign hout255)
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
                                (returnEquiv.void rfl rfl rfl)
                            · obtain ⟨_, _, _, _, rd1405⟩ :=
                                blindAuctionRevealX_postCallNonempty_toRequire
                                  (by simpa using rd1350) hout0
                                  (lt_size_of_lt_sign hout255)
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
                                (returnEquiv.void rfl rfl rfl)
                      · sorry
                    · have hrev :=
                        blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
                          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                        rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
                        hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
                        hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
                        hsecretsEnd hafter hbefore hvaluesEq hfakesEq hsecretsEq hbidsHash
                      have hsecretsNeNat :
                          secrets.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                        intro hnat
                        apply hsecretsEq
                        apply u256_inj
                        rw [hbidsEq]
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
                        (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                        rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax
                        hvaluesEnd hfakesGt hfakesStart hfakesLenLoad hfakesLenMax
                        hfakesEnd hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax
                        hsecretsEnd hafter hbefore hvaluesEq hfakesEq hbidsHash
                    have hfakesNeNat :
                        fakes.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                      intro hnat
                      apply hfakesEq
                      apply u256_inj
                      rw [hbidsEq]
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
                      (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                      rd1806 hvaluesGt hvaluesStart hvaluesLenLoad hvaluesLenMax hvaluesEnd
                      hfakesGt hfakesStart hfakesLenLoad hfakesLenMax hfakesEnd
                      hsecretsGt hsecretsStart hsecretsLenLoad hsecretsLenMax hsecretsEnd
                      hafter hbefore hvaluesEq hbidsHash
                  have hvaluesNeNat :
                      values.length ≠ (revealScratchBidsLengthWord σ_solm I).toNat := by
                    intro hnat
                    apply hvaluesEq
                    apply u256_inj
                    rw [hbidsEq]
                    omega
                  have hbody :
                      ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                        callargs revealTransition.body .reverted := by
                    exact blindAuctionRevealBodyReverts_decoded_lengthMismatch
                      evmSolm hdec hvaluesGet hfakesGet hsecretsGet hwvSolm hafterBody
                      hbeforeBody hlenBody (Or.inl hvaluesNeNat)
                  exact hrev.reEquivExecutionRevert hcode hd hdec hbody
              · have hrev := blindAuctionRevealX_from887_tooLate
                    (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    rd887 hafter (Nat.le_of_not_gt hbefore)
                have hafterBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat <
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchBiddingEndWord σ_solm I).toNat <
                    (revealScratchTimestampWord I).toNat
                  rw [← hbiddingEq]
                  exact hafter
                have hlateBody :
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩).toNat ≤
                      (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat := by
                  change (revealScratchRevealEndWord σ_solm I).toNat ≤
                    (revealScratchTimestampWord I).toNat
                  rw [← hrevealEq]
                  exact Nat.le_of_not_gt hbefore
                have hbody :
                    ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                      callargs revealTransition.body .reverted := by
                  exact blindAuctionRevealBodyReverts_tooLate hwvSolm hbiddingAbsent
                    hrevealAbsent hafterBody hlateBody
                exact hrev.reEquivExecutionRevert hcode hd hdec hbody
            · have hrev := blindAuctionRevealX_from887_tooEarly
                  (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  rd887 (Nat.le_of_not_gt hafter)
              have htimeBody :
                  (UInt256.ofNat evmSolm.executionEnv.header.timestamp).toNat ≤
                    (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩).toNat := by
                change (revealScratchTimestampWord I).toNat ≤
                  (revealScratchBiddingEndWord σ_solm I).toNat
                rw [← hbiddingEq]
                exact Nat.le_of_not_gt hafter
              have hbody :
                  ExecTransitionBody blindAuctionConfig blindAuctionContract evmSolm
                    callargs revealTransition.body .reverted := by
                exact blindAuctionRevealBodyReverts_tooEarly hwvSolm hbiddingAbsent htimeBody
              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
        · have hcalldataGe : 2 ^ 255 ≤ I.calldata.size := by omega
          have hdecNone := blindAuctionDecode_reveal_none_huge_dynamic (I := I) hcalldataGe
          have hrev :=
            blindAuctionRevealDecode1806_hugeDynamic_reverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 hcalldataGe hsize
          exact hrev.reEquivDecodingFailed hcode hd hdecNone
  · have hrev := blindAuctionX_reveal_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hdecNone :
        decodeCalldata (revealTransition.params.map Param.name)
          (transitionSignature revealTransition).paramTypes I.calldata = none
    · exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
            revealTransition.body .reverted := by
        exact blindAuctionRevealBodyReverts_nonpayable
          (by simp only [initState]; exact hwv)
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
