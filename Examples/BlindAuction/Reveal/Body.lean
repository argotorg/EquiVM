import Examples.BlindAuction.Reveal.BodyCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

namespace BlindAuction

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoopBody_fromLoopStart {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate}
    {loopLen revealEnd biddingEnd secretsLenWord secretsEnd fakesLenWord fakesEnd
      valuesLenWord valuesEnd sel : UInt256}
    {values fakes secrets : List Value} {callargs : Store}
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hsecretsEnd : secretsEnd = ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
    (hfakesEnd : fakesEnd = ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
    (hvaluesEnd : valuesEnd = ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
    (hvaluesEq : loopLen = valuesLenWord)
    (hfakesEq : loopLen = fakesLenWord)
    (hsecretsEq : loopLen = secretsLenWord)
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
    (hvaluesLenMax : UInt256.gt valuesLenWord revealMaxU64 = ⟨0⟩) :
    ∀ v a L evm,
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm → ∀ k C,
        RD blindAuctionBytecode I g s0
          ⟨1023⟩
          (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
            secretsLenWord secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel)
          a.mem a.aw ByteArray.empty a.acc k C →
        RevealLoopBodyOutcome I g s0 σ₀ gh bl A v k C loopLen revealEnd biddingEnd
          secretsLenWord secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel
          values fakes secrets a L evm := by
  intro v a L evm hInv k C rd1023
  have hInvOrig :
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm := hInv
  rcases hInv with
    ⟨hiL, hlenL, hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      hvariant, hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub,
      haccounts⟩
  let curLen : UInt256 :=
    (a.acc.2.find? I.codeOwner).option ⟨0⟩
      (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩)
  have hlenLoad :
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) =
        curLen := rfl
  have hlenSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen := by
    have hfind :=
      accountMapEquiv_storage_findD haccounts I.codeOwner
        (revealScratchBidsLengthSlot I) ⟨0⟩
    dsimp [curLen]
    rw [henv]
    simpa [Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, revealScratchBidsLengthSlot, bidsBase,
      blindAuctionMappingSlot] using hfind.symm
  have hbaseHashWord :=
    BlindAuction.scratch_revealBidsMappingBaseKeccak_any I a.mem
  let baseHashInput : ByteArray :=
    (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
      ((UInt256.toByteArray (revealScratchSenderWord I)).write 0
        a.mem 0 32) 32 32).readWithPadding 0 64)
  have hbaseRoundtrip :
      UInt256.toByteArray (uInt256OfByteArray (ffi.KEC baseHashInput)) =
        ffi.KEC baseHashInput := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_data_toByteArray]
    rw [← byteArray_toList_eq]
    simp [toBytesBE_keccak_uInt256OfByteArray]
  have hbaseHash :
      ffi.KEC
        (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
          ((UInt256.toByteArray (revealScratchSenderWord I)).write 0
            a.mem 0 32) 32 32).readWithPadding 0 64) =
        UInt256.toByteArray (revealScratchBidsLengthSlot I) := by
    dsimp [baseHashInput] at hbaseRoundtrip
    rw [← hbaseRoundtrip]
    rw [uInt256OfByteArray_eq]
    rw [hbaseHashWord]
  have hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0
                a.mem 0 32) 32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray
          (ffi.KEC
            (UInt256.toByteArray (revealScratchBidsLengthSlot I))) := by
    exact BlindAuction.scratch_revealBidsArrayDataKeccak_any I
      ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
        ((UInt256.toByteArray (revealScratchSenderWord I)).write 0
          a.mem 0 32) 32 32)
  have hidxLtLoop : a.idx.toNat < loopLen.toNat := by
    omega
  by_cases hboundBids : a.idx.toNat < curLen.toNat
  · have hvalueBound : a.idx.toNat < valuesLenWord.toNat := by
      simpa [hvaluesEq] using hidxLtLoop
    have hfakesBound : a.idx.toNat < fakesLenWord.toNat := by
      simpa [hfakesEq] using hidxLtLoop
    have hsecretsBound : a.idx.toNat < secretsLenWord.toNat := by
      simpa [hsecretsEq] using hidxLtLoop
    have hboundValues : a.idx.toNat < values.length := by
      rw [hvaluesListLen]
      exact hvalueBound
    have hboundFakes : a.idx.toNat < fakes.length := by
      rw [hfakesListLen]
      exact hfakesBound
    have hboundSecrets : a.idx.toNat < secrets.length := by
      rw [hsecretsListLen]
      exact hsecretsBound
    obtain ⟨e0, e1, e2, hval0, hval1, hval2⟩ :=
      blindAuctionDecode_reveal_array_decodes hdec hstore
    obtain ⟨value, hvalueLookup⟩ :=
      revealDecode_dynamicArray_uint256_lookup_shape hval0 hboundValues
    obtain ⟨word, hfakeLookup⟩ :=
      revealDecode_dynamicArray_bool_lookup_shape hval1 hboundFakes
    obtain ⟨secret, hsecretLookup⟩ :=
      revealDecode_dynamicArray_bytes32_lookup_shape hval2 hboundSecrets
    let fakeWord : UInt256 := UInt256.ofNat word
    have hvalueLoad :
        uInt256OfByteArray
              (I.calldata.readBytes
              (UInt256.mul ⟨32⟩ a.idx + valuesEnd).toNat
              32) = value := by
      simpa [hvaluesEnd] using
        blindAuctionDecode_reveal_values_load hsize hdec hstore hvalueLookup
    have hfakeLoad :
        uInt256OfByteArray
              (I.calldata.readBytes
              (UInt256.mul ⟨32⟩ a.idx + fakesEnd).toNat
              32) = fakeWord := by
      simpa [fakeWord, hfakesEnd] using
        blindAuctionDecode_reveal_fakes_load hsize hdec hstore hfakeLookup
    have hsecretLoad :
        uInt256OfByteArray
              (I.calldata.readBytes
              (UInt256.mul ⟨32⟩ a.idx + secretsEnd).toNat
              32) = secret := by
      simpa [hsecretsEnd] using
        blindAuctionDecode_reveal_secrets_load hsize hdec hstore hsecretLookup
    have hfakeSlt :
        UInt256.slt
            (UInt256.sub (UInt256.mul ⟨32⟩ a.idx + fakesEnd + ⟨32⟩)
              (UInt256.mul ⟨32⟩ a.idx + fakesEnd)) ⟨32⟩ = ⟨0⟩ := by
      simpa [hfakesEnd] using
        BlindAuction.scratch_blindAuctionDecode_reveal_fakes_slt hsize hdec hstore hfakeLookup
    have hfakeWordSmall :
        (UInt256.ofNat word).toNat = word :=
      BlindAuction.scratch_blindAuctionDecode_reveal_fakes_word_toNat
        hdec hstore hfakeLookup
    have hloopLenLe : loopLen.toNat ≤ solcMaxU64 := by
      have hle := scratch_word_le_solcMax_of_ugt_zero hvaluesLenMax
      simpa [hvaluesEq] using hle
    have hfp128 : a.fp.toNat + 128 < UInt256.size := by
      have hidxLe : a.idx.toNat ≤ solcMaxU64 := by omega
      exact RevealLoopCursor.fp_add128_lt_size_of_idx_le a hidxLe
    have hfp96 : 96 ≤ a.fp.toNat := by
      rw [a.hfpIdx]
      omega
    exact scratch_revealLoopBody_decoded_inBounds_fromLoopStart
      (I := I) (g := g) (s0 := s0)
      (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C)
      (loopLen := loopLen) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLenWord := secretsLenWord)
      (secretsEnd := secretsEnd)
      (fakesLenWord := fakesLenWord)
      (fakesEnd := fakesEnd)
      (valuesLenWord := valuesLenWord)
      (valuesEnd := valuesEnd) (sel := sel)
      (value := value) (secret := secret)
      (fakeWord := fakeWord) (word := word)
      (values := values) (fakes := fakes) (secrets := secrets)
      (a := a) (L := L) (evm := evm)
      hInvOrig
      rd1023 hbaseHash hbaseHashWord hlenLoad hboundBids hdataHash hvaluesEq
      hfp128 hfp96 hvalueBound hfakesBound hsecretsBound
      hvalueLoad hfakeSlt hfakeLoad hsecretLoad
      (by rfl) hfakeWordSmall hbidsL hvaluesL hfakesL hsecretsL hiL hlenL
      hrefundL hlenSrc hboundValues hboundFakes hboundSecrets
      hvalueLookup hfakeLookup hsecretLookup hperm
  · exact Or.inl <|
      scratch_revealLoopBody_bounds_fromLoopStart
        (I := I) (g := g) (s0 := s0)
        (k := k) (C := C)
        (loopLen := loopLen) (curLen := curLen)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLen := secretsLenWord)
        (secretsEnd := secretsEnd)
        (fakesLen := fakesLenWord)
        (fakesEnd := fakesEnd)
        (valuesLen := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
        (a := a) (L := L) (evm := evm)
        rd1023 hbaseHashWord hlenLoad (Nat.le_of_not_gt hboundBids)
        hbidsL hiL hlenSrc

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoop_fromLoopStart_or_revert {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate}
    {loopLen revealEnd biddingEnd secretsLenWord secretsEnd fakesLenWord fakesEnd
      valuesLenWord valuesEnd sel : UInt256}
    {values fakes secrets : List Value} {callargs : Store}
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hsecretsEnd : secretsEnd = ⟨4⟩ + revealSecretsOffsetWord I + ⟨32⟩)
    (hfakesEnd : fakesEnd = ⟨4⟩ + revealFakesOffsetWord I + ⟨32⟩)
    (hvaluesEnd : valuesEnd = ⟨4⟩ + revealValuesOffsetWord I + ⟨32⟩)
    (hvaluesEq : loopLen = valuesLenWord)
    (hfakesEq : loopLen = fakesLenWord)
    (hsecretsEq : loopLen = secretsLenWord)
    (hvaluesListLen : values.length = valuesLenWord.toNat)
    (hfakesListLen : fakes.length = fakesLenWord.toNat)
    (hsecretsListLen : secrets.length = secretsLenWord.toNat)
    (hvaluesLenMax : UInt256.gt valuesLenWord revealMaxU64 = ⟨0⟩) :
    RevealLoopRunFromStart I g s0 σ₀ gh bl A loopLen revealEnd biddingEnd secretsLenWord
      secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel values fakes secrets := by
  refine scratch_revealLoop_from_bodyOutcome_or_revert
    (I := I) (g := g) (s0 := s0)
    loopLen revealEnd biddingEnd secretsLenWord secretsEnd fakesLenWord fakesEnd
    valuesLenWord valuesEnd sel values fakes secrets σ₀ gh bl A ?_
  exact scratch_revealLoopBody_fromLoopStart
    (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
    (loopLen := loopLen) (revealEnd := revealEnd) (biddingEnd := biddingEnd)
    (secretsLenWord := secretsLenWord) (secretsEnd := secretsEnd)
    (fakesLenWord := fakesLenWord) (fakesEnd := fakesEnd)
    (valuesLenWord := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
    (values := values) (fakes := fakes) (secrets := secrets) (callargs := callargs)
    hsize hperm hdec hstore hsecretsEnd hfakesEnd hvaluesEnd hvaluesEq hfakesEq
    hsecretsEq hvaluesListLen hfakesListLen hsecretsListLen hvaluesLenMax

end BlindAuction
