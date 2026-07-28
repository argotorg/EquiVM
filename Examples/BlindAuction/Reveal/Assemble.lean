import Examples.BlindAuction.Reveal.Cases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

namespace BlindAuction

theorem scratch_revealLoopAdvance_secretStore_continue {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State} {fake : Bool}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyCont :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm a.idx value secret fake }
          evm))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩) a.refund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty a.acc k C)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
    ∃ a' L1 evm1 L2 evm2 k' C',
      (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L1 } evm1) ∨
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  rcases hInv with
    ⟨hiL, hlenL, hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      hvariant, hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  have hidxFit : a.idx.toNat + 1 < UInt256.size := by
    have hloopLt : loopLen.toNat < UInt256.size := loopLen.val.isLt
    omega
  let L1 : Store := scratch_revealSecretStoreOf L evm a.idx value secret fake
  let nextIdx : UInt256 := a.idx + ⟨1⟩
  let L2 : Store := L1.insert "i" (.int (Int.ofNat nextIdx.toNat))
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat a.idx.toNat)) := by
    simpa [L1] using scratch_revealSecretStoreOf_i_get L evm a.idx value secret fake hiL
  have hpost :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm) := by
    simpa [L2, nextIdx] using scratch_revealLoopPostStep evm L1 a.idx hiL1 hidxFit
  let nextCursor : RevealLoopCursor :=
    { idx := nextIdx,
      refund := a.refund,
      mem := memNext,
      aw := awNext,
      acc := a.acc,
      fp := newFree,
      haw := hawNext,
      hawSmall := hawNextSmall,
      hfpLoad := hfpNext,
      hfpRead := hreadNext,
      hmem96 := hmemNext96,
      hmemle := hmemNextLe,
      hgap := hgapNext,
      hfpIdx := by
        have hadd : nextIdx.toNat = a.idx.toNat + 1 := by
          simpa [nextIdx] using add1_toNat hidxFit
        rw [hnextFpNat, a.hfpIdx, hadd]
        omega }
  have hInvNext :
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v nextCursor L2 evm := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [L2, nextIdx, nextCursor, store_get_self]
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "length" =
        some (.int (Int.ofNat loopLen.toNat))
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_length_get L evm a.idx loopLen value secret fake hlenL
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "refund" =
        some (.int (Int.ofNat nextCursor.refund.toNat))
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_refund_get L evm a.idx a.refund value secret fake hrefundL
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "bids" = none
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_bids_get L evm a.idx value secret fake hbidsL
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "values" =
        some (.array values)
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_values_get L evm a.idx value secret fake values hvaluesL
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "fakes" =
        some (.array fakes)
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_fakes_get L evm a.idx value secret fake fakes hfakesL
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "secrets" =
        some (.array secrets)
      rw [store_get_ne]
      · exact scratch_revealSecretStoreOf_secrets_get L evm a.idx value secret fake secrets hsecretsL
      · decide
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · exact henv
    · exact hσ0
    · exact hgh
    · exact hbl
    · simpa [nextCursor] using hcreated
    · exact hsub
    · simpa [nextCursor] using haccounts
  exact ⟨nextCursor, L1, evm, L2, evm, k, C, Or.inr hbodyCont, hpost, hInvNext,
    by simpa [nextCursor, nextIdx] using rdNext⟩

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoopBody_fakeTrue_fromLoopStart {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord : UInt256}
    {word : Nat}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (rd1023 : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      a.mem a.aw ByteArray.empty a.acc k C)
    (hbaseHash :
      (ffi.KEC
        (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
          ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32) 32 32)
            |>.readWithPadding 0 64)) =
        UInt256.toByteArray (revealScratchBidsLengthSlot I))
    (hlenLoad :
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hboundBids : a.idx.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32) 32 32)
            0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
    (hfp128 : a.fp.toNat + 128 < UInt256.size)
    (hfp96 : 96 ≤ a.fp.toNat)
    (hvalueBound : a.idx.toNat < valuesLen.toNat)
    (hfakesBound : a.idx.toNat < fakesLen.toNat)
    (hsecretsBound : a.idx.toNat < secretsLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub (UInt256.mul ⟨32⟩ a.idx + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ a.idx + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + fakesEnd).toNat 32) =
        fakeWord)
    (hsecretLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + secretsEnd).toNat 32) =
        secret)
    (hfakeWordEq : fakeWord = UInt256.ofNat word)
    (hfakeWordSmall : (UInt256.ofNat word).toNat = word)
    (hfakeOne : fakeWord = ⟨1⟩)
    (hbidsL : L.get? "bids" = none)
    (hvaluesL : L.get? "values" = some (.array values))
    (hfakesL : L.get? "fakes" = some (.array fakes))
    (hsecretsL : L.get? "secrets" = some (.array secrets))
    (hiL : L.get? "i" = some (.int (Int.ofNat a.idx.toNat)))
    (hrefundL : L.get? "refund" = some (.int (Int.ofNat a.refund.toNat)))
    (hlenSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundValues : a.idx.toNat < values.length)
    (hboundFakes : a.idx.toNat < fakes.length)
    (hboundSecrets : a.idx.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values a.idx.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes a.idx.toNat = some (rawBoolWordValue word))
    (hsecretLookup :
      lookupNth? secrets a.idx.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hperm : I.perm = true) :
    (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0) ∨
    ∃ a' L1 evm1 L2 evm2 k' C',
      (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L1 } evm1) ∨
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  have hInvOrig := hInv
  rcases hInv with
    ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
      _hvariant, _hidxLe, henv, _hσ0, _hgh, _hbl, _hcreated, _hsub, haccounts⟩
  have hfakeNorm :
      normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool true) := by
    exact scratch_normalizeRawBoolWord_true_of_u256 hfakeWordSmall
      (by rw [← hfakeWordEq]; exact hfakeOne)
  let slot : UInt256 := bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat))
  let memSlot1 : ByteArray :=
    (UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32
  let memSlot2 : ByteArray :=
    (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 memSlot1 32 32
  let memSlot3 : ByteArray :=
    (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 memSlot2 0 32
  have hslotMemFacts :
      memSlot3.readWithPadding 64 32 = UInt256.toByteArray a.fp ∧
        memSlot3.size = a.mem.size := by
    simpa [memSlot1, memSlot2, memSlot3] using
      scratch_revealThreeScratchWrites_preserve_fp
        (mem := a.mem) (fp := a.fp) (key := revealScratchSenderWord I)
        (slot := (⟨4⟩ : UInt256)) (data := revealScratchBidsLengthSlot I)
        a.hfpRead a.hmem96
  have hfpSlot :
      (if (⟨64⟩ : UInt256).toNat ≥ memSlot3.size ∨
          (⟨64⟩ : UInt256) ≥ a.aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memSlot3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        a.fp := by
    rcases hslotMemFacts with ⟨hreadSlot, hsizeSlot⟩
    exact scratch_mload_of_read
      (mem := memSlot3) (fp := (⟨64⟩ : UInt256)) (packedLen := a.fp) (aw := a.aw)
      (by
        rw [hsizeSlot]
        change 64 < a.mem.size
        have hm : 96 ≤ a.mem.size := a.hmem96
        omega)
      (scratch_not_mload64_oob_of_aw_ge3_small a.haw a.hawSmall)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadSlot)
  obtain ⟨kSlot, CSlot, rd1069⟩ :=
    scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen_concrete
      (I := I) (g := g) (s0 := s0) (k := k) (C := C) (mem := a.mem) (aw := a.aw)
      (rdata := ByteArray.empty) (acc := a.acc)
      (i := a.idx) (refund := a.refund) (len := loopLen) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      rd1023 (scratch_reveal_aw_mstore0_of_ge3 a.haw)
      (scratch_reveal_aw_mstore32_of_ge3 a.haw)
      (scratch_reveal_aw_keccak64_of_ge3 a.haw)
      hbaseHash hlenLoad hboundBids hdataHash
  have hslotRead : memSlot3.readWithPadding 64 32 = UInt256.toByteArray a.fp :=
    hslotMemFacts.1
  have hslotSize : memSlot3.size = a.mem.size := hslotMemFacts.2
  have hslotMem96 : 96 ≤ memSlot3.size := by
    rw [hslotSize]
    exact a.hmem96
  have hslotMemle : memSlot3.size ≤ a.fp.toNat + 32 := by
    rw [hslotSize]
    exact a.hmemle
  have hslotGap : a.fp.toNat + 32 - memSlot3.size < USize.size := by
    rw [hslotSize]
    exact a.hgap
  let blinded : UInt256 :=
    (a.acc.2.find? I.codeOwner).option ⟨0⟩
      (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩)
  have hblindedEvm :
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded := rfl
  have hblindedSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm a.idx) = blinded := by
    have hfind :=
      accountMapEquiv_storage_findD haccounts I.codeOwner ((⟨0⟩ : UInt256) + slot) ⟨0⟩
    dsimp [blinded] at hfind ⊢
    rw [henv]
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      scratch_revealBidBlindedSlot, slot, u256_zero_add, henv] using hfind.symm
  let hashWord : UInt256 :=
    uInt256OfByteArray
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value true secret).toArray))
  obtain ⟨newFree, memPacked, awPacked, memNext, awNext,
        kPacked, CPacked, rd1207, hawNext, hawNextSmall,
        hfpNext, hreadNext, hmemNext96, hmemNextLe,
        hgapNext, hnextFpNat, hfpPacked, hlenPacked,
        hhashPacked, hnewFreeEq, hmemNextEq, hawNextEq⟩ :=
    scratch_revealLoopBody_toPacked_fromElemSlot_cursor
      (I := I) (g := g) (s0 := s0) (k := kSlot) (C := CSlot)
      (mem := memSlot3) (aw := a.aw) (rdata := ByteArray.empty)
      (cA := a.acc.1) (σ := a.acc.2)
      (slot := slot) (i := a.idx) (refund := a.refund) (len := loopLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd)
      (sel := sel) (value := value) (secret := secret)
      (fakeWord := fakeWord) (fp := a.fp) (fake := true)
      (by simpa [slot] using rd1069)
      a.haw a.hawSmall hfp128 hslotMemle hslotGap hslotRead hslotMem96 hfp96 hfpSlot
      hvalueBound hfakesBound hsecretsBound hvalueLoad hfakeSlt hfakeLoad
      (by simpa using hfakeOne) hsecretLoad
  by_cases hflag0 : UInt256.eq blinded hashWord = (⟨0⟩ : UInt256)
  · have hne :
        EVM.Word.toBytesBE blinded ≠
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value true secret).toArray)).toList := by
      exact scratch_revealPackedHash_ne_of_u256_eq_zero
        (blinded := blinded) (value := value) (secret := secret) (fake := true)
        (by simpa [hashWord] using hflag0)
    have hhashEval :=
      scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L a.idx value secret true
    have hbodyCont :
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue
            { contract := blindAuctionContract,
              locals := scratch_revealSecretStoreOf L evm a.idx value secret true }
            evm) := by
      exact scratch_revealLoopBody_continue_hash_mismatch_of_get evm L values fakes secrets
        curLen a.refund a.idx value secret blinded true (rawBoolWordValue word)
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value true secret).toArray)).toList
        hbidsL hvaluesL hfakesL hsecretsL hiL hlenSrc hboundBids hboundValues hboundFakes
        hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblindedSrc hhashEval hne
    obtain ⟨k1235, C1235, rd1235⟩ :=
      scratch_blindAuctionRevealX_loopBody_packed_suffix
        (I := I) (g := g) (s0 := s0) (k := kPacked) (C := CPacked)
        (mem := memPacked) (aw := awPacked) (rdata := ByteArray.empty)
        (cA := a.acc.1) (σ := a.acc.2)
        (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
        (i := a.idx) (refund := a.refund) (len := loopLen)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLen := secretsLen) (secretsEnd := secretsEnd)
        (fakesLen := fakesLen) (fakesEnd := fakesEnd)
        (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
        (fp := a.fp) (hash := hashWord) (blinded := blinded) (flag := ⟨0⟩)
        (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
        (by simpa [hashWord] using hhashPacked)
        hblindedEvm
        (by simpa [hashWord] using hflag0)
    obtain ⟨kNext, CNext, rdNext⟩ :=
      scratch_blindAuctionRevealX_hashGuard_mismatch_toNext
        (I := I) (g := g) (s0 := s0) (k := k1235) (C := C1235)
        (rdata := ByteArray.empty) (acc := a.acc)
        (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
        (i := a.idx) (refund := a.refund) (len := loopLen)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLen := secretsLen) (secretsEnd := secretsEnd)
        (fakesLen := fakesLen) (fakesEnd := fakesEnd)
        (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) rd1235
    exact Or.inr <|
      scratch_revealLoopAdvance_secretStore_continue
        (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
        (v := v) (k := kNext) (C := CNext) (loopLen := loopLen)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLen := secretsLen) (secretsEnd := secretsEnd)
        (fakesLen := fakesLen) (fakesEnd := fakesEnd)
        (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
        (value := value) (secret := secret) (newFree := newFree)
        (memNext := memNext) (awNext := awNext)
        (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
        (evm := evm) (fake := true) hInvOrig hbodyCont
        (by simpa [scratch_revealEvmLoopStack, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
        hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe hgapNext hnextFpNat
  · have hflag1 : UInt256.eq blinded hashWord = (⟨1⟩ : UInt256) := by
      by_cases heq : blinded = hashWord
      · simpa [heq] using u256_eq_refl hashWord
      · have hz : UInt256.eq blinded hashWord = (⟨0⟩ : UInt256) := u256_eq_of_ne heq
        exact False.elim (hflag0 hz)
    let deposit : UInt256 :=
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩)
    have hdepositEvm :
        (a.acc.2.find? I.codeOwner).option ⟨0⟩
          (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit := rfl
    have hdepositSrc :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (scratch_revealBidDepositSlot evm a.idx) = deposit := by
      have hfind := accountMapEquiv_storage_findD haccounts I.codeOwner (slot + ⟨1⟩) ⟨0⟩
      have hdep' :
          Option.option (⟨0⟩ : UInt256)
              (fun ac => ac.storage.findD
                (bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)) + ⟨1⟩)
                ⟨0⟩)
              (a.acc.2.find? I.codeOwner) = deposit := by
        simpa [deposit, slot] using hdepositEvm
      rw [henv]
      simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        scratch_revealBidDepositSlot, scratch_revealBidBlindedSlot, slot, henv] at hfind ⊢
      rw [← hfind]
      exact hdep'
    by_cases hfit : a.refund.toNat + deposit.toNat < UInt256.size
    · obtain ⟨hbodyOk, hrdNext⟩ :=
        scratch_revealLoopBody_hashMatch_noPlace_fromPacked_pair
          (I := I) (g := g) (s0 := s0) (k := kPacked) (C := CPacked)
          (mem := memPacked) (aw := awPacked) (rdata := ByteArray.empty)
          (cA := a.acc.1) (σ := a.acc.2)
          (L := L) (evm := evm) (values := values) (fakes := fakes)
          (secrets := secrets) (slot := slot) (i := a.idx)
          (refund := a.refund) (len := loopLen) (curLen := curLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
          (value := value) (secret := secret) (fakeWord := fakeWord)
          (blinded := blinded) (deposit := deposit) (fp := a.fp)
          (fake := true) (fakeRaw := rawBoolWordValue word)
          (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
          (by simpa [hashWord] using hhashPacked)
          hblindedEvm (by simpa [hashWord] using hflag1)
          hdepositEvm hperm hbidsL hvaluesL hfakesL hsecretsL hiL hrefundL hlenSrc
          hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
          hsecretLookup hblindedSrc hdepositSrc (by simpa using hfakeOne) hfit (Or.inl rfl)
      obtain ⟨kNext, CNext, rdNext⟩ := hrdNext
      exact Or.inr <|
        scratch_revealLoopAdvance_refundAdded_zeroBlinded
          (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
          (v := v) (k := kNext) (C := CNext) (loopLen := loopLen) (slot := slot)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
          (value := value) (secret := secret) (deposit := deposit) (newFree := newFree)
          (memNext := memNext) (awNext := awNext)
          (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
          (evm := evm) (fake := true) hInvOrig hbodyOk
          (by simpa [deposit, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
          (by rfl) hfit hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe
          hgapNext hnextFpNat
    · have hover : UInt256.size ≤ a.refund.toNat + deposit.toNat := Nat.le_of_not_gt hfit
      have heq :
          EVM.Word.toBytesBE blinded =
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value true secret).toArray)).toList := by
        exact scratch_revealPackedHash_eq_of_u256_eq_one
          (blinded := blinded) (value := value) (secret := secret)
          (fake := true) (by simpa [hashWord] using hflag1)
      have hhashEval :=
        scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L a.idx value secret true
      obtain ⟨k1235, C1235, rd1235⟩ :=
        scratch_blindAuctionRevealX_loopBody_packed_suffix
          (I := I) (g := g) (s0 := s0) (k := kPacked) (C := CPacked)
          (mem := memPacked) (aw := awPacked) (rdata := ByteArray.empty)
          (cA := a.acc.1) (σ := a.acc.2)
          (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
          (i := a.idx) (refund := a.refund) (len := loopLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
          (fp := a.fp) (hash := hashWord) (blinded := blinded) (flag := ⟨1⟩)
          (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
          (by simpa [hashWord] using hhashPacked)
          hblindedEvm
          (by simpa [hashWord] using hflag1)
      obtain ⟨k1247, C1247, rd1247⟩ :=
        scratch_blindAuctionRevealX_hashGuard_match_to1247
          (I := I) (g := g) (s0 := s0) (k := k1235) (C := C1235)
          (rdata := ByteArray.empty) (acc := a.acc)
          (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
          (i := a.idx) (refund := a.refund) (len := loopLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) rd1235
      exact Or.inl <|
        scratch_revealLoopBody_refundOverflow_from1247_pair
          (I := I) (g := g) (s0 := s0) (k := k1247) (C := C1247)
          (mem := memNext) (aw := awNext) (rdata := ByteArray.empty)
          (cA := a.acc.1) (σ := a.acc.2)
          (L := L) (evm := evm)
          (values := values) (fakes := fakes) (secrets := secrets)
          (slot := slot) (i := a.idx) (refund := a.refund) (len := loopLen)
          (curLen := curLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
          (value := value) (secret := secret) (fakeWord := fakeWord)
          (blinded := blinded) (deposit := deposit)
          (fake := true) (fakeRaw := rawBoolWordValue word)
          (by simpa [hnewFreeEq, hmemNextEq, hawNextEq] using rd1247)
          hawNext hdepositEvm hbidsL hvaluesL hfakesL hsecretsL hiL hrefundL
          hlenSrc hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup
          hfakeLookup hfakeNorm hsecretLookup hblindedSrc hdepositSrc hhashEval heq hover

theorem scratch_revealLoopBody_fakeInvalid_fromLoopStart {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {loopLen curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value fakeWord : UInt256}
    {fakeRaw : Value}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (rd1023 : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      a.mem a.aw ByteArray.empty a.acc k C)
    (hbaseHashWord :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hboundBids : a.idx.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32) 32 32)
            0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
    (hvalueBound : a.idx.toNat < valuesLen.toNat)
    (hfakesBound : a.idx.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub (UInt256.mul ⟨32⟩ a.idx + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ a.idx + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + fakesEnd).toNat 32) =
        fakeWord)
    (hfakeZero : fakeWord ≠ ⟨0⟩)
    (hfakeOne : fakeWord ≠ ⟨1⟩)
    (hbidsL : L.get? "bids" = none)
    (hvaluesL : L.get? "values" = some (.array values))
    (hfakesL : L.get? "fakes" = some (.array fakes))
    (hiL : L.get? "i" = some (.int (Int.ofNat a.idx.toNat)))
    (hlenSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundValues : a.idx.toNat < values.length)
    (hboundFakes : a.idx.toNat < fakes.length)
    (hvalueLookup :
      lookupNth? values a.idx.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes a.idx.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .revert) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  exact
    scratch_revealLoopBody_fakeInvalid_pair
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := a.mem) (aw := a.aw) (rdata := ByteArray.empty)
      (cA := a.acc.1) (σ := a.acc.2) (L := L) (evm := evm)
      (values := values) (fakes := fakes) (secrets := secrets)
      (i := a.idx) (refund := a.refund) (len := loopLen) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      (value := value) (fakeWord := fakeWord) (fakeRaw := fakeRaw)
      rd1023 a.haw hbaseHashWord hlenLoad hboundBids hdataHash hvalueBound
      hfakesBound hvalueLoad hfakeSlt hfakeLoad hfakeZero hfakeOne hbidsL hvaluesL
      hfakesL hiL hlenSrc hboundValues hboundFakes hvalueLookup hfakeLookup hfakeNorm

theorem scratch_revealLoopBody_bounds_fromLoopStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ}
    {loopLen curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    {a : RevealLoopCursor} {L : Store} {evm : EVM.State}
    (rd1023 : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      a.mem a.aw ByteArray.empty a.acc k C)
    (hbaseHashWord :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (a.acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hboundBids : curLen.toNat ≤ a.idx.toNat)
    (hbidsL : L.get? "bids" = none)
    (hiL : L.get? "i" = some (.int (Int.ofNat a.idx.toNat)))
    (hlenSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  exact
    scratch_revealLoopBody_bounds_pair
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := a.mem) (aw := a.aw) (rdata := ByteArray.empty)
      (cA := a.acc.1) (σ := a.acc.2) (L := L) (evm := evm)
      (i := a.idx) (refund := a.refund) (len := loopLen) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      rd1023 a.haw hbaseHashWord hlenLoad hboundBids hbidsL hiL hlenSrc

theorem scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidNonzero_pendingHash
    {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen slot revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret deposit high old pending newFree : UInt256}
    {oldAddr : AccountAddress} {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm a.idx a.refund value secret deposit }
          (scratch_revealZeroBlindedState
            (scratch_placeBidAfterBidder
              (scratch_placeBidAfterHigh
                (scratch_placeBidAfterPending evm oldAddr
                  (UInt256.ofNat (pending.toNat + high.toNat))) value)
              evm.executionEnv.source) a.idx)))
    (rdNext :
      let key := UInt256.land (scratch_placeBidHighestBidderWord a.acc.2 I) solcAddrMask
      let awPB1 := UInt256.ofNat (MachineState.M awNext.toNat (⟨0⟩ : UInt256).toNat 32)
      let awPB2 := UInt256.ofNat (MachineState.M awPB1.toNat (⟨32⟩ : UInt256).toNat 32)
      let awPB3 := UInt256.ofNat (MachineState.M awPB2.toNat (⟨0⟩ : UInt256).toNat 64)
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (a.idx + ⟨1⟩)
          (UInt256.sub (deposit + a.refund) value) loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (scratch_placeBidPendingHashMem memNext key) awPB3 ByteArray.empty
        (a.acc.1, sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap a.acc.2 I
                (scratch_placeBidHighestBidWord a.acc.2 I +
                  scratch_placeBidPendingWord a.acc.2 I)) I value)
            I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k C)
    (hslot : slot = bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)))
    (hhighWord : scratch_placeBidHighestBidWord a.acc.2 I = high)
    (holdWord : scratch_placeBidHighestBidderWord a.acc.2 I = old)
    (hpendingWord : scratch_placeBidPendingWord a.acc.2 I = pending)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hsum : pending.toNat + high.toNat < UInt256.size)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
    ∃ a' L1 evm1 L2 evm2 k' C',
      (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L1 } evm1) ∨
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  let key : UInt256 := UInt256.land (scratch_placeBidHighestBidderWord a.acc.2 I) solcAddrMask
  let awPB1 : UInt256 :=
    UInt256.ofNat (MachineState.M awNext.toNat (⟨0⟩ : UInt256).toNat 32)
  let awPB2 : UInt256 :=
    UInt256.ofNat (MachineState.M awPB1.toNat (⟨32⟩ : UInt256).toNat 32)
  let awPB3 : UInt256 :=
    UInt256.ofNat (MachineState.M awPB2.toNat (⟨0⟩ : UInt256).toNat 64)
  have hawPB1Eq : awPB1 = awNext := by
    simpa [awPB1] using scratch_reveal_aw_mstore0_of_ge3 hawNext
  have hawPB2Eq : awPB2 = awNext := by
    simpa [awPB2, hawPB1Eq] using scratch_reveal_aw_mstore32_of_ge3 hawNext
  have hawPB3Eq : awPB3 = awNext := by
    simpa [awPB3, hawPB2Eq] using scratch_reveal_aw_keccak64_of_ge3 hawNext
  have hawPB3 : 3 ≤ awPB3.toNat := by
    simpa [hawPB3Eq] using hawNext
  have hawPB3Small : awPB3.toNat * 32 < UInt256.size := by
    simpa [hawPB3Eq] using hawNextSmall
  have hpendingMemFacts :=
    scratch_placeBidPendingHashMem_preserve_fp
      (mem := memNext) (fp := newFree) (key := key) hreadNext hmemNext96
  have hreadPB :
      (scratch_placeBidPendingHashMem memNext key).readWithPadding 64 32 =
        UInt256.toByteArray newFree :=
    hpendingMemFacts.1
  have hsizePB :
      (scratch_placeBidPendingHashMem memNext key).size = memNext.size :=
    hpendingMemFacts.2
  have hmemPB96 : 96 ≤ (scratch_placeBidPendingHashMem memNext key).size := by
    rw [hsizePB]
    exact hmemNext96
  have hmemPBLe :
      (scratch_placeBidPendingHashMem memNext key).size ≤ newFree.toNat + 32 := by
    rw [hsizePB]
    exact hmemNextLe
  have hgapPB :
      newFree.toNat + 32 - (scratch_placeBidPendingHashMem memNext key).size < USize.size := by
    rw [hsizePB]
    exact hgapNext
  have hfpPB :
      (if (⟨64⟩ : UInt256).toNat ≥ (scratch_placeBidPendingHashMem memNext key).size ∨
            (⟨64⟩ : UInt256) ≥ awPB3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((scratch_placeBidPendingHashMem memNext key).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        newFree := by
    exact scratch_mload_of_read
      (mem := scratch_placeBidPendingHashMem memNext key)
      (fp := (⟨64⟩ : UInt256)) (packedLen := newFree) (aw := awPB3)
      (by
        change 64 < (scratch_placeBidPendingHashMem memNext key).size
        have hm := hmemPB96
        omega)
      (scratch_not_mload64_oob_of_aw_ge3_small hawPB3 hawPB3Small)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadPB)
  exact
    scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidNonzero
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C) (loopLen := loopLen) (slot := slot)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      (value := value) (secret := secret) (deposit := deposit) (high := high)
      (old := old) (pending := pending) (newFree := newFree) (oldAddr := oldAddr)
      (memNext := scratch_placeBidPendingHashMem memNext key) (awNext := awPB3)
      (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
      (evm := evm) hInv hbodyOk (by simpa [key, awPB1, awPB2, awPB3] using rdNext)
      hslot hhighWord holdWord hpendingWord holdAddr hfit hdepositGe hsum hawPB3
      hawPB3Small hfpPB hreadPB hmemPB96 hmemPBLe hgapPB hnextFpNat

theorem scratch_blindAuctionPlaceBidBodyReverts_true_nonzero_pendingOverflow
    (evm : EVM.State) (bidder oldAddr : AccountAddress)
    (value high old pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hover : UInt256.size ≤ pending.toNat + high.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold placeBidFn
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
    [ .ite (.binary .le (.var "value") (.storage highestBidRef))
        [ .return [(.boolLit false)] ] [],
      .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
        [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
            (u256 (.binary .add
              (.storage (pendingReturnsRef (.storage highestBidderRef)))
              (.storage highestBidRef))) ] [],
      .assign .storage highestBidRef (.var "value"),
      .assign .storage highestBidderRef (.var "bidder"),
      .return [(.boolLit true)] ]
    .reverted
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_value_le_highestBid_false evm bidder value high hhigh hlt)
      ExecBlock.nil
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (scratch_eval_placeBid_highestBidder_ne_zero_true evm bidder value old hold hnonzero) ?_
  exact ExecBlock.consRevert <|
    ExecStmt.assignExprRevert
      (scratch_eval_placeBid_pending_add_revert evm bidder oldAddr value old high pending
        hhigh hold holdAddr hpending hover)

theorem scratch_revealLoopBody_revert_placeBid_pendingOverflow_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value)
    (len refund i value secret blinded deposit : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceBody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm
        (scratch_placeBidStore evm.executionEnv.source value) placeBidFn.body .reverted) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts .reverted := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret false
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false
  let refundAdded : UInt256 := UInt256.ofNat (refund.toNat + deposit.toNat)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret false hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok") .reverted := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    exact
      ExecStmt.internalCallRevert
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using hplaceBody)
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        .reverted :=
    ExecBlock.consRevert hcall
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        .reverted :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts) .reverted := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    exact ExecBlock.consRevert hplaceIte
  exact
    scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_nonzero_overflow_anyMem {g : Sat256} {s0 : State}
    {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hnonzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (scratch_placeBidPendingWord σ I).toNat +
          (scratch_placeBidHighestBidWord σ I).toNat)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 16 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  let key := UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
  let memKey := scratch_placeBidPendingKeyMem mem key
  let memHash := scratch_placeBidPendingHashMem mem key
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
  have haw1 : 3 ≤ aw1.toNat := by
    simpa [aw1] using
      scratch_reveal_aw_M_ge3 (aw := aw) (off := (⟨0⟩ : UInt256))
        (len := (⟨32⟩ : UInt256)) haw
  have haw2 : 3 ≤ aw2.toNat := by
    simpa [aw2] using
      scratch_reveal_aw_M_ge3 (aw := aw1) (off := (⟨32⟩ : UInt256))
        (len := (⟨32⟩ : UInt256)) haw1
  have haw3 : 3 ≤ aw3.toNat := by
    simpa [aw3] using
      scratch_reveal_aw_M_ge3 (aw := aw2) (off := (⟨0⟩ : UInt256))
        (len := (⟨64⟩ : UInt256)) haw2
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hmaskNonzero :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hnonzero
  have rd1564 := rd1564₀
  have rd1565₀ := evm_run rd1564 with [iszero]
  have rd1565 := rd1565₀
  rw [isZero_eq_zero_of_ne hmaskNonzero] at rd1565
  have rd1571 := evm_run rd1565 with [push2 ⟨1618⟩, jumpiNT (by decide), push1 ⟨6⟩]
  obtain ⟨_, _, rd1572₀⟩ := rd1571.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1572⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1572⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1572₀⟩
  have rd1574 := evm_run rd1572 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd1575₀⟩ := rd1574.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1575⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1575⟩
      (scratch_placeBidHighestBidderWord σ I :: scratch_placeBidHighestBidWord σ I ::
        ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1575₀⟩
  have rd1587₀ := evm_run rd1575 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have hmask :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) =
        UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) =
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
    exact Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
  have rd1587 := rd1587₀
  rw [hmask] at rd1587
  have rd1588 := evm_run rd1587 with [
    raw mstore (Cₘ aw1 - Cₘ aw) memKey aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      (by simp [memKey, scratch_placeBidPendingKeyMem, key])
      (by rfl) (by evm_ov)]
  have rd1593 := evm_run rd1588 with [
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) memHash aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw2])
      (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        simp [memHash, scratch_placeBidPendingHashMem, memKey])
      (by rfl) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have hkeyCanon := solcAddrMask_result_canonical
    (scratch_placeBidHighestBidderWord σ I)
  have hslot := scratch_placeBidPendingKeccak_any mem key hkeyCanon
  have rd1597 := evm_run rd1593 with [
    raw keccak256 (Cₘ aw3 - Cₘ aw2) (scratch_placeBidPendingSlot σ I) aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw3,
          show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
      (by simpa [memHash, key, scratch_placeBidPendingSlot] using hslot) (by rfl) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1598₀⟩ := rd1597.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1599⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1599⟩
      (scratch_placeBidPendingWord σ I :: scratch_placeBidPendingSlot σ I ::
        ⟨0⟩ :: scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      memHash aw3 rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidPendingWord, scratch_placeBidPendingSlot,
      memHash] using rd1598₀⟩
  have rd1611 := evm_run rd1599 with [
    swap1, swap2, swap1, push2 ⟨1612⟩, swap1, dup5, swap1, push2 ⟨2045⟩,
    jump (by jump_dest)]
  exact scratch_blindAuctionCheckedAddOverflowRevert rd1611 hover haw3 (by evm_ov)

theorem scratch_blindAuctionRevealX_placeCond_placeBid_true_nonzero_overflow_revert {I}
    {g : Sat256} {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceTrue : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderNonzero :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (scratch_placeBidPendingWord σ I).toNat +
          (scratch_placeBidHighestBidWord σ I).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  exact
    scratch_RD_placeBid_true_nonzero_overflow_anyMem
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hplaceTrue hhighestBidderNonzero hover haw (by simp)

end BlindAuction
