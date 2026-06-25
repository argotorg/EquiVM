import Examples.BlindAuction.Reveal.Assemble

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

namespace BlindAuction

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoopBody_fakeFalse_fromLoopStart {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen curLen revealEnd biddingEnd secretsLenWord secretsEnd fakesLenWord fakesEnd
      valuesLenWord valuesEnd sel value secret fakeWord : UInt256}
    {word : Nat}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (rd1023 : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
        secretsLenWord secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel)
      a.mem a.aw ByteArray.empty a.acc k C)
    (hbaseHash :
      ffi.KEC
        (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
          ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 a.mem 0 32) 32 32)
          |>.readWithPadding 0 64) =
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
    (hvaluesEq : loopLen = valuesLenWord)
    (hfp128 : a.fp.toNat + 128 < UInt256.size)
    (hfp96 : 96 ≤ a.fp.toNat)
    (hvalueBound : a.idx.toNat < valuesLenWord.toNat)
    (hfakesBound : a.idx.toNat < fakesLenWord.toNat)
    (hsecretsBound : a.idx.toNat < secretsLenWord.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + valuesEnd).toNat 32) = value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ a.idx + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ a.idx + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + fakesEnd).toNat 32) = fakeWord)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ a.idx + secretsEnd).toNat 32) = secret)
    (hfakeWordEq : fakeWord = UInt256.ofNat word)
    (hfakeWordSmall : (UInt256.ofNat word).toNat = word)
    (hfakeZero : fakeWord = ⟨0⟩)
    (hbidsL : L.get? "bids" = none)
    (hvaluesL : L.get? "values" = some (.array values))
    (hfakesL : L.get? "fakes" = some (.array fakes))
    (hsecretsL : L.get? "secrets" = some (.array secrets))
    (hiL : L.get? "i" = some (.int (Int.ofNat a.idx.toNat)))
    (hlenL : L.get? "length" = some (.int (Int.ofNat loopLen.toNat)))
    (hrefundL : L.get? "refund" = some (.int (Int.ofNat a.refund.toNat)))
    (hlenSrc :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundValues : a.idx.toNat < values.length)
    (hboundFakes : a.idx.toNat < fakes.length)
    (hboundSecrets : a.idx.toNat < secrets.length)
    (hvalueLookup : lookupNth? values a.idx.toNat = some (.int (Int.ofNat value.toNat)))
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
          secretsLenWord secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  let idx : RevealLoopCursor → UInt256 := fun a => a.idx
  let refundOf : RevealLoopCursor → UInt256 := fun a => a.refund
  let memOf : RevealLoopCursor → ByteArray := fun a => a.mem
  let awOf : RevealLoopCursor → UInt256 := fun a => a.aw
  let accOf : RevealLoopCursor → Batteries.RBSet AccountAddress compare × AccountMap := fun a => a.acc
  let Inv : ℕ → RevealLoopCursor → Store → EVM.State → Prop :=
    RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A
  have hInvOrig := hInv
  rcases hInv with
    ⟨hiL, hlenL, hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      hvariant, hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  · have hfakeNorm :
        normalizeRawBoolWord? (rawBoolWordValue word) =
          .ok (.bool false) := by
      exact scratch_normalizeRawBoolWord_false_of_u256
        hfakeWordSmall (by rw [← hfakeWordEq]; exact hfakeZero)
    let slot : UInt256 :=
      bidsElemSlot (.address I.source)
        (.int (Int.ofNat (idx a).toNat))
    let memSlot1 : ByteArray :=
      (UInt256.toByteArray (revealScratchSenderWord I)).write 0
        (memOf a) 0 32
    let memSlot2 : ByteArray :=
      (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 memSlot1 32 32
    let memSlot3 : ByteArray :=
      (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
        memSlot2 0 32
    have hslotMemFacts :
        memSlot3.readWithPadding 64 32 =
            UInt256.toByteArray a.fp ∧
          memSlot3.size = (memOf a).size := by
      simpa [memSlot1, memSlot2, memSlot3, memOf] using
        scratch_revealThreeScratchWrites_preserve_fp
          (mem := memOf a) (fp := a.fp)
          (key := revealScratchSenderWord I)
          (slot := (⟨4⟩ : UInt256))
          (data := revealScratchBidsLengthSlot I)
          a.hfpRead a.hmem96
    have hfpSlot :
        (if (⟨64⟩ : UInt256).toNat ≥ memSlot3.size ∨
            (⟨64⟩ : UInt256) ≥ (awOf a) * ⟨32⟩
         then ⟨0⟩
         else UInt256.ofNat
          (fromByteArrayBigEndian
            (memSlot3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
          a.fp := by
      rcases hslotMemFacts with ⟨hreadSlot, hsizeSlot⟩
      exact scratch_mload_of_read
        (mem := memSlot3) (fp := (⟨64⟩ : UInt256))
        (packedLen := a.fp) (aw := awOf a)
        (by
          rw [hsizeSlot]
          change 64 < (memOf a).size
          have hm : 96 ≤ (memOf a).size := by
            simpa [memOf] using a.hmem96
          omega)
        (by
          simpa [awOf] using
            scratch_not_mload64_oob_of_aw_ge3_small
              a.haw a.hawSmall)
        (by
          simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide]
            using hreadSlot)
    obtain ⟨kSlot, CSlot, rd1069⟩ :=
      scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen_concrete
        (I := I) (g := g)
        (s0 := s0)
        (k := k) (C := C) (mem := memOf a) (aw := awOf a)
        (rdata := ByteArray.empty) (acc := accOf a)
        (i := idx a) (refund := refundOf a) (len := loopLen)
        (curLen := curLen)
        (revealEnd := revealEnd)
        (biddingEnd := biddingEnd)
        (secretsLen := secretsLenWord)
        (secretsEnd := secretsEnd)
        (fakesLen := fakesLenWord)
        (fakesEnd := fakesEnd)
        (valuesLen := valuesLenWord)
        (valuesEnd := valuesEnd)
        (sel := sel)
        rd1023
        (scratch_reveal_aw_mstore0_of_ge3 a.haw)
        (scratch_reveal_aw_mstore32_of_ge3 a.haw)
        (scratch_reveal_aw_keccak64_of_ge3 a.haw)
        hbaseHash hlenLoad hboundBids hdataHash
    have hslotRead :
        memSlot3.readWithPadding 64 32 =
          UInt256.toByteArray a.fp := hslotMemFacts.1
    have hslotSize : memSlot3.size = (memOf a).size := hslotMemFacts.2
    have hslotMem96 : 96 ≤ memSlot3.size := by
      rw [hslotSize]
      simpa [memOf] using a.hmem96
    have hslotMemle : memSlot3.size ≤ a.fp.toNat + 32 := by
      rw [hslotSize]
      simpa [memOf] using a.hmemle
    have hslotGap :
        a.fp.toNat + 32 - memSlot3.size < USize.size := by
      rw [hslotSize]
      simpa [memOf] using a.hgap
    let blinded : UInt256 :=
      ((accOf a).2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩)
    have hblindedEvm :
        ((accOf a).2.find? I.codeOwner).option ⟨0⟩
          (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded := rfl
    have hblindedSrc :
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (scratch_revealBidBlindedSlot evm (idx a)) = blinded := by
      have hfind :=
        accountMapEquiv_storage_findD haccounts I.codeOwner
          ((⟨0⟩ : UInt256) + slot) ⟨0⟩
      dsimp [blinded] at hfind ⊢
      rw [henv]
      simpa [Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, scratch_revealBidBlindedSlot, slot,
        u256_zero_add, henv] using hfind.symm
    let hashWord : UInt256 :=
      uInt256OfByteArray
        (ffi.KEC
          (ByteArray.mk
            (scratch_revealPackedBytes value false secret).toArray))
    by_cases hflag0 : UInt256.eq blinded hashWord = ⟨0⟩
    · obtain ⟨hbodyMismatch, nextFp, memNext, awNext, kNext, CNext,
        rdNext, hawNext, hawNextSmall, hfpNext, hreadNext,
        hmemNext96, hmemNextLe, hgapNext, hnextFpNat⟩ :=
        scratch_revealLoopBody_hashMismatch_fromElemSlot_cursor_pair
          (I := I) (g := g)
          (s0 := s0)
          (k := kSlot) (C := CSlot)
          (mem := memSlot3) (aw := awOf a)
          (rdata := ByteArray.empty)
          (cA := (accOf a).1) (σ := (accOf a).2)
          (L := L) (evm := evm)
          (values := values) (fakes := fakes)
          (secrets := secrets) (slot := slot) (i := idx a)
          (refund := refundOf a) (len := loopLen) (curLen := curLen)
          (revealEnd := revealEnd)
          (biddingEnd := biddingEnd)
          (secretsLen := secretsLenWord)
          (secretsEnd := secretsEnd)
          (fakesLen := fakesLenWord)
          (fakesEnd := fakesEnd)
          (valuesLen := valuesLenWord)
          (valuesEnd := valuesEnd)
          (sel := sel) (value := value)
          (secret := secret) (fakeWord := fakeWord)
          (blinded := blinded) (fp := a.fp)
          (fakeRaw := rawBoolWordValue word)
          (by simpa [slot] using rd1069)
          a.haw a.hawSmall hfp128 hslotMemle hslotGap hslotRead
          hslotMem96 hfp96 hfpSlot hvalueBound hfakesBound
          hsecretsBound (by simpa using hvalueLoad) hfakeSlt
          (by simpa using hfakeLoad) hfakeZero
          (by simpa using hsecretLoad) hblindedEvm
          (by simpa [hashWord] using hflag0)
          hbidsL hvaluesL hfakesL hsecretsL hiL hlenSrc
          hboundBids hboundValues hboundFakes hboundSecrets
          hvalueLookup hfakeLookup hfakeNorm hsecretLookup
          hblindedSrc
      exact Or.inr <|
        scratch_revealLoopAdvance_secretStore_continue
          (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
          (v := v) (k := kNext) (C := CNext) (loopLen := loopLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLenWord) (secretsEnd := secretsEnd)
          (fakesLen := fakesLenWord) (fakesEnd := fakesEnd)
          (valuesLen := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
          (value := value) (secret := secret) (newFree := nextFp)
          (memNext := memNext) (awNext := awNext)
          (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
          (evm := evm) (fake := false) hInvOrig hbodyMismatch
          (by simpa [idx, refundOf, memOf, awOf, accOf] using rdNext)
          hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe hgapNext hnextFpNat
    · have hflag1 :
          UInt256.eq blinded hashWord = (⟨1⟩ : UInt256) := by
        by_cases heq : blinded = hashWord
        · simpa [heq] using u256_eq_refl hashWord
        · have hz :
            UInt256.eq blinded hashWord = (⟨0⟩ : UInt256) :=
            u256_eq_of_ne heq
          exact False.elim (hflag0 hz)
      obtain ⟨newFree, memPacked, awPacked, memNext, awNext,
          kPacked, CPacked, rd1207, hawNext, hawNextSmall,
          hfpNext, hreadNext, hmemNext96, hmemNextLe,
            hgapNext, hnextFpNat, hfpPacked, hlenPacked,
            hhashPacked, hnewFreeEq, hmemNextEq, hawNextEq⟩ :=
        scratch_revealLoopBody_toPacked_fromElemSlot_cursor
          (I := I) (g := g)
          (s0 := s0)
          (k := kSlot) (C := CSlot)
          (mem := memSlot3) (aw := awOf a)
          (rdata := ByteArray.empty)
          (cA := (accOf a).1) (σ := (accOf a).2)
          (slot := slot) (i := idx a) (refund := refundOf a)
          (len := loopLen)
          (revealEnd := revealEnd)
          (biddingEnd := biddingEnd)
          (secretsLen := secretsLenWord)
          (secretsEnd := secretsEnd)
          (fakesLen := fakesLenWord)
          (fakesEnd := fakesEnd)
          (valuesLen := valuesLenWord)
          (valuesEnd := valuesEnd)
          (sel := sel) (value := value)
          (secret := secret) (fakeWord := fakeWord) (fp := a.fp)
          (fake := false) (by simpa [slot] using rd1069)
          a.haw a.hawSmall hfp128 hslotMemle hslotGap hslotRead
          hslotMem96 hfp96 hfpSlot hvalueBound hfakesBound
          hsecretsBound (by simpa using hvalueLoad) hfakeSlt
          (by simpa using hfakeLoad)
          (by simpa using hfakeZero)
          (by simpa using hsecretLoad)
      let deposit : UInt256 :=
        ((accOf a).2.find? I.codeOwner).option ⟨0⟩
          (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩)
      have hdepositEvm :
          ((accOf a).2.find? I.codeOwner).option ⟨0⟩
            (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) =
            deposit := rfl
      have hdepositSrc :
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (scratch_revealBidDepositSlot evm (idx a)) = deposit := by
        have hfind :=
          accountMapEquiv_storage_findD haccounts I.codeOwner
            (slot + ⟨1⟩) ⟨0⟩
        have hdep' :
            Option.option (⟨0⟩ : UInt256)
                (fun ac => ac.storage.findD
                  (bidsElemSlot (.address I.source)
                    (.int (Int.ofNat (idx a).toNat)) + ⟨1⟩)
                  ⟨0⟩)
                ((accOf a).2.find? I.codeOwner) = deposit := by
          simpa [deposit, slot] using hdepositEvm
        rw [henv]
        simp [Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, scratch_revealBidDepositSlot,
          scratch_revealBidBlindedSlot, slot, henv] at hfind ⊢
        rw [← hfind]
        exact hdep'
      by_cases hfit :
          (refundOf a).toNat + deposit.toNat < UInt256.size
      · by_cases hdepositLt : deposit.toNat < value.toNat
        · obtain ⟨hbodyOk, hrdNext⟩ :=
            scratch_revealLoopBody_hashMatch_noPlace_fromPacked_pair
              (I := I) (g := g)
              (s0 := s0)
              (k := kPacked) (C := CPacked)
              (mem := memPacked) (aw := awPacked)
              (rdata := ByteArray.empty)
              (cA := (accOf a).1) (σ := (accOf a).2)
              (L := L) (evm := evm)
              (values := values) (fakes := fakes)
              (secrets := secrets) (slot := slot) (i := idx a)
              (refund := refundOf a) (len := loopLen) (curLen := curLen)
              (revealEnd := revealEnd)
              (biddingEnd := biddingEnd)
              (secretsLen := secretsLenWord)
              (secretsEnd := secretsEnd)
              (fakesLen := fakesLenWord)
              (fakesEnd := fakesEnd)
              (valuesLen := valuesLenWord)
              (valuesEnd := valuesEnd)
              (sel := sel) (value := value)
              (secret := secret) (fakeWord := fakeWord)
              (blinded := blinded) (deposit := deposit)
              (fp := a.fp) (fake := false)
              (fakeRaw := rawBoolWordValue word)
              (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
              (by simpa [hashWord] using hhashPacked)
              hblindedEvm
              (by simpa [hashWord] using hflag1)
              hdepositEvm hperm hbidsL hvaluesL hfakesL
              hsecretsL hiL hrefundL hlenSrc hboundBids
              hboundValues hboundFakes hboundSecrets hvalueLookup
              hfakeLookup hfakeNorm hsecretLookup hblindedSrc
              hdepositSrc (by simpa using hfakeZero) hfit
              (Or.inr hdepositLt)
          obtain ⟨kNext, CNext, rdNext⟩ := hrdNext
          exact Or.inr <| by
            simpa [Inv, idx, refundOf, memOf, awOf, accOf] using
              scratch_revealLoopAdvance_refundAdded_zeroBlinded
                (I := I) (g := g)
                (s0 := s0)
                (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
                (v := v) (k := kNext) (C := CNext)
                (loopLen := loopLen) (slot := slot)
                (revealEnd := revealEnd)
                (biddingEnd := biddingEnd)
                (secretsLen := secretsLenWord)
                (secretsEnd :=
                  secretsEnd)
                (fakesLen := fakesLenWord)
                (fakesEnd :=
                  fakesEnd)
                (valuesLen := valuesLenWord)
                (valuesEnd :=
                  valuesEnd)
                (sel := sel)
                (value := value) (secret := secret)
                (deposit := deposit) (newFree := newFree)
                (memNext := memNext) (awNext := awNext)
                (values := values) (fakes := fakes)
                (secrets := secrets) (a := a) (L := L)
                (evm := evm) (fake := false)
                hInvOrig hbodyOk
                (by simpa [deposit, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
                (by rfl) hfit hawNext hawNextSmall hfpNext
                hreadNext hmemNext96 hmemNextLe hgapNext
                hnextFpNat
        · have hdepositGe : value.toNat ≤ deposit.toNat :=
            Nat.le_of_not_gt hdepositLt
          let high : UInt256 :=
            scratch_placeBidHighestBidWord (accOf a).2 I
          have hhighSrc :
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                ⟨6⟩ = high := by
            have hfind :=
              accountMapEquiv_storage_findD haccounts I.codeOwner
                ⟨6⟩ ⟨0⟩
            rw [henv]
            simp [Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, high,
              scratch_placeBidHighestBidWord] at hfind ⊢
            rw [← hfind]
          by_cases hplaceFalse : value.toNat ≤ high.toNat
          · obtain ⟨hbodyOk, hrdNext⟩ :=
              scratch_revealLoopBody_hashMatch_placeBidFalse_fromPacked_pair
                (I := I) (g := g)
                (s0 := s0)
                (k := kPacked) (C := CPacked)
                (mem := memPacked) (aw := awPacked)
                (rdata := ByteArray.empty)
                (cA := (accOf a).1) (σ := (accOf a).2)
                (L := L) (evm := evm)
              (values := values) (fakes := fakes)
              (secrets := secrets) (slot := slot) (i := idx a)
              (refund := refundOf a) (len := loopLen) (curLen := curLen)
                (revealEnd := revealEnd)
                (biddingEnd := biddingEnd)
                (secretsLen := secretsLenWord)
                (secretsEnd :=
                  secretsEnd)
                (fakesLen := fakesLenWord)
                (fakesEnd := fakesEnd)
                (valuesLen := valuesLenWord)
                (valuesEnd :=
                  valuesEnd)
                (sel := sel)
                (value := value) (secret := secret)
                (fakeWord := fakeWord) (blinded := blinded)
                (deposit := deposit) (high := high)
                (fp := a.fp) (fakeRaw := rawBoolWordValue word)
                (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
                (by simpa [hashWord] using hhashPacked)
                hblindedEvm
                (by simpa [hashWord] using hflag1)
                hdepositEvm hperm hbidsL hvaluesL hfakesL
                hsecretsL hiL hrefundL hlenSrc hboundBids
                hboundValues hboundFakes hboundSecrets
                hvalueLookup hfakeLookup hfakeNorm hsecretLookup
                hblindedSrc hdepositSrc hhighSrc
                (by simpa using hfakeZero) hfit hdepositGe
                hplaceFalse
                (by simpa [high] using hplaceFalse)
            obtain ⟨kNext, CNext, rdNext⟩ := hrdNext
            exact Or.inr <| by
              simpa [Inv, idx, refundOf, memOf, awOf, accOf] using
                scratch_revealLoopAdvance_refundAddedOk_zeroBlinded
                  (I := I) (g := g)
                  (s0 := s0)
                  (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
                  (v := v) (k := kNext) (C := CNext)
                  (loopLen := loopLen) (slot := slot)
                  (revealEnd := revealEnd)
                  (biddingEnd := biddingEnd)
                  (secretsLen := secretsLenWord)
                  (secretsEnd :=
                    secretsEnd)
                  (fakesLen := fakesLenWord)
                  (fakesEnd :=
                    fakesEnd)
                  (valuesLen := valuesLenWord)
                  (valuesEnd :=
                    valuesEnd)
                  (sel := sel)
                  (value := value) (secret := secret)
                  (deposit := deposit) (newFree := newFree)
                  (memNext := memNext) (awNext := awNext)
                  (values := values) (fakes := fakes)
                  (secrets := secrets) (a := a) (L := L)
                  (evm := evm)
                  hInvOrig hbodyOk
                  (by simpa [deposit, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
                  (by rfl) hfit hawNext hawNextSmall hfpNext
                  hreadNext hmemNext96 hmemNextLe hgapNext
                  hnextFpNat
          · have hlt : high.toNat < value.toNat :=
              Nat.lt_of_not_ge hplaceFalse
            let old : UInt256 :=
              scratch_placeBidHighestBidderWord (accOf a).2 I
            have holdSrc :
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  ⟨5⟩ = old := by
              have hfind :=
                accountMapEquiv_storage_findD haccounts I.codeOwner
                  ⟨5⟩ ⟨0⟩
              rw [henv]
              simp [Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, old,
                scratch_placeBidHighestBidderWord] at hfind ⊢
              rw [← hfind]
            by_cases hzero :
                UInt256.land old solcAddrMask = ⟨0⟩
            · obtain ⟨hbodyOk, hrdNext⟩ :=
                scratch_revealLoopBody_hashMatch_placeBidTrueZero_fromPacked_pair
                  (I := I) (g := g)
                  (s0 := s0)
                  (k := kPacked) (C := CPacked)
                  (mem := memPacked) (aw := awPacked)
                  (rdata := ByteArray.empty)
                  (cA := (accOf a).1) (σ := (accOf a).2)
                  (L := L) (evm := evm)
                  (values := values) (fakes := fakes)
                  (secrets := secrets) (slot := slot) (i := idx a)
                  (refund := refundOf a) (len := loopLen) (curLen := curLen)
                  (revealEnd := revealEnd)
                  (biddingEnd := biddingEnd)
                  (secretsLen := secretsLenWord)
                  (secretsEnd :=
                    secretsEnd)
                  (fakesLen := fakesLenWord)
                  (fakesEnd :=
                    fakesEnd)
                  (valuesLen := valuesLenWord)
                  (valuesEnd :=
                    valuesEnd)
                  (sel := sel)
                  (value := value) (secret := secret)
                  (fakeWord := fakeWord) (blinded := blinded)
                  (deposit := deposit) (high := high) (old := old)
                  (fp := a.fp) (fakeRaw := rawBoolWordValue word)
                  (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
                  (by simpa [hashWord] using hhashPacked)
                  hblindedEvm
                  (by simpa [hashWord] using hflag1)
                  hdepositEvm hperm hbidsL hvaluesL hfakesL
                  hsecretsL hiL hrefundL hlenSrc hboundBids
                  hboundValues hboundFakes hboundSecrets
                  hvalueLookup hfakeLookup hfakeNorm hsecretLookup
                  hblindedSrc hdepositSrc hhighSrc holdSrc
                  (by simpa using hfakeZero) hfit hdepositGe hlt
                  hzero
                  (by simpa [high] using hlt)
                  (by simpa [old] using hzero)
              obtain ⟨kNext, CNext, rdNext⟩ := hrdNext
              exact Or.inr <| by
                simpa [Inv, idx, refundOf, memOf, awOf, accOf] using
                  scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidZero
                    (I := I) (g := g)
                    (s0 := s0)
                    (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
                    (v := v) (k := kNext) (C := CNext)
                    (loopLen := loopLen) (slot := slot)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel)
                    (value := value) (secret := secret)
                    (deposit := deposit) (newFree := newFree)
                    (memNext := memNext) (awNext := awNext)
                    (values := values) (fakes := fakes)
                    (secrets := secrets) (a := a) (L := L)
                    (evm := evm)
                    hInvOrig hbodyOk
                    (by simpa [deposit, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
                    (by rfl) hfit hdepositGe hawNext hawNextSmall
                    hfpNext hreadNext hmemNext96 hmemNextLe
                    hgapNext hnextFpNat
            · let oldAddr : AccountAddress :=
                AccountAddress.ofNat
                  (UInt256.land old solcAddrMask).toNat
              let pending : UInt256 :=
                scratch_placeBidPendingWord (accOf a).2 I
              have holdAddr :
                  oldAddr =
                    AccountAddress.ofNat
                      (UInt256.land old solcAddrMask).toNat := rfl
              have hpendingSrc :
                  Solm.EVM.storageLoad evm
                      evm.executionEnv.codeOwner
                      (pendingReturnsSlot (.address oldAddr)) =
                    pending := by
                have hfind :=
                  accountMapEquiv_storage_findD haccounts I.codeOwner
                    (scratch_placeBidPendingSlot (accOf a).2 I) ⟨0⟩
                have hslotPending :
                    scratch_placeBidPendingSlot (accOf a).2 I =
                      pendingReturnsSlot (.address oldAddr) := by
                  unfold scratch_placeBidPendingSlot
                  simp [old, oldAddr]
                rw [henv]
                simp [Solm.EVM.storageLoad, State.lookupAccount,
                  Account.lookupStorage, pending,
                  scratch_placeBidPendingWord, hslotPending] at hfind ⊢
                rw [← hfind]
              by_cases hsum :
                  pending.toNat + high.toNat < UInt256.size
              · obtain ⟨hbodyOk, hrdNext⟩ :=
                  scratch_revealLoopBody_hashMatch_placeBidTrueNonzero_fromPacked_pair
                    (I := I) (g := g)
                    (s0 := s0)
                    (k := kPacked) (C := CPacked)
                    (mem := memPacked) (aw := awPacked)
                    (rdata := ByteArray.empty)
                    (cA := (accOf a).1) (σ := (accOf a).2)
                    (L := L) (evm := evm)
                    (values := values) (fakes := fakes)
                    (secrets := secrets) (slot := slot) (i := idx a)
                    (refund := refundOf a) (len := loopLen) (curLen := curLen)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel)
                    (value := value) (secret := secret)
                    (fakeWord := fakeWord) (blinded := blinded)
                    (deposit := deposit) (high := high) (old := old)
                    (pending := pending) (oldAddr := oldAddr)
                    (fp := a.fp)
                    (fakeRaw := rawBoolWordValue word)
                    (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
                    (by simpa [hashWord] using hhashPacked)
                    hblindedEvm
                    (by simpa [hashWord] using hflag1)
                    hdepositEvm hperm hbidsL hvaluesL hfakesL
                    hsecretsL hiL hrefundL hlenSrc hboundBids
                    hboundValues hboundFakes hboundSecrets
                    hvalueLookup hfakeLookup hfakeNorm hsecretLookup
                    hblindedSrc hdepositSrc hhighSrc holdSrc holdAddr
                    hpendingSrc (by simpa using hfakeZero) hfit
                    hdepositGe hlt hzero hsum
                    (by simpa [high] using hlt)
                    (by simpa [old] using hzero)
                    (by simpa [high, pending] using hsum)
                obtain ⟨kNext, CNext, rdNext⟩ := hrdNext
                exact Or.inr <| by
                  simpa [Inv, idx, refundOf, memOf, awOf, accOf] using
                    scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidNonzero_pendingHash
                      (I := I) (g := g)
                      (s0 := s0)
                      (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
                      (v := v) (k := kNext) (C := CNext)
                      (loopLen := loopLen) (slot := slot)
                      (revealEnd := revealEnd)
                      (biddingEnd := biddingEnd)
                      (secretsLen := secretsLenWord)
                      (secretsEnd :=
                        secretsEnd)
                      (fakesLen := fakesLenWord)
                      (fakesEnd :=
                        fakesEnd)
                      (valuesLen := valuesLenWord)
                      (valuesEnd :=
                        valuesEnd)
                      (sel := sel)
                      (value := value) (secret := secret)
                      (deposit := deposit) (high := high)
                      (old := old) (pending := pending)
                      (newFree := newFree) (oldAddr := oldAddr)
                      (memNext := memNext) (awNext := awNext)
                      (values := values) (fakes := fakes)
                      (secrets := secrets) (a := a) (L := L)
                      (evm := evm)
                      hInvOrig hbodyOk
                      (by
                        simpa [deposit, hnewFreeEq, hmemNextEq, hawNextEq] using rdNext)
                      (by rfl) (by rfl) (by rfl) (by rfl)
                      holdAddr hfit hdepositGe hsum hawNext
                      hawNextSmall hreadNext hmemNext96 hmemNextLe
                      hgapNext hnextFpNat
              · have hoverPending :
                  UInt256.size ≤ pending.toNat + high.toNat :=
                  Nat.le_of_not_gt hsum
                have heq :
                    EVM.Word.toBytesBE blinded =
                      (ffi.KEC (ByteArray.mk
                        (scratch_revealPackedBytes value false secret).toArray)).toList := by
                  exact scratch_revealPackedHash_eq_of_u256_eq_one
                    (blinded := blinded) (value := value)
                    (secret := secret) (fake := false)
                    (by simpa [hashWord] using hflag1)
                have hhashEval :=
                  scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L
                    (idx a) value secret false
                have hplaceBodyRev :
                    ExecTransitionBody blindAuctionConfig
                      blindAuctionContract evm
                      (scratch_placeBidStore
                        evm.executionEnv.source value)
                      placeBidFn.body .reverted :=
                  scratch_blindAuctionPlaceBidBodyReverts_true_nonzero_pendingOverflow
                    evm evm.executionEnv.source oldAddr value high old
                    pending hhighSrc holdSrc holdAddr hpendingSrc hlt
                    hzero hoverPending
                have hsrc :
                    ExecBlock blindAuctionConfig
                      { contract := blindAuctionContract, locals := L }
                      evm scratch_revealLoopBodyStmts .reverted :=
                  scratch_revealLoopBody_revert_placeBid_pendingOverflow_of_get
                    evm L values fakes secrets curLen (refundOf a)
                    (idx a) value secret blinded deposit
                    (rawBoolWordValue word)
                    (ffi.KEC (ByteArray.mk
                      (scratch_revealPackedBytes value false secret).toArray)).toList
                    hbidsL hvaluesL hfakesL hsecretsL hiL hrefundL
                    hlenSrc hboundBids hboundValues hboundFakes
                    hboundSecrets hvalueLookup hfakeLookup hfakeNorm
                    hsecretLookup hblindedSrc hdepositSrc hhashEval heq
                    hfit hdepositGe hplaceBodyRev
                obtain ⟨k1235, C1235, rd1235⟩ :=
                  scratch_blindAuctionRevealX_loopBody_packed_suffix
                    (I := I) (g := g)
                    (s0 := s0)
                    (k := kPacked) (C := CPacked)
                    (mem := memPacked) (aw := awPacked)
                    (rdata := ByteArray.empty)
                    (cA := (accOf a).1) (σ := (accOf a).2)
                    (secret := secret) (fakeWord := fakeWord)
                    (value := value) (slot := slot) (i := idx a)
                    (refund := refundOf a) (len := loopLen)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel) (fp := a.fp)
                    (hash := hashWord) (blinded := blinded)
                    (flag := ⟨1⟩)
                    (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
                    (by simpa [hashWord] using hhashPacked)
                    hblindedEvm
                    (by simpa [hashWord] using hflag1)
                obtain ⟨k1247, C1247, rd1247⟩ :=
                  scratch_blindAuctionRevealX_hashGuard_match_to1247
                    (I := I) (g := g)
                    (s0 := s0)
                    (k := k1235) (C := C1235)
                    (rdata := ByteArray.empty)
                    (acc := ((accOf a).1, (accOf a).2))
                    (secret := secret) (fake := fakeWord)
                    (value := value) (slot := slot) (i := idx a)
                    (refund := refundOf a) (len := loopLen)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel) rd1235
                obtain ⟨k1265, C1265, rd1265⟩ :=
                  scratch_blindAuctionRevealX_refundAdd_toPlaceCond
                    (I := I) (g := g)
                    (s0 := s0)
                    (k := k1247) (C := C1247)
                    (rdata := ByteArray.empty)
                    (cA := (accOf a).1) (σ := (accOf a).2)
                    (secret := secret) (fake := fakeWord)
                    (value := value) (slot := slot) (i := idx a)
                    (refund := refundOf a) (len := loopLen)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel)
                    (deposit := deposit) rd1247 hdepositEvm hfit
                have hoverEvm :
                    UInt256.size ≤
                      (scratch_placeBidPendingWord (accOf a).2 I).toNat +
                        (scratch_placeBidHighestBidWord
                          (accOf a).2 I).toNat := by
                  simpa [pending, high] using hoverPending
                have hrev :
                    RDrev blindAuctionBytecode g s0 :=
                  scratch_blindAuctionRevealX_placeCond_placeBid_true_nonzero_overflow_revert
                    (I := I) (g := g)
                    (s0 := s0)
                    (k := k1265) (C := C1265)
                    (mem := memNext) (aw := awNext)
                    (rdata := ByteArray.empty)
                    (cA := (accOf a).1) (σ := (accOf a).2)
                    (secret := secret) (value := value)
                    (slot := slot) (i := idx a)
                    (refund := deposit + refundOf a)
                    (len := loopLen)
                    (revealEnd := revealEnd)
                    (biddingEnd := biddingEnd)
                    (secretsLen := secretsLenWord)
                    (secretsEnd :=
                      secretsEnd)
                    (fakesLen := fakesLenWord)
                    (fakesEnd :=
                      fakesEnd)
                    (valuesLen := valuesLenWord)
                    (valuesEnd :=
                      valuesEnd)
                    (sel := sel)
                    (deposit := deposit)
                    (by simpa [hfakeZero, hnewFreeEq, hmemNextEq, hawNextEq] using rd1265)
                    hdepositEvm hdepositGe
                    (by simpa [high] using hlt)
                    (by simpa [old] using hzero)
                    hoverEvm hawNext
                exact Or.inl ⟨hsrc, hrev⟩
      · have hover :
            UInt256.size ≤ (refundOf a).toNat + deposit.toNat :=
          Nat.le_of_not_gt hfit
        have heq :
            EVM.Word.toBytesBE blinded =
              (ffi.KEC (ByteArray.mk
                (scratch_revealPackedBytes value false secret).toArray)).toList := by
          exact scratch_revealPackedHash_eq_of_u256_eq_one
            (blinded := blinded) (value := value) (secret := secret)
            (fake := false) (by simpa [hashWord] using hflag1)
        have hhashEval :=
          scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L
            (idx a) value secret false
        obtain ⟨k1235, C1235, rd1235⟩ :=
          scratch_blindAuctionRevealX_loopBody_packed_suffix
            (I := I) (g := g)
            (s0 := s0)
            (k := kPacked) (C := CPacked)
            (mem := memPacked) (aw := awPacked)
            (rdata := ByteArray.empty)
            (cA := (accOf a).1) (σ := (accOf a).2)
            (secret := secret) (fakeWord := fakeWord)
            (value := value) (slot := slot) (i := idx a)
            (refund := refundOf a) (len := loopLen)
            (revealEnd := revealEnd)
            (biddingEnd := biddingEnd)
            (secretsLen := secretsLenWord)
            (secretsEnd := secretsEnd)
            (fakesLen := fakesLenWord)
            (fakesEnd := fakesEnd)
            (valuesLen := valuesLenWord)
            (valuesEnd := valuesEnd)
            (sel := sel) (fp := a.fp)
            (hash := hashWord) (blinded := blinded) (flag := ⟨1⟩)
            (by simpa [hnewFreeEq] using rd1207) hfpPacked hlenPacked
            (by simpa [hashWord] using hhashPacked)
            hblindedEvm
            (by simpa [hashWord] using hflag1)
        obtain ⟨k1247, C1247, rd1247⟩ :=
          scratch_blindAuctionRevealX_hashGuard_match_to1247
            (I := I) (g := g)
            (s0 := s0)
            (k := k1235) (C := C1235)
            (rdata := ByteArray.empty)
            (acc := ((accOf a).1, (accOf a).2))
            (secret := secret) (fake := fakeWord)
            (value := value) (slot := slot) (i := idx a)
            (refund := refundOf a) (len := loopLen)
            (revealEnd := revealEnd)
            (biddingEnd := biddingEnd)
            (secretsLen := secretsLenWord)
            (secretsEnd := secretsEnd)
            (fakesLen := fakesLenWord)
            (fakesEnd := fakesEnd)
            (valuesLen := valuesLenWord)
            (valuesEnd := valuesEnd)
            (sel := sel) rd1235
        exact Or.inl <|
          scratch_revealLoopBody_refundOverflow_from1247_pair
            (I := I) (g := g)
            (s0 := s0)
            (k := k1247) (C := C1247)
            (mem := memNext) (aw := awNext)
            (rdata := ByteArray.empty)
            (cA := (accOf a).1) (σ := (accOf a).2)
            (L := L) (evm := evm)
            (values := values) (fakes := fakes)
            (secrets := secrets) (slot := slot) (i := idx a)
            (refund := refundOf a) (len := loopLen) (curLen := curLen)
            (revealEnd := revealEnd)
            (biddingEnd := biddingEnd)
            (secretsLen := secretsLenWord)
            (secretsEnd := secretsEnd)
            (fakesLen := fakesLenWord)
            (fakesEnd := fakesEnd)
            (valuesLen := valuesLenWord)
            (valuesEnd := valuesEnd)
            (sel := sel) (value := value)
            (secret := secret) (fakeWord := fakeWord)
            (blinded := blinded) (deposit := deposit)
            (fake := false) (fakeRaw := rawBoolWordValue word)
            (by simpa [hnewFreeEq, hmemNextEq, hawNextEq] using rd1247)
            hawNext hdepositEvm hbidsL hvaluesL hfakesL
            hsecretsL hiL hrefundL hlenSrc hboundBids hboundValues
            hboundFakes hboundSecrets hvalueLookup hfakeLookup
            hfakeNorm hsecretLookup hblindedSrc hdepositSrc hhashEval
            heq hover

end BlindAuction
