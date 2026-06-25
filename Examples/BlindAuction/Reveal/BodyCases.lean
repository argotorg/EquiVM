import Examples.BlindAuction.Reveal.FakeFalse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

namespace BlindAuction

def RevealLoopBodyOutcome (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (gh : BlockHeader) (bl : ProcessedBlocks) (A : Substate)
    (v _k _C : ℕ)
    (loopLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (values fakes secrets : List Value) (_a : RevealLoopCursor) (L : Store)
    (evm : EVM.State) : Prop :=
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
      a'.mem a'.aw ByteArray.empty a'.acc k' C'

def RevealLoopRunFromStart (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (gh : BlockHeader) (bl : ProcessedBlocks) (A : Substate)
    (loopLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (values fakes secrets : List Value) : Prop :=
  ∀ v a L evm, RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a L evm → ∀ k C,
    RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack a.idx a.refund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      a.mem a.aw ByteArray.empty a.acc k C →
    (∃ a' L' evm' k' C',
      ExecForLoop blindAuctionConfig
        { contract := blindAuctionContract, locals := L } evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok { contract := blindAuctionContract, locals := L' } evm') ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A 0 a' L' evm' ∧
      RD blindAuctionBytecode I g s0 ⟨1331⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C') ∨
    (ExecForLoop blindAuctionConfig
        { contract := blindAuctionContract, locals := L } evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0)

theorem scratch_revealLoop_from_bodyOutcome_or_revert {I : ExecutionEnv} {g : Sat256}
    {s0 : State}
    (len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (values fakes secrets : List Value)
    (σ₀ : AccountMap) (gh : BlockHeader) (bl : ProcessedBlocks) (A : Substate)
    (hbody : ∀ v a L evm,
        RevealLoopInv len values fakes secrets I σ₀ gh bl A (v + 1) a L evm → ∀ k C,
          RD blindAuctionBytecode I g s0 ⟨1023⟩
            (scratch_revealEvmLoopStack a.idx a.refund len revealEnd biddingEnd
              secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
            a.mem a.aw ByteArray.empty a.acc k C →
          RevealLoopBodyOutcome I g s0 σ₀ gh bl A v k C len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel
            values fakes secrets a L evm) :
    RevealLoopRunFromStart I g s0 σ₀ gh bl A len revealEnd biddingEnd secretsLen secretsEnd
      fakesLen fakesEnd valuesLen valuesEnd sel values fakes secrets := by
  unfold RevealLoopRunFromStart
  refine scratch_revealLoop_from_body_or_revert
    (I := I) (g := g) (s0 := s0) (rdata := ByteArray.empty)
    len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel
    (RevealLoopInv len values fakes secrets I σ₀ gh bl A)
    (fun a => a.idx) (fun a => a.refund) (fun a => a.mem) (fun a => a.aw) (fun a => a.acc)
    ?_ ?_
  · intro v a L evm hInv
    simpa using RevealLoopInv_shape len values fakes secrets I σ₀ gh bl A v a L evm hInv
  · intro v a L evm hInv k C rd1023
    change RevealLoopBodyOutcome I g s0 σ₀ gh bl A v k C len revealEnd biddingEnd
      secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel values fakes secrets a L evm
    exact hbody v a L evm hInv k C rd1023

set_option maxHeartbeats 10000000 in
theorem scratch_revealLoopBody_decoded_inBounds_fromLoopStart {I} {g : Sat256}
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
    (hvaluesEq : loopLen = valuesLenWord)
    (hfp128 : a.fp.toNat + 128 < UInt256.size)
    (hfp96 : 96 ≤ a.fp.toNat)
    (hvalueBound : a.idx.toNat < valuesLenWord.toNat)
    (hfakesBound : a.idx.toNat < fakesLenWord.toNat)
    (hsecretsBound : a.idx.toNat < secretsLenWord.toNat)
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
    RevealLoopBodyOutcome I g s0 σ₀ gh bl A v k C loopLen revealEnd biddingEnd
      secretsLenWord secretsEnd fakesLenWord fakesEnd valuesLenWord valuesEnd sel
      values fakes secrets a L evm := by
  by_cases hfakeZero : fakeWord = ⟨0⟩
  · exact scratch_revealLoopBody_fakeFalse_fromLoopStart
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C)
      (loopLen := loopLen) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLenWord := secretsLenWord) (secretsEnd := secretsEnd)
      (fakesLenWord := fakesLenWord) (fakesEnd := fakesEnd)
      (valuesLenWord := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
      (value := value) (secret := secret) (fakeWord := fakeWord) (word := word)
      (values := values) (fakes := fakes) (secrets := secrets)
      (a := a) (L := L) (evm := evm)
      hInv rd1023 hbaseHash hlenLoad hboundBids hdataHash hvaluesEq
      hfp128 hfp96 hvalueBound hfakesBound hsecretsBound hvalueLoad hfakeSlt hfakeLoad
      hsecretLoad hfakeWordEq hfakeWordSmall hfakeZero
      hbidsL hvaluesL hfakesL hsecretsL hiL hlenL hrefundL hlenSrc
      hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hsecretLookup hperm
  · by_cases hfakeOne : fakeWord = ⟨1⟩
    · exact scratch_revealLoopBody_fakeTrue_fromLoopStart
        (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
        (v := v) (k := k) (C := C)
        (loopLen := loopLen) (curLen := curLen)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd)
        (secretsLen := secretsLenWord) (secretsEnd := secretsEnd)
        (fakesLen := fakesLenWord) (fakesEnd := fakesEnd)
        (valuesLen := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
        (value := value) (secret := secret) (fakeWord := fakeWord) (word := word)
        (values := values) (fakes := fakes) (secrets := secrets)
        (a := a) (L := L) (evm := evm)
        hInv rd1023 hbaseHash hlenLoad hboundBids hdataHash hfp128 hfp96
        hvalueBound hfakesBound hsecretsBound hvalueLoad hfakeSlt hfakeLoad hsecretLoad
        hfakeWordEq hfakeWordSmall hfakeOne hbidsL hvaluesL hfakesL hsecretsL hiL
        hrefundL hlenSrc hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup
        hsecretLookup hperm
    · have hfakeNorm :
          normalizeRawBoolWord? (rawBoolWordValue word) = .revert := by
        exact scratch_normalizeRawBoolWord_revert_of_u256
          hfakeWordSmall
          (by simpa [hfakeWordEq] using hfakeZero)
          (by simpa [hfakeWordEq] using hfakeOne)
      exact Or.inl <|
        scratch_revealLoopBody_fakeInvalid_fromLoopStart
          (I := I) (g := g) (s0 := s0) (k := k) (C := C)
          (loopLen := loopLen) (curLen := curLen)
          (revealEnd := revealEnd) (biddingEnd := biddingEnd)
          (secretsLen := secretsLenWord) (secretsEnd := secretsEnd)
          (fakesLen := fakesLenWord) (fakesEnd := fakesEnd)
          (valuesLen := valuesLenWord) (valuesEnd := valuesEnd) (sel := sel)
          (value := value) (fakeWord := fakeWord) (fakeRaw := rawBoolWordValue word)
          (values := values) (fakes := fakes) (secrets := secrets)
          (a := a) (L := L) (evm := evm)
          rd1023 hbaseHashWord hlenLoad hboundBids hdataHash
          hvalueBound hfakesBound hvalueLoad hfakeSlt hfakeLoad
          hfakeZero hfakeOne hbidsL hvaluesL hfakesL hiL hlenSrc
          hboundValues hboundFakes hvalueLookup hfakeLookup hfakeNorm

end BlindAuction
