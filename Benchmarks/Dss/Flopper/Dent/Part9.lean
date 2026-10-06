import Benchmarks.Dss.Flopper.Dent.Part8

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
theorem flopperDentBodyCoreLotNotLower
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLe :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat ≤
        (dentLotWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLeSolm : (dentLotStoredWord evmSolm I).toNat ≤ (dentLotWord I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLe
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_lotNotLower evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLeSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨memLot, _, _, hmemLot, hreadLot, rd2201⟩ :=
    flopperDentX_toLotLtGuardFromDecoded hlive hguy hticOk hendGt hbid hdecoded
  have hrev := flopperDentX_lotNotLowerFromGuard hlotLe hmemLot hreadLot rd2201
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreLotOneOverflow
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat <
      UInt256.size)
    (hlotOneOverflow :
      UInt256.size ≤
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
          dentOneWord.toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLtSolm : (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmSolm, dentBegWord, initState] using hbegFit
  have hlotOneOverflowSolm :
      UInt256.size ≤ (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotOneOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_lotOneOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneOverflowSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨_, _, _, _, _, rd2273⟩ :=
    flopperDentX_toLotLowerOkFromDecoded hlive hguy hticOk hendGt hbid hlotLt hdecoded
  have hrev := flopperDentX_lotOneOverflow hlotOneOverflow rd2273
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreBegLotOverflow
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegOverflow :
      UInt256.size ≤ (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLtSolm : (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLt
  have hbegOverflowSolm :
      UInt256.size ≤ (dentBegWord evmSolm).toNat * (dentLotWord I).toNat := by
    simpa [evmSolm, dentBegWord, initState] using hbegOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_begLotOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegOverflowSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨_, _, _, _, _, rd2273⟩ :=
    flopperDentX_toLotLowerOkFromDecoded hlive hguy hticOk hendGt hbid hlotLt hdecoded
  have hrev : RDrev flopperBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
    by_cases hlotOneFit :
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
          dentOneWord.toNat < UInt256.size
    · obtain ⟨_, _, rd2310⟩ := flopperDentX_lotOneOk hlotOneFit rd2273
      exact flopperDentX_begLotOverflow hbegOverflow rd2310
    · have hlotOneOverflow :
          UInt256.size ≤
            (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
              dentOneWord.toNat := by
        omega
      exact flopperDentX_lotOneOverflow hlotOneOverflow rd2273
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreInsufficientDecrease
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat <
      UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hinsuff :
      (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨533⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentEndWord, dentTimestampWord, initState] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLtSolm : (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmSolm, dentBegWord, initState] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotOneFit
  have hinsuffSolm : (dentLotOneWord evmSolm I).toNat < (dentBegLotWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotOneWord, dentLotStoredWord, dentBegLotWord, dentBegWord,
      initState] using hinsuff
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        .reverted := by
    exact flopperDentBodyReverts_insufficientDecrease evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hinsuffSolm
  have hdecoded :=
    flopperDentX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  obtain ⟨memLotOne, _, _, hmemLotOne, hreadLotOne, rd2322⟩ :=
    flopperDentX_toBegLotOkFromDecoded hlive hguy hticOk hendGt hbid hlotLt
      hlotOneFit hbegFit hdecoded
  have hrev := flopperDentX_insufficientDecreaseFromGuard hinsuff hmemLotOne hreadLotOne rd2322
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreAddOverflowCallerEq
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {memStart : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val =
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (rd2405 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmSolm, dentBegWord, initState] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerSolm : UInt256.ofNat evmSolm.executionEnv.source.val = dentGuyWord evmSolm I := by
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hcaller
  have httl :=
    dentRuntimeTtlWord_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have haddOverflowSolm :
      2 ^ 48 ≤
        (dentNow48Word evmSolm).toNat +
          (dentTtlWord (dentAfterLotStore evmSolm I)).toNat := by
    simpa [evmSolm, dentNow48Word, dentTimestampWord, initState, httl] using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body .reverted := by
    exact flopperDentBodyReverts_addOverflow_callerEq evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm haddOverflowSolm
  obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
  obtain ⟨_, _, rd2889⟩ := flopperDentX_callerEqOkFromGuard hcaller rd2435
  have hrev :=
    flopperDentX_addOverflowFromTail (g := Sat256.ofUInt256 g) hperm haddOverflow rd2889
  exact flopperDentBodyCoreRevert hcode hdispatch hdecode hbody hrev

theorem flopperDentBodyCoreSuccessCallerEq
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {memStart : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val =
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat < 2 ^ 48)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I))
    (rd2405 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2405⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (dentIdWord I)
  have hliveSolm : dentLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm, dentLiveWord, initState] using hlive
  have hguySolm : dentGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hzero
  have hticOkSolm :
      (dentTimestampWord evmSolm).toNat < (dentTicWord evmSolm I).toNat ∨
        dentTicWord evmSolm I = ⟨0⟩ := by
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, dentTimestampWord, dentTicWord, initState, packedSlot]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, dentTicWord, initState, packedSlot] using hzero
  have hendGtSolm : (dentTimestampWord evmSolm).toNat < (dentEndWord evmSolm I).toNat := by
    simpa [evmSolm, dentTimestampWord, dentEndWord, initState, packedSlot] using hendGt
  have hbidSolm : dentBidWord I = dentBidStoredWord evmSolm I := by
    simpa [evmSolm, dentBidStoredWord, initState] using hbid
  have hlotLtSolm :
      (dentLotWord I).toNat < (dentLotStoredWord evmSolm I).toNat := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotLt
  have hbegFitSolm :
      (dentBegWord evmSolm).toNat * (dentLotWord I).toNat < UInt256.size := by
    simpa [evmSolm, dentBegWord, initState] using hbegFit
  have hlotOneFitSolm :
      (dentLotStoredWord evmSolm I).toNat * dentOneWord.toNat < UInt256.size := by
    simpa [evmSolm, dentLotStoredWord, initState] using hlotOneFit
  have hsuffSolm :
      (dentBegLotWord evmSolm I).toNat ≤ (dentLotOneWord evmSolm I).toNat := by
    simpa [evmSolm, dentBegLotWord, dentBegWord, dentLotOneWord, dentLotStoredWord,
      initState] using hsuff
  have hcallerSolm : UInt256.ofNat evmSolm.executionEnv.source.val = dentGuyWord evmSolm I := by
    simpa [evmSolm, dentGuyWord, initState, packedSlot] using hcaller
  have httl :=
    dentRuntimeTtlWord_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have haddFitSolm :
      (dentNow48Word evmSolm).toNat +
          (dentTtlWord (dentAfterLotStore evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, dentNow48Word, dentTimestampWord, initState, httl] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (dentLocals I) dentTransition.body
        (.returned { contract := contract, locals := dentTicLocals evmSolm I }
          (dentPostState evmSolm I) none) := by
    exact flopperDentBodyReturns_success_callerEq evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
      hendGtSolm hbidSolm hlotLtSolm hbegFitSolm hlotOneFitSolm hsuffSolm
      hcallerSolm haddFitSolm
  obtain ⟨_, _, rd2435⟩ := flopperDentX_toCallerEqGuard rd2405
  obtain ⟨_, _, rd2889⟩ := flopperDentX_callerEqOkFromGuard hcaller rd2435
  have hret :=
    flopperDentX_successFromTail (g := Sat256.ofUInt256 g) hperm haddFit rd2889
  have hpostAccounts :=
    dentRuntimeTailSuccessAccountMap_eq_postState
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) haddFit
  exact flopperDentBodyCoreSuccessCallerEqBridge hcode hdispatch hdecode hbody hret hpostAccounts

set_option maxHeartbeats 2000000 in
theorem flopperDentBodyCoreMoveSuccessTicZero
    {σ σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {mem outMove : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨8⟩ σ I = ⟨1⟩)
    (hguy : solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I).toNat ∨
        uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (uint48Offset26Word (auctionPackedSlot (dentIdWord I)) σ I).toNat)
    (hbid : dentBidWord I = solcSlotWordAt (auctionBidSlot (dentIdWord I)) σ I)
    (hlotLt :
      (dentLotWord I).toNat <
        (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat)
    (hbegFit : (solcSlotWordAt ⟨4⟩ σ I).toNat * (dentLotWord I).toNat < UInt256.size)
    (hlotOneFit :
      (solcSlotWordAt (auctionLotSlot (dentIdWord I)) σ I).toNat *
        dentOneWord.toNat < UInt256.size)
    (hsuff :
      (dentBegLotWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (dentLotOneWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hcaller :
      UInt256.ofNat I.source.val ≠
        solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (solcAddressSlotWord ⟨2⟩ σ I) ≠ ⟨0⟩)
    (hticMove :
      uint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2545 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        solcAddressSlotWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outMove σ' k C)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcall :
      typedCallViaEVM config
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨2⟩ σ I).toNat))
        "move" 0
        [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
          .address (AccountAddress.ofNat
            (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ I).toNat),
          .int (Int.ofNat (dentBidWord I).toNat)]
        (true,
          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' },
          outMove) true)
    (hdispatch : dispatchMsg contract I.calldata = some dentTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dentTransition.params.map Param.name)
        (transitionSignature dentTransition).paramTypes I.calldata = some (dentLocals I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hashNoCode :
      Reasoning.Theory.extCodeSizeWord σ'
        (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I) = ⟨0⟩
  · exact flopperDentBodyCoreAshNoCodeMoveCallerNeTicZero hcode hwv hlive hguy hticOk
      hendGt hbid hlotLt hbegFit hlotOneFit hsuff hcaller hcodeSize hticMove hashNoCode
      rd2545 hmem hread64 hcall hdispatch hdecode
  · have hashCodeSize :
        Reasoning.Theory.extCodeSizeWord σ'
          (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩ :=
      hashNoCode
    obtain ⟨memAshSelector, σAsh, zAsh, outAsh, AinAsh, AAsh, k2690, C2690,
        rd2690, hashCall, houtAshSize, hmemAsh64, hreadAsh64, hmemAsh128Of,
        hreadAsh128Of⟩ :=
      flopperDentX_moveSuccessTicZeroAshCall
        (g := Sat256.ofUInt256 g) hperm hmem hread64 hticMove hashCodeSize hdepth rd2545
    let evmAshPre : EVM.State :=
      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ', substate := AinAsh }
    have hdepthNeAsh : evmAshPre.executionEnv.depth ≠ 1024 := by
      intro hbad
      have hbadI : I.depth = 1024 := by
        simpa [evmAshPre, initState] using hbad
      have hval : I.depth.val = 1024 := congrArg Fin.val hbadI
      omega
    by_cases hzAsh : zAsh = true
    · have rd2690True : RD flopperBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
          (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
            solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I :: ⟨0⟩ ::
            dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
          (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat)
          (UInt256.ofNat 8) outAsh σAsh k2690 C2690 := by
        simpa only [hzAsh] using rd2690
      have hashCallTrue :
          typedCallViaEVM config
            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := AinAsh }
            (EVM.address (AccountAddress.ofNat
              (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
            "Ash" 0 []
            (true,
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σAsh, substate := AAsh },
              outAsh) true := by
        simpa only [hzAsh] using hashCall
      obtain ⟨AAshCore, hashCallTrueCoreRaw⟩ :=
        typedCallViaEVM_zero_setSubstate hashCallTrue
          (by simpa [evmAshPre] using hdepthNeAsh) A'
      have hashCallTrueCore :
          typedCallViaEVM config
            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' }
            (EVM.address (AccountAddress.ofNat
              (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
            "Ash" 0 []
            (true,
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σAsh, substate := AAshCore },
              outAsh) true := by
        simpa using hashCallTrueCoreRaw
      by_cases houtAsh32 : 32 ≤ outAsh.size
      · have hmemAsh128 := hmemAsh128Of houtAsh32
        have hreadAsh128 := hreadAsh128Of houtAsh32
        by_cases hkissNoCode :
            Reasoning.Theory.extCodeSizeWord σAsh
              (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I) =
                ⟨0⟩
        · exact flopperDentBodyCoreKissNoCodeMoveCallerNeTicZero hcode hwv hlive hguy
            hticOk hendGt hbid hlotLt hbegFit hlotOneFit hsuff hcaller hcodeSize hticMove
            hashCodeSize hkissNoCode hdepth rd2690True hcall hashCallTrueCore houtAsh32
            houtAshSize hmemAsh64 hreadAsh64 hmemAsh128 hreadAsh128 hdispatch hdecode
        · have hkissCodeSize :
              Reasoning.Theory.extCodeSizeWord σAsh
                (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I) ≠
                  ⟨0⟩ := hkissNoCode
          obtain ⟨_, _, rd2731⟩ :=
            flopperDentX_ashCallSuccessDecodeOk houtAsh32 houtAshSize hmemAsh64 hreadAsh64
              hmemAsh128 hreadAsh128 rd2690True
          obtain ⟨_, _, rd2817⟩ :=
            flopperDentX_ashDecodeOkToKissExtcodesizeGuard hmemAsh128 hreadAsh64 rd2731
          let memAsh := outAsh.write 0 memAshSelector dentAshOutPtr.toNat
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat
          let memKissMap := twoWordHashMem (dentIdWord I) ⟨1⟩ memAsh
          let memKiss := dentKissCalldataMem (dentKissAmtWord I outAsh) memKissMap
          have hkissEncode :
              config.externalABI.encode? "kiss"
                  [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)] =
                some (memKiss.readWithPadding dentKissOutPtr.toNat dentKissInSize.toNat) := by
            simpa only [memKiss] using
              (dentKissEncode_eq (dentKissAmtWord I outAsh) (mem := memKissMap))
          obtain ⟨σKiss, zKiss, outKiss, AinKiss, AKiss, k2833, C2833,
              rd2833, hkissCall, houtKissSize⟩ :=
            flopperDentX_kissCall
              (g := Sat256.ofUInt256 g) hperm hkissCodeSize hdepth
              (by simpa only [memAsh, memKissMap, memKiss] using hkissEncode)
              (by simpa only [memAsh, memKissMap, memKiss] using rd2817)
          by_cases hzKiss : zKiss = true
          · have rd2833True : RD flopperBytecode I (Sat256.ofUInt256 g)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
                (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
                  solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
                  dentAshWord outAsh :: dentBidWord I :: dentLotWord I ::
                  dentIdWord I :: ⟨334⟩ :: sel :: [])
                memKiss (UInt256.ofNat 8) outKiss σKiss k2833 C2833 := by
              simpa only [hzKiss, memAsh, memKissMap, memKiss] using rd2833
            have hkissCallTrue :
                typedCallViaEVM config
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σAsh, substate := AinKiss }
                  (EVM.address (AccountAddress.ofNat
                    (solcAddressSlotWord (auctionPackedSlot (dentIdWord I))
                      σAsh I).toNat))
                  "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
                  (true,
                    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σKiss, substate := AKiss },
                    outKiss) true := by
              simpa only [hzKiss] using hkissCall
            by_cases haddFit :
                (UInt256.land (UInt256.ofNat I.header.timestamp) uint48Mask).toNat +
                    (dentRuntimeTtlWord I.codeOwner
                      (dentRuntimeAfterGuyMap I.codeOwner σKiss I) I).toNat <
                  2 ^ 48
            · exact flopperDentBodyCoreSuccessMoveCallerNeTicZeroKissSuccess
                hcode hperm hwv hlive hguy hticOk hendGt hbid hlotLt hbegFit hlotOneFit
                hsuff hcaller hcodeSize hticMove hashCodeSize hkissCodeSize haddFit
                hdepth rd2833True hcall hashCallTrueCore houtAsh32 hkissCallTrue
                hdispatch hdecode
            · exact flopperDentBodyCoreAddOverflowMoveCallerNeTicZeroKissSuccess
                hcode hperm hwv hlive hguy hticOk hendGt hbid hlotLt hbegFit hlotOneFit
                hsuff hcaller hcodeSize hticMove hashCodeSize hkissCodeSize
                (Nat.le_of_not_gt haddFit) hdepth rd2833True hcall hashCallTrueCore
                houtAsh32 hkissCallTrue hdispatch hdecode
          · have hzKissFalse : zKiss = false := by
              cases zKiss <;> simp at hzKiss ⊢
            have rd2833False : RD flopperBytecode I (Sat256.ofUInt256 g)
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2833⟩
                (⟨0⟩ :: dentKissEndPtr :: dentKissSelectorWord ::
                  solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σAsh I ::
                  dentAshWord outAsh :: dentBidWord I :: dentLotWord I ::
                  dentIdWord I :: ⟨334⟩ :: sel :: [])
                memKiss (UInt256.ofNat 8) outKiss σKiss k2833 C2833 := by
              simpa only [hzKissFalse, memAsh, memKissMap, memKiss] using rd2833
            have hkissCallFalse :
                typedCallViaEVM config
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σAsh, substate := AinKiss }
                  (EVM.address (AccountAddress.ofNat
                    (solcAddressSlotWord (auctionPackedSlot (dentIdWord I))
                      σAsh I).toNat))
                  "kiss" 0 [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
                  (false,
                    { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σKiss, substate := AKiss },
                    outKiss) true := by
              simpa only [hzKissFalse] using hkissCall
            exact flopperDentBodyCoreKissCallFailureMoveCallerNeTicZero hcode hwv
              hlive hguy hticOk hendGt hbid hlotLt hbegFit hlotOneFit hsuff hcaller
              hcodeSize hticMove hashCodeSize hkissCodeSize hdepth rd2833False hcall
              hashCallTrueCore houtAsh32 hkissCallFalse houtKissSize hdispatch hdecode
      · exact flopperDentBodyCoreAshDecodeShortMoveCallerNeTicZero hcode hwv
          hlive hguy hticOk hendGt hbid hlotLt hbegFit hlotOneFit hsuff hcaller hcodeSize
          hticMove hashCodeSize hdepth rd2690True hcall hashCallTrueCore (by omega)
          houtAshSize hmemAsh64 hreadAsh64 hdispatch hdecode
    · have hzAshFalse : zAsh = false := by
        cases zAsh <;> simp at hzAsh ⊢
      have rd2690False : RD flopperBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
          (⟨0⟩ :: dentAshEndPtr :: dentAshSelectorWord ::
            solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I :: ⟨0⟩ ::
            dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
          (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat)
          (UInt256.ofNat 8) outAsh σAsh k2690 C2690 := by
        simpa only [hzAshFalse] using rd2690
      have hashCallFalse :
          typedCallViaEVM config
            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := AinAsh }
            (EVM.address (AccountAddress.ofNat
              (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
            "Ash" 0 []
            (false,
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σAsh, substate := AAsh },
              outAsh) true := by
        simpa only [hzAshFalse] using hashCall
      obtain ⟨AAshCore, hashCallFalseCoreRaw⟩ :=
        typedCallViaEVM_zero_setSubstate hashCallFalse
          (by simpa [evmAshPre] using hdepthNeAsh) A'
      have hashCallFalseCore :
          typedCallViaEVM config
            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' }
            (EVM.address (AccountAddress.ofNat
              (solcAddressSlotWord (auctionPackedSlot (dentIdWord I)) σ' I).toNat))
            "Ash" 0 []
            (false,
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σAsh, substate := AAshCore },
              outAsh) true := by
        simpa using hashCallFalseCoreRaw
      exact flopperDentBodyCoreAshCallFailureMoveCallerNeTicZero hcode hwv hlive hguy
        hticOk hendGt hbid hlotLt hbegFit hlotOneFit hsuff hcaller hcodeSize hticMove
        hashCodeSize hdepth rd2690False hcall hashCallFalseCore houtAshSize hdispatch
        hdecode

end Benchmarks.Dss.Flopper
