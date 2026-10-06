import Benchmarks.Dss.Cat.BiteConnect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — the success branch of `catBiteBody`

The all-success branch already shares one account map between the RD trace and typed EVM calls.
This wrapper passes its call chain and arithmetic side conditions directly to `catBiteSuccessLeaf`. -/
theorem catBiteSuccessBranch {σ σ₀ A I} {g : UInt256}
    {evmIlk evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
    {ilksOut urnsOut grabOut fessOut kickOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art id : UInt256}
    {acc : AccountMap}
    (hcode : I.code = catBytecode)
    (hret : RDret catBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id))
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hsz36 : 36 ≤ I.calldata.size) (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : solcSlotWordAt ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat) (hartPos : 0 < art.toNat)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
    (hvatCodeMid :
      0 < (UInt256.ofNat
        ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = some [bw id])
    (hAccountsFinal : acc = evmKick.accountMap) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact catBiteSuccessLeaf hcode hret hdispatch hdecode hsz36 hwv hvatCode0 hIlksCall hIlksDec
    hvatCodeIlk hUrnsCall hUrnsDec hlive hfitInkSpot hfitArtRate hfitDunkRoomWad hfitInkDart
    hfitDartRate hfitTabBase hfitLitterNew hspotPos hratePos hartPos hmilkChopPos hunsafe hlitLtBox
    hroomGeDust hdartPos hdinkPos hdartLim hdinkLim hvatCodeMid hGrabCall hGrabDec hvowCode
    hFessCall hFessDec hLitStore hflipCode hKickCall hKickDec hAccountsFinal

end Benchmarks.Dss.Cat
