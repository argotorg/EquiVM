import Benchmarks.Midnight.RatifierABI

variable {fork : Ethereum.Fork}

/-! The dynamic byte buffer returned by source-level offer encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def offerBytes (offer : OfferData) : ByteArray :=
  (UInt256.ofNat 32).toByteArray ++ offerEncodedBytes offer

def offerBytesSize (offer : OfferData) : Nat := 32 + offerEncodedSize offer

theorem offerBytes_size (offer : OfferData) : (offerBytes offer).size = offerBytesSize offer := by
  rw [offerBytes, ByteArray.size_append, toByteArray_size, offerEncodedBytes_size]
  rfl

theorem offerBytesSize_padded (offer : OfferData) :
    paddedSize (offerBytesSize offer) = offerBytesSize offer := by
  simp only [offerBytesSize, offerEncodedSize, offerCallbackOffset, paddedSize]
  omega

theorem OfferData.encodeCall (offer : OfferData) (hc : OfferCanonical offer) :
    config.externalABI.encode? "encodeOffer" [Model.offerValue offer.value] = some (offerBytes offer)
    := by
  change encodeReturnValues? [Model.offerABI] [Model.abiValue (Model.offerValue offer.value)] = _
  rw [offer.abiOfferValue]
  have he := offer.encodeValue hc
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    show isDynamicABIType Model.offerABI = true from rfl, if_true, bind, Option.bind,
    encodeABIValuesFrom?, he, List.nil_append, List.append_nil, List.length_nil,
    Nat.add_zero]
  simp only [offerBytes, natBytes, word_toBytesBE_eq_toByteArray_toList]
  congr 1
  apply ByteArray.ext
  simp only [byteArray_toList_eq, ← Array.toList_append, Array.toArray_toList, ByteArray.data_append]
  rfl

def takeEncodedOfferFrame (frame : Frame) (offer : OfferData) : Frame :=
  { frame with locals := frame.locals.insert "encodedOffer" (.bytes (offerBytes offer)) }

theorem takeEncodeOfferSource {frame : Frame} {evm : State} {offer : OfferData}
    (hc : OfferCanonical offer)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    ABlock fork config evm frame (takeTransition.body.drop 64) (takeEncodedOfferFrame frame offer)
      (takeTransition.body.drop 65) := by
  have he : evalExpr? config frame evm (.abiEncodeCall "encodeOffer" [.var "offer"]) =
      .ok (.bytes (offerBytes offer)) := by
    simp only [evalExpr?, evalExprList?, ho, EvalResult.ofOption, bind, EvalResult.bind,
      pure, offer.encodeCall hc]
  exact ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letDecl he) h⟩

end Benchmarks.Midnight
