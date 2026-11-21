import Benchmarks.Midnight.MarketData
import Benchmarks.Midnight.BoolDecode

/-! Typed offers and the fifteen-word layout used by the take decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure OfferData where
  market : MarketData
  buy : UInt256
  maker : AccountAddress
  start : UInt256
  expiry : UInt256
  tick : UInt256
  group : UInt256
  callback : AccountAddress
  callbackData : ByteArray
  receiverIfMakerIsSeller : AccountAddress
  ratifier : AccountAddress
  reduceOnly : UInt256
  maxUnits : UInt256
  maxAssets : UInt256
  continuousFeeCap : UInt256

def OfferData.value (o : OfferData) : Value :=
  .tuple [o.market.value, wordToElem .bool o.buy, .address o.maker,
    .int o.start.toNat, .int o.expiry.toNat, .int o.tick.toNat, wordBytes32Value o.group,
    .address o.callback, .bytes o.callbackData, .address o.receiverIfMakerIsSeller,
    .address o.ratifier, wordToElem .bool o.reduceOnly, .int o.maxUnits.toNat,
    .int o.maxAssets.toNat, .int o.continuousFeeCap.toNat]

def OfferData.words (o : OfferData) (marketPtr callbackPtr : UInt256) : List UInt256 :=
  [marketPtr, o.buy, UInt256.ofNat o.maker.val, o.start, o.expiry, o.tick, o.group,
    UInt256.ofNat o.callback.val, callbackPtr, UInt256.ofNat o.receiverIfMakerIsSeller.val,
    UInt256.ofNat o.ratifier.val, o.reduceOnly, o.maxUnits, o.maxAssets, o.continuousFeeCap]

def OfferData.at (bytes : ByteArray) (base : Nat) (market : MarketData)
    (callbackData : ByteArray) : OfferData :=
  ⟨market, calldataWord bytes (base + 32),
    AccountAddress.ofNat (calldataWord bytes (base + 64)).toNat,
    calldataWord bytes (base + 96), calldataWord bytes (base + 128),
    calldataWord bytes (base + 160), calldataWord bytes (base + 192),
    AccountAddress.ofNat (calldataWord bytes (base + 224)).toNat, callbackData,
    AccountAddress.ofNat (calldataWord bytes (base + 288)).toNat,
    AccountAddress.ofNat (calldataWord bytes (base + 320)).toNat,
    calldataWord bytes (base + 352), calldataWord bytes (base + 384),
    calldataWord bytes (base + 416), calldataWord bytes (base + 448)⟩

def OfferData.tailCanonicalAt (bytes : ByteArray) (base : Nat) : Prop :=
  (calldataWord bytes (base + 288)).toNat < EVM.addressModulus ∧
    (calldataWord bytes (base + 320)).toNat < EVM.addressModulus ∧
    (calldataWord bytes (base + 352) = ⟨0⟩ ∨ calldataWord bytes (base + 352) = ⟨1⟩) ∧
    (calldataWord bytes (base + 384)).toNat < 2^128 ∧
    (calldataWord bytes (base + 416)).toNat < 2^128

def OfferData.canonicalAt (bytes : ByteArray) (base : Nat) : Prop :=
  (calldataWord bytes (base + 32) = ⟨0⟩ ∨ calldataWord bytes (base + 32) = ⟨1⟩) ∧
    (calldataWord bytes (base + 64)).toNat < EVM.addressModulus ∧
    (calldataWord bytes (base + 224)).toNat < EVM.addressModulus ∧
    OfferData.tailCanonicalAt bytes base

instance (bytes : ByteArray) (base : Nat) : Decidable (OfferData.tailCanonicalAt bytes base) := by
  unfold OfferData.tailCanonicalAt
  infer_instance

instance (bytes : ByteArray) (base : Nat) : Decidable (OfferData.canonicalAt bytes base) := by
  unfold OfferData.canonicalAt OfferData.tailCanonicalAt
  infer_instance

theorem OfferData.abiValue (o : OfferData) : Model.abiValue o.value = o.value := by
  simp only [OfferData.value, Model.abiValue, Model.abiValues, MarketData.abiValue,
    wordBytes32Value, wordToElem]
  split <;> split <;> rfl

end Benchmarks.Midnight
