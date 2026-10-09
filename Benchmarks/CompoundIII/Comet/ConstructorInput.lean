import Benchmarks.CompoundIII.Comet.ConstructorEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

/-- Canonical constructor asset data, with the widths checked by the deployment encoder. -/
structure ConstructorAsset where
  asset : AccountAddress
  priceFeed : AccountAddress
  decimals : Fin (2^8)
  borrowCollateralFactor : Fin (2^64)
  liquidateCollateralFactor : Fin (2^64)
  liquidationFactor : Fin (2^64)
  supplyCap : Fin (2^128)

namespace ConstructorAsset

def abiType : ABIType := .tuple
  [.elem .address,
    .elem .address,
    .elem (.int (.uint ⟨8, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨128, by decide⟩))]

def scalars (c : ConstructorAsset) : List ScalarReturn :=
  [constructorAddressScalar c.asset,
    constructorAddressScalar c.priceFeed,
    constructorUintScalar ⟨8, by decide⟩ c.decimals,
    constructorUintScalar ⟨64, by decide⟩ c.borrowCollateralFactor,
    constructorUintScalar ⟨64, by decide⟩ c.liquidateCollateralFactor,
    constructorUintScalar ⟨64, by decide⟩ c.liquidationFactor,
    constructorUintScalar ⟨128, by decide⟩ c.supplyCap]

def value (c : ConstructorAsset) : Value :=
  .tuple (c.scalars.map ScalarReturn.value)

theorem of_encoded {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? abiType value = some bytes) :
    ∃ c : ConstructorAsset, value = c.value := by
  obtain ⟨values, rfl, htuple⟩ := constructorEncode_tuple h
  have hs0 := constructorEncode_fields htuple
  obtain ⟨v0, rest0, bytes0, rfl, h0, hs1⟩ := constructorEncodeFields_cons hs0
  obtain ⟨x0, rfl⟩ := constructorEncode_address h0
  obtain ⟨v1, rest1, bytes1, rfl, h1, hs2⟩ := constructorEncodeFields_cons hs1
  obtain ⟨x1, rfl⟩ := constructorEncode_address h1
  obtain ⟨v2, rest2, bytes2, rfl, h2, hs3⟩ := constructorEncodeFields_cons hs2
  obtain ⟨x2, rfl⟩ := constructorEncode_uint h2
  obtain ⟨v3, rest3, bytes3, rfl, h3, hs4⟩ := constructorEncodeFields_cons hs3
  obtain ⟨x3, rfl⟩ := constructorEncode_uint h3
  obtain ⟨v4, rest4, bytes4, rfl, h4, hs5⟩ := constructorEncodeFields_cons hs4
  obtain ⟨x4, rfl⟩ := constructorEncode_uint h4
  obtain ⟨v5, rest5, bytes5, rfl, h5, hs6⟩ := constructorEncodeFields_cons hs5
  obtain ⟨x5, rfl⟩ := constructorEncode_uint h5
  obtain ⟨v6, rest6, bytes6, rfl, h6, hs7⟩ := constructorEncodeFields_cons hs6
  obtain ⟨x6, rfl⟩ := constructorEncode_uint h6
  have hrest := constructorEncodeFields_nil hs7
  subst rest6
  exact ⟨⟨x0, x1, x2, x3, x4, x5, x6⟩, rfl⟩

theorem staticArray_of_encoded {values : List Value} {bytes : List UInt8}
    (h : encodeABIStaticArrayElems? abiType values = some bytes) :
    ∃ assets : List ConstructorAsset, values = assets.map ConstructorAsset.value := by
  induction values generalizing bytes with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    rw [encodeABIStaticArrayElems?] at h
    obtain ⟨vb, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, _⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, rfl⟩ := of_encoded hv
    obtain ⟨assets, rfl⟩ := ih ht
    exact ⟨a :: assets, rfl⟩

theorem array_of_encoded {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.dynamicArray abiType) value = some bytes) :
    ∃ assets : List ConstructorAsset, value = .array (assets.map ConstructorAsset.value) := by
  cases value <;> simp only [encodeABIValue?] at h
  all_goals try contradiction
  obtain ⟨tail, ht, _⟩ := Option.bind_eq_some_iff.mp h
  rw [encodeABIArrayElems?] at ht
  have hd : isDynamicABIType abiType = false := by decide
  rw [hd] at ht
  simp only [Bool.false_eq_true, if_false] at ht
  obtain ⟨assets, rfl⟩ := staticArray_of_encoded ht
  exact ⟨assets, rfl⟩

end ConstructorAsset

structure ConstructorConfig where
  governor : AccountAddress
  pauseGuardian : AccountAddress
  baseToken : AccountAddress
  baseTokenPriceFeed : AccountAddress
  extensionDelegate : AccountAddress
  supplyKink : Fin (2^64)
  supplyPerYearInterestRateSlopeLow : Fin (2^64)
  supplyPerYearInterestRateSlopeHigh : Fin (2^64)
  supplyPerYearInterestRateBase : Fin (2^64)
  borrowKink : Fin (2^64)
  borrowPerYearInterestRateSlopeLow : Fin (2^64)
  borrowPerYearInterestRateSlopeHigh : Fin (2^64)
  borrowPerYearInterestRateBase : Fin (2^64)
  storeFrontPriceFactor : Fin (2^64)
  trackingIndexScale : Fin (2^64)
  baseTrackingSupplySpeed : Fin (2^64)
  baseTrackingBorrowSpeed : Fin (2^64)
  baseMinForRewards : Fin (2^104)
  baseBorrowMin : Fin (2^104)
  targetReserves : Fin (2^104)
  assetConfigs : List ConstructorAsset

namespace ConstructorConfig

def abiType : ABIType := .tuple
  [.elem .address,
    .elem .address,
    .elem .address,
    .elem .address,
    .elem .address,
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨104, by decide⟩)),
    .elem (.int (.uint ⟨104, by decide⟩)),
    .elem (.int (.uint ⟨104, by decide⟩)),
    .dynamicArray ConstructorAsset.abiType]

def scalars (c : ConstructorConfig) : List ScalarReturn :=
  [constructorAddressScalar c.governor,
    constructorAddressScalar c.pauseGuardian,
    constructorAddressScalar c.baseToken,
    constructorAddressScalar c.baseTokenPriceFeed,
    constructorAddressScalar c.extensionDelegate,
    constructorUintScalar ⟨64, by decide⟩ c.supplyKink,
    constructorUintScalar ⟨64, by decide⟩ c.supplyPerYearInterestRateSlopeLow,
    constructorUintScalar ⟨64, by decide⟩ c.supplyPerYearInterestRateSlopeHigh,
    constructorUintScalar ⟨64, by decide⟩ c.supplyPerYearInterestRateBase,
    constructorUintScalar ⟨64, by decide⟩ c.borrowKink,
    constructorUintScalar ⟨64, by decide⟩ c.borrowPerYearInterestRateSlopeLow,
    constructorUintScalar ⟨64, by decide⟩ c.borrowPerYearInterestRateSlopeHigh,
    constructorUintScalar ⟨64, by decide⟩ c.borrowPerYearInterestRateBase,
    constructorUintScalar ⟨64, by decide⟩ c.storeFrontPriceFactor,
    constructorUintScalar ⟨64, by decide⟩ c.trackingIndexScale,
    constructorUintScalar ⟨64, by decide⟩ c.baseTrackingSupplySpeed,
    constructorUintScalar ⟨64, by decide⟩ c.baseTrackingBorrowSpeed,
    constructorUintScalar ⟨104, by decide⟩ c.baseMinForRewards,
    constructorUintScalar ⟨104, by decide⟩ c.baseBorrowMin,
    constructorUintScalar ⟨104, by decide⟩ c.targetReserves]

def value (c : ConstructorConfig) : Value :=
  .tuple (c.scalars.map ScalarReturn.value ++ [.array (c.assetConfigs.map ConstructorAsset.value)])

theorem of_encoded {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? abiType value = some bytes) :
    ∃ c : ConstructorConfig, value = c.value := by
  obtain ⟨values, rfl, htuple⟩ := constructorEncode_tuple h
  have hs0 := constructorEncode_fields htuple
  obtain ⟨v0, rest0, bytes0, rfl, h0, hs1⟩ := constructorEncodeFields_cons hs0
  obtain ⟨x0, rfl⟩ := constructorEncode_address h0
  obtain ⟨v1, rest1, bytes1, rfl, h1, hs2⟩ := constructorEncodeFields_cons hs1
  obtain ⟨x1, rfl⟩ := constructorEncode_address h1
  obtain ⟨v2, rest2, bytes2, rfl, h2, hs3⟩ := constructorEncodeFields_cons hs2
  obtain ⟨x2, rfl⟩ := constructorEncode_address h2
  obtain ⟨v3, rest3, bytes3, rfl, h3, hs4⟩ := constructorEncodeFields_cons hs3
  obtain ⟨x3, rfl⟩ := constructorEncode_address h3
  obtain ⟨v4, rest4, bytes4, rfl, h4, hs5⟩ := constructorEncodeFields_cons hs4
  obtain ⟨x4, rfl⟩ := constructorEncode_address h4
  obtain ⟨v5, rest5, bytes5, rfl, h5, hs6⟩ := constructorEncodeFields_cons hs5
  obtain ⟨x5, rfl⟩ := constructorEncode_uint h5
  obtain ⟨v6, rest6, bytes6, rfl, h6, hs7⟩ := constructorEncodeFields_cons hs6
  obtain ⟨x6, rfl⟩ := constructorEncode_uint h6
  obtain ⟨v7, rest7, bytes7, rfl, h7, hs8⟩ := constructorEncodeFields_cons hs7
  obtain ⟨x7, rfl⟩ := constructorEncode_uint h7
  obtain ⟨v8, rest8, bytes8, rfl, h8, hs9⟩ := constructorEncodeFields_cons hs8
  obtain ⟨x8, rfl⟩ := constructorEncode_uint h8
  obtain ⟨v9, rest9, bytes9, rfl, h9, hs10⟩ := constructorEncodeFields_cons hs9
  obtain ⟨x9, rfl⟩ := constructorEncode_uint h9
  obtain ⟨v10, rest10, bytes10, rfl, h10, hs11⟩ := constructorEncodeFields_cons hs10
  obtain ⟨x10, rfl⟩ := constructorEncode_uint h10
  obtain ⟨v11, rest11, bytes11, rfl, h11, hs12⟩ := constructorEncodeFields_cons hs11
  obtain ⟨x11, rfl⟩ := constructorEncode_uint h11
  obtain ⟨v12, rest12, bytes12, rfl, h12, hs13⟩ := constructorEncodeFields_cons hs12
  obtain ⟨x12, rfl⟩ := constructorEncode_uint h12
  obtain ⟨v13, rest13, bytes13, rfl, h13, hs14⟩ := constructorEncodeFields_cons hs13
  obtain ⟨x13, rfl⟩ := constructorEncode_uint h13
  obtain ⟨v14, rest14, bytes14, rfl, h14, hs15⟩ := constructorEncodeFields_cons hs14
  obtain ⟨x14, rfl⟩ := constructorEncode_uint h14
  obtain ⟨v15, rest15, bytes15, rfl, h15, hs16⟩ := constructorEncodeFields_cons hs15
  obtain ⟨x15, rfl⟩ := constructorEncode_uint h15
  obtain ⟨v16, rest16, bytes16, rfl, h16, hs17⟩ := constructorEncodeFields_cons hs16
  obtain ⟨x16, rfl⟩ := constructorEncode_uint h16
  obtain ⟨v17, rest17, bytes17, rfl, h17, hs18⟩ := constructorEncodeFields_cons hs17
  obtain ⟨x17, rfl⟩ := constructorEncode_uint h17
  obtain ⟨v18, rest18, bytes18, rfl, h18, hs19⟩ := constructorEncodeFields_cons hs18
  obtain ⟨x18, rfl⟩ := constructorEncode_uint h18
  obtain ⟨v19, rest19, bytes19, rfl, h19, hs20⟩ := constructorEncodeFields_cons hs19
  obtain ⟨x19, rfl⟩ := constructorEncode_uint h19
  obtain ⟨v20, rest20, bytes20, rfl, h20, hs21⟩ := constructorEncodeFields_cons hs20
  obtain ⟨assets, rfl⟩ := ConstructorAsset.array_of_encoded h20
  have hrest := constructorEncodeFields_nil hs21
  subst rest20
  exact ⟨⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, assets⟩, rfl⟩

end ConstructorConfig

theorem cometConstructorInput {args : List Value} {bytes : List UInt8}
    (h : encodeABIValues? (contract.ctor.params.map Param.ty) args = some bytes) :
    ∃ c : ConstructorConfig, args = [c.value] := by
  have ht : contract.ctor.params.map Param.ty = [ConstructorConfig.abiType] := rfl
  rw [ht] at h
  have hs0 := constructorEncode_fields h
  obtain ⟨v, rest, vb, rfl, hv, hs1⟩ := constructorEncodeFields_cons hs0
  have hrest := constructorEncodeFields_nil hs1
  subst rest
  obtain ⟨c, rfl⟩ := ConstructorConfig.of_encoded hv
  exact ⟨c, rfl⟩

end Benchmarks.CompoundIII.Comet
