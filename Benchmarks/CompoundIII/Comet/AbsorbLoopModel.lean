import Benchmarks.CompoundIII.Comet.AbsorbAssetModel
import Benchmarks.CompoundIII.Comet.IsInAssetSource
import Benchmarks.CompoundIII.Comet.AssetSearch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def absorbLoopBody : List Stmt :=
  [.internalCall "isInAsset" [.var "assetsIn", .var "i", .var "_reserved"] "__c3",
    .ite (.var "__c3") absorbAssetBlock [], assetSearchIncrement]

def absorbLoopBlock : List Stmt := [.while assetSearchCond absorbLoopBody]

inductive AbsorbLoopTrace (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (assets reserved : UInt256) : Nat → UInt256 → State → InternalValueOutcome UInt256 → Prop where
  | exhausted {i delta evm} (hi : v.numAssets.toNat ≤ i) :
      AbsorbLoopTrace v account assets reserved i delta evm (.ok evm delta)
  | skipped {i delta evm result} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = false)
      (ht : AbsorbLoopTrace v account assets reserved (i + 1) delta evm result) :
      AbsorbLoopTrace v account assets reserved i delta evm result
  | reverted {i delta evm} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (ht : AbsorbAssetTrace v account (UInt256.ofNat i) delta evm .reverted) :
      AbsorbLoopTrace v account assets reserved i delta evm .reverted
  | staticViolation {i delta evm} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (ht : AbsorbAssetTrace v account (UInt256.ofNat i) delta evm .staticViolation) :
      AbsorbLoopTrace v account assets reserved i delta evm .staticViolation
  | next {i delta evm evm' d result} (hi : i < v.numAssets.toNat)
      (hm : isInAssetBool assets (UInt256.ofNat i) reserved = true)
      (hv : AbsorbAssetTrace v account (UInt256.ofNat i) delta evm (.ok evm' d))
      (ht : AbsorbLoopTrace v account assets reserved (i + 1) (d.delta delta) evm' result) :
      AbsorbLoopTrace v account assets reserved i delta evm result

end Benchmarks.CompoundIII.Comet
