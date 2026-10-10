import Benchmarks.CompoundIII.Comet.AbsorbAfterAssetModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure AbsorbAssetData where
  assetOut : ByteArray
  seized : UInt256
  price : UInt256

def AbsorbAssetData.delta (d : AbsorbAssetData) (old : UInt256) : UInt256 :=
  absorbCollateralDelta old d.seized d.price d.assetOut

def absorbAssetInfoFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "assetInfo" (assetValue out) }

def absorbAssetFrame (frame : Frame) (delta : UInt256) (d : AbsorbAssetData) : Frame :=
  absorbAfterAssetFrame (absorbAssetInfoFrame frame d.assetOut) d.assetOut delta d.seized d.price

def absorbAssetBlock : List Stmt :=
  .internalCall "getAssetInfo_body" [.var "i"] "assetInfo" :: absorbAfterAssetBlock

inductive AbsorbAssetTrace (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (i delta : UInt256) (evm : State) : InternalValueOutcome AbsorbAssetData → Prop where
  | assetFailed {evm' z out}
      (hc : callViaEVM evm v.assetList 0 (assetPayload i) (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ AssetValid out)) :
      AbsorbAssetTrace v account i delta evm .reverted
  | assetOk {evm' out result}
      (hc : callViaEVM evm v.assetList 0 (assetPayload i) (true, evm', out) false)
      (hh : out.size < 2^255) (hv : AssetValid out)
      (ht : AbsorbAfterAssetTrace account out delta evm' result) :
      AbsorbAssetTrace v account i delta evm
        (result.map (fun price ↦ ⟨out,
          withdrawCollateralBalance evm' account (absorbAssetAddress out), price⟩))

end Benchmarks.CompoundIII.Comet
