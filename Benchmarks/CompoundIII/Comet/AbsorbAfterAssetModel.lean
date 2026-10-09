import Benchmarks.CompoundIII.Comet.AbsorbSeizeModel
import Benchmarks.CompoundIII.Comet.AbsorbCollateralPriceModel
import Benchmarks.CompoundIII.Comet.InternalValueOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbAssetAddress (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (calldataWord out 32).toNat

def absorbAssetNameFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "asset" (.address (absorbAssetAddress out)) }

def absorbAssetSeizedFrame (frame : Frame) (out : ByteArray) (seized : UInt256) : Frame :=
  let named := absorbAssetNameFrame frame out
  { named with locals := named.locals.insert "seizeAmount" (.int seized.toNat) }

def absorbAfterAssetFrame (frame : Frame) (out : ByteArray) (delta seized price : UInt256) : Frame :=
  absorbCollateralMathFrame
    (absorbCollateralPriceFrame (absorbAssetSeizedFrame frame out seized) price)
    delta seized price out

def absorbAfterAssetBlock : List Stmt :=
  .letDecl "asset" (some (.elem .address)) (.field (.var "assetInfo") "asset") ::
    (absorbSeizeBlock ++ absorbCollateralPriceBlock)

inductive AbsorbAfterAssetTrace (account : AccountAddress) (out : ByteArray)
    (delta : UInt256) (evm : State) : InternalValueOutcome UInt256 → Prop where
  | seizeReverted
      (h : absorbSeizeOutcome evm account (absorbAssetAddress out) = .reverted) :
      AbsorbAfterAssetTrace account out delta evm .reverted
  | seizeStatic
      (h : absorbSeizeOutcome evm account (absorbAssetAddress out) = .staticViolation) :
      AbsorbAfterAssetTrace account out delta evm .staticViolation
  | priced {seizedState result}
      (h : absorbSeizeOutcome evm account (absorbAssetAddress out) = .ok seizedState)
      (ht : AbsorbCollateralPriceTrace out delta
        (withdrawCollateralBalance evm account (absorbAssetAddress out)) seizedState result) :
      AbsorbAfterAssetTrace account out delta evm (InternalValueOutcome.ofOption result)

end Benchmarks.CompoundIII.Comet
