import Benchmarks.CompoundIII.Comet.AbsorbCollateralMathModel
import Benchmarks.CompoundIII.Comet.AbsorbCollateralEvent
import Benchmarks.CompoundIII.Comet.PriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbCollateralPriceTrace (assetOut : ByteArray) (delta seized : UInt256) :
    State → Option (State × UInt256) → Prop where
  | priceFailed {evm evm' z out}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      AbsorbCollateralPriceTrace assetOut delta seized evm none
  | result {evm evm' out}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out) :
      AbsorbCollateralPriceTrace assetOut delta seized evm
        (if AbsorbCollateralMathValid delta seized (calldataWord out 32) assetOut then
          some (evm', calldataWord out 32) else none)

def absorbCollateralPriceBlock : List Stmt :=
  .internalCall "getPrice_body" [.field (.var "assetInfo") "priceFeed"] "__c5" ::
    (absorbCollateralMathBlock ++ [absorbCollateralEvent])

def absorbCollateralPriceFrame (frame : Frame) (price : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c5" (.int price.toNat) }

def absorbCollateralPriceResult (frame : Frame) (delta seized : UInt256) (assetOut : ByteArray) :
    Option (State × UInt256) → ExecResult
  | none => .reverted
  | some (evm, price) => .ok
      (absorbCollateralMathFrame (absorbCollateralPriceFrame frame price) delta seized price assetOut) evm

end Benchmarks.CompoundIII.Comet
