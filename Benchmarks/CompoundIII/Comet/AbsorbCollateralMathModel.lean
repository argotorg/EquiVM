import Benchmarks.CompoundIII.Comet.AssetSource
import Benchmarks.CompoundIII.Comet.MulPrice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbCollateralValue (seized price : UInt256) (out : ByteArray) : UInt256 :=
  mulPriceWord seized price (calldataWord out 96)

def absorbCollateralContribution (seized price : UInt256) (out : ByteArray) : UInt256 :=
  mulFactorWord (absorbCollateralValue seized price out) (calldataWord out 192)

def absorbCollateralDelta (delta seized price : UInt256) (out : ByteArray) : UInt256 :=
  delta + absorbCollateralContribution seized price out

def AbsorbCollateralWordsValid (delta seized price scale factor : UInt256) : Prop :=
  MulPriceValid seized price scale ∧
    (mulPriceWord seized price scale).toNat * factor.toNat < UInt256.size ∧
    delta.toNat + (mulFactorWord (mulPriceWord seized price scale) factor).toNat < UInt256.size

instance absorbCollateralWordsDecidable (delta seized price scale factor : UInt256) :
    Decidable (AbsorbCollateralWordsValid delta seized price scale factor) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def AbsorbCollateralMathValid (delta seized price : UInt256) (out : ByteArray) : Prop :=
  AbsorbCollateralWordsValid delta seized price (calldataWord out 96) (calldataWord out 192)

instance absorbCollateralMathDecidable (delta seized price : UInt256) (out : ByteArray) :
    Decidable (AbsorbCollateralMathValid delta seized price out) :=
  inferInstanceAs (Decidable
    (AbsorbCollateralWordsValid delta seized price (calldataWord out 96) (calldataWord out 192)))

def absorbCollateralMathBlock : List Stmt :=
  [.internalCall "mulPrice"
      [.var "seizeAmount", .var "__c5", .field (.var "assetInfo") "scale"] "value",
    .internalCall "mulFactor"
      [.var "value", .field (.var "assetInfo") "liquidationFactor"] "__c7",
    .assign .localVar ⟨"deltaValue", []⟩
      (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "deltaValue") (.var "__c7")))]

def absorbCollateralValueFrame (frame : Frame) (seized price : UInt256) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "value" (.int (absorbCollateralValue seized price out).toNat) }

def absorbCollateralFactorFrame (frame : Frame) (seized price : UInt256) (out : ByteArray) : Frame :=
  let f := absorbCollateralValueFrame frame seized price out
  { f with locals := f.locals.insert "__c7" (.int (absorbCollateralContribution seized price out).toNat) }

def absorbCollateralMathFrame (frame : Frame) (delta seized price : UInt256) (out : ByteArray) : Frame :=
  let f := absorbCollateralFactorFrame frame seized price out
  { f with locals := f.locals.insert "deltaValue" (.int (absorbCollateralDelta delta seized price out).toNat) }

end Benchmarks.CompoundIII.Comet
