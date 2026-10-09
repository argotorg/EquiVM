import Benchmarks.CompoundIII.Comet.DivPriceSource
import Benchmarks.CompoundIII.Comet.CollateralCheckModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def absorbDeltaBalance (v : CometWithExtendedAssetListImmutables) (delta price : UInt256) : UInt256 :=
  divPriceWord delta price (collateralBaseScale v)

def absorbBalanceSum (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256) : UInt256 :=
  old + absorbDeltaBalance v delta price

def AbsorbBalanceValid (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256) : Prop :=
  DivPriceValid delta price (collateralBaseScale v) ∧
    (absorbDeltaBalance v delta price).toNat < 2^255 ∧
    signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat < (2^255 : Int)

instance (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256) :
    Decidable (AbsorbBalanceValid v old delta price) := by
  unfold AbsorbBalanceValid
  infer_instance

def absorbBalanceWord (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256) : UInt256 :=
  let sum := absorbBalanceSum v old delta price
  if sum.toNat < 2^255 then sum else ⟨0⟩

theorem absorbBalanceSum_signed {v old delta price} (hv : AbsorbBalanceValid v old delta price) :
    signedWord (absorbBalanceSum v old delta price) =
      signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat := by
  apply signedWord_add_of_range
  · have ho := (signedWord_bounds old).1
    change -(2^255 : Int) ≤ signedWord old at ho
    simp only [Int.ofNat_eq_natCast]
    omega
  · exact hv.2.2

theorem absorbBalanceWord_lt (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256) :
    (absorbBalanceWord v old delta price).toNat < 2^255 := by
  dsimp only [absorbBalanceWord]
  split_ifs with h
  · exact h
  · decide

def absorbBalanceBlock : List Stmt :=
  [.internalCall "divPrice" [.var "deltaValue", .var "basePrice",
      .cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩)))] "deltaBalance",
    .internalCall "signed256" [.var "deltaBalance"] "__c9",
    .letDecl "newBalance" (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.inRange (.sint ⟨256, by decide⟩) (.binary .add (.var "oldBalance") (.var "__c9"))),
    .ite (.binary .lt (.var "newBalance") (.intLit 0))
      [.assign .localVar ⟨"newBalance", []⟩ (.intLit 0)] []]

def absorbBalanceDivFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (delta price : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "deltaBalance" (.int (absorbDeltaBalance v delta price).toNat) }

def absorbBalanceSignedFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (delta price : UInt256) : Frame :=
  let ready := absorbBalanceDivFrame frame v delta price
  { ready with locals := ready.locals.insert "__c9" (.int (absorbDeltaBalance v delta price).toNat) }

def absorbBalanceFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (old delta price : UInt256) : Frame :=
  let ready := absorbBalanceSignedFrame frame v delta price
  let sum := absorbBalanceSum v old delta price
  let summed := { ready with locals := ready.locals.insert "newBalance" (.int (signedWord sum)) }
  if sum.toNat < 2^255 then summed
  else { summed with locals := summed.locals.insert "newBalance" (.int 0) }

end Benchmarks.CompoundIII.Comet
