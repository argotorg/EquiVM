import Benchmarks.CompoundIII.Comet.CollateralCheckModel
import Benchmarks.CompoundIII.Comet.MulPrice
import Benchmarks.CompoundIII.Comet.SignedArithmeticWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def absorbPaidWord (old next : UInt256) : UInt256 := UInt256.sub next old

def AbsorbDebtValid (v : CometWithExtendedAssetListImmutables) (old next price : UInt256) : Prop :=
  0 ≤ signedWord next - signedWord old ∧
    signedWord next - signedWord old < (2^255 : Int) ∧
    MulPriceValid (absorbPaidWord old next) price (collateralBaseScale v)

instance (v : CometWithExtendedAssetListImmutables) (old next price : UInt256) :
    Decidable (AbsorbDebtValid v old next price) := by
  unfold AbsorbDebtValid; infer_instance

def absorbDebtValue (v : CometWithExtendedAssetListImmutables) (old next price : UInt256) : UInt256 :=
  mulPriceWord (absorbPaidWord old next) price (collateralBaseScale v)

theorem absorbPaidWord_signed {old next : UInt256} (hn : next.toNat < 2^255)
    (hh : signedWord next - signedWord old < (2^255 : Int)) :
    signedWord (absorbPaidWord old next) = signedWord next - signedWord old := by
  apply signedWord_sub_of_range
  · have hn0 := (signedWord_nonneg_iff next).2 hn
    have ho := (signedWord_bounds old).2
    omega
  · exact hh

def absorbDebtArithmeticBlock : List Stmt :=
  [.internalCall "unsigned256"
      [.inRange (.sint ⟨256, by decide⟩) (.binary .sub (.var "newBalance") (.var "oldBalance"))]
      "basePaidOut",
    .internalCall "mulPrice" [.var "basePaidOut", .var "basePrice",
      .cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩)))] "valueOfBasePaidOut"]

def absorbPaidFrame (frame : Frame) (old next : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "basePaidOut" (.int (absorbPaidWord old next).toNat) }

def absorbDebtFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (old next price : UInt256) : Frame :=
  let paid := absorbPaidFrame frame old next
  { paid with locals := paid.locals.insert "valueOfBasePaidOut" (.int (absorbDebtValue v old next price).toNat) }

end Benchmarks.CompoundIII.Comet
