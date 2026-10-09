import Benchmarks.CompoundIII.Comet.DivBaseWei
import Benchmarks.CompoundIII.Comet.AccrualWrites
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def trackingSpeed (v : CometWithExtendedAssetListImmutables) (borrow : Bool) : UInt256 :=
  if borrow then v.baseTrackingBorrowSpeed else v.baseTrackingSupplySpeed

def trackingSpeedName (borrow : Bool) : Ident :=
  if borrow then "baseTrackingBorrowSpeed" else "baseTrackingSupplySpeed"

def trackingDivName (borrow : Bool) : Ident := if borrow then "__c4" else "__c2"
def trackingSafeName (borrow : Bool) : Ident := if borrow then "__c5" else "__c3"

def trackingIncrement (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (total elapsed : UInt256) : UInt256 :=
  divBaseWeiWord v (UInt256.mul (trackingSpeed v borrow) elapsed) total

abbrev TrackingIncrementValid (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (total elapsed : UInt256) : Prop :=
  (trackingSpeed v borrow).toNat * elapsed.toNat < UInt256.size ∧
    DivBaseWeiValid v (UInt256.mul (trackingSpeed v borrow) elapsed) total ∧
    (trackingIncrement v borrow total elapsed).toNat < 2^64

abbrev TrackingAccrualValid (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (w0 w1 elapsed : UInt256) : Prop :=
  TrackingIncrementValid v borrow (totalsPrincipalWord w1 borrow) elapsed ∧
    (trackingIndexWord w0 borrow).toNat +
      (trackingIncrement v borrow (totalsPrincipalWord w1 borrow) elapsed).toNat < 2^64

def trackingAccrualBlock (borrow : Bool) : List Stmt :=
  [.internalCall "divBaseWei"
      [.inRange (.uint ⟨256, by decide⟩)
        (.binary .mul (.immutable (trackingSpeedName borrow)) (.var "timeElapsed")),
        .storage ⟨totalsPrincipalName borrow, []⟩] (trackingDivName borrow),
    .internalCall "safe64" [.var (trackingDivName borrow)] (trackingSafeName borrow),
    .assign .storage ⟨trackingIndexName borrow, []⟩
      (.inRange (.uint ⟨64, by decide⟩) (.binary .add
        (.storage ⟨trackingIndexName borrow, []⟩) (.var (trackingSafeName borrow))))]

def trackingAccrualFrame (frame : Frame) (borrow : Bool) (increment : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert (trackingDivName borrow) (.int increment.toNat)).insert
      (trackingSafeName borrow) (.int increment.toNat) }

def trackingAccrualState (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (elapsed : UInt256) : EVM.State :=
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  storeTrackingIndex evm borrow
    (trackingIndexWord w0 borrow +
      trackingIncrement v borrow (totalsPrincipalWord w1 borrow) elapsed)

abbrev TrackingEnabled (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (evm : EVM.State) : Prop :=
  v.baseMinForRewards.toNat ≤
    (totalsPrincipalWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) borrow).toNat

abbrev TrackingBranchValid (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (evm : EVM.State) (elapsed : UInt256) : Prop :=
  if TrackingEnabled v borrow evm then
    TrackingAccrualValid v borrow
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) elapsed else True

def trackingBranchState (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (elapsed : UInt256) : EVM.State :=
  if TrackingEnabled v borrow evm then trackingAccrualState evm v borrow elapsed else evm

def trackingBranchFrame (frame : Frame) (evm : EVM.State)
    (v : CometWithExtendedAssetListImmutables) (borrow : Bool) (elapsed : UInt256) : Frame :=
  if TrackingEnabled v borrow evm then trackingAccrualFrame frame borrow
    (trackingIncrement v borrow
      (totalsPrincipalWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) borrow)
      elapsed)
  else frame

def trackingBranch (borrow : Bool) : Stmt :=
  .ite (.binary .ge (.storage ⟨totalsPrincipalName borrow, []⟩) (.immutable "baseMinForRewards"))
    (trackingAccrualBlock borrow) []

theorem evalTrackingSpeed (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (frame : Frame) (evm : EVM.State) (hi : frame.immutables = immStore v) :
    evalExpr? config frame evm (.immutable (trackingSpeedName borrow)) =
      .ok (.int (trackingSpeed v borrow).toNat) := by
  cases borrow <;>
    simp only [trackingSpeedName, trackingSpeed, Bool.false_eq_true, if_false, if_true,
      evalExpr?, hi, immStore_get_baseTrackingBorrowSpeed,
      immStore_get_baseTrackingSupplySpeed, EvalResult.ofOption] <;> rfl

end Benchmarks.CompoundIII.Comet
