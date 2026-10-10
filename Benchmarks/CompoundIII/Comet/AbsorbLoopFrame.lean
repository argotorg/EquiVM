import Benchmarks.CompoundIII.Comet.AbsorbLoopModel
import Benchmarks.CompoundIII.Comet.CollateralLoopFrame
import Benchmarks.CompoundIII.Comet.UserBasicData

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure AbsorbLoopFrame (v : CometWithExtendedAssetListImmutables)
    (absorber account : AccountAddress) (basic : UserBasicData) (old price : UInt256)
    (i : Nat) (delta : UInt256) (frame : Frame) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  absorber : frame.locals.get? "absorber" = some (.address absorber)
  account : frame.locals.get? "account" = some (.address account)
  accountUser : frame.locals.get? "accountUser" = some (userBasicValue basic)
  oldBalance : frame.locals.get? "oldBalance" = some (.int (signedWord old))
  oldPrincipal : frame.locals.get? "oldPrincipal" = some (.int (signed104 basic.principal))
  basePrice : frame.locals.get? "basePrice" = some (.int price.toNat)
  assets : frame.locals.get? "assetsIn" = some (.int basic.assets.toNat)
  reserved : frame.locals.get? "_reserved" = some (.int basic.reserved.toNat)
  index : frame.locals.get? "i" = some (.int i)
  delta : frame.locals.get? "deltaValue" = some (.int delta.toNat)
  userCollateral : frame.locals.get? "userCollateral" = none
  totalsCollateral : frame.locals.get? "totalsCollateral" = none
  userBasic : frame.locals.get? "userBasic" = none
  supplyBase : frame.locals.get? "totalSupplyBase" = none
  borrowBase : frame.locals.get? "totalBorrowBase" = none
  supplyIndex : frame.locals.get? "baseSupplyIndex" = none

theorem AbsorbLoopFrame.member {v absorber account basic old price i delta frame}
    (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) (member : Bool) :
    AbsorbLoopFrame v absorber account basic old price i delta
      (collateralMemberFrame frame member) := by
  cases hf
  constructor <;> simp_all only [collateralMemberFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

theorem AbsorbLoopFrame.next {v absorber account basic old price i delta frame}
    (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) :
    AbsorbLoopFrame v absorber account basic old price (i + 1) delta
      (collateralNextFrame frame i) := by
  cases hf
  constructor <;> simp_all only [collateralNextFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

theorem AbsorbLoopFrame.asset {v absorber account basic old price i delta frame}
    (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) (d : AbsorbAssetData) :
    AbsorbLoopFrame v absorber account basic old price i (d.delta delta)
      (absorbAssetFrame frame delta d) := by
  cases hf
  constructor <;> simp_all only [absorbAssetFrame, absorbAssetInfoFrame, absorbAfterAssetFrame,
    absorbAssetSeizedFrame, absorbAssetNameFrame, absorbCollateralPriceFrame,
    absorbCollateralMathFrame, absorbCollateralFactorFrame, absorbCollateralValueFrame,
    AbsorbAssetData.delta, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

end Benchmarks.CompoundIII.Comet
