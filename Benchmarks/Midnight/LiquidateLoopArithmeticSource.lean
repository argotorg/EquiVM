import Benchmarks.Midnight.LiquidateLoopSourceFinish

variable {fork : Ethereum.Fork}

/-! Source semantics and retained locals for the arithmetic part of a liquidation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateArithmeticFrame (frame : Frame)
    (collateral price lltv cursor maxDebt badDebt bitmap index : UInt256) : Frame :=
  liquidateFinishFrame
    (liquidateRecoveryFrame (liquidateValueFrame frame collateral price lltv maxDebt)
      collateral price lltv cursor)
    badDebt (liquidateRecoveryValue collateral price lltv cursor) bitmap index

theorem liquidateArithmeticFrame_arguments {frame : Frame} {m : MarketData}
    {id target seized repaid borrower mode collateral price lltv cursor maxDebt badDebt
      bitmap index : UInt256} {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id target seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame
      (liquidateArithmeticFrame frame collateral price lltv cursor maxDebt badDebt bitmap index)
      m id target seized repaid borrower mode receiver callback data := by
  exact ((((((((((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert
    _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert
    _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateArithmeticFrame_accumulators {frame : Frame}
    {collateral price lltv cursor maxDebt badDebt bitmap index savedPrice originalDebt : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt savedPrice originalDebt badDebt) :
    LiquidateAccumulators
      (liquidateArithmeticFrame frame collateral price lltv cursor maxDebt badDebt bitmap index)
      (bitmapClear bitmap index) (maxDebt + healthCollateralCapacity collateral price lltv)
      savedPrice originalDebt (zeroFloorSubWord badDebt
        (liquidateRecoveryValue collateral price lltv cursor)) := by
  rcases h with ⟨hb, hm, hp, ho, hd⟩
  constructor <;> simp only [liquidateArithmeticFrame, liquidateFinishFrame,
    liquidateRecoveryFrame, liquidateValueFrame, wordLocal,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
    simp_all

theorem liquidateLoopArithmeticSource {frame : Frame} {evm : State}
    {id borrower index price maxDebt badDebt bitmap : UInt256} {c : CollateralData}
    (hcontract : frame.contract = contract) (hcanon : borrower.toNat < EVM.addressModulus)
    (hpos : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value))
    (hp : frame.locals.get? "price" = some (.int price.toNat))
    (hm : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hb : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat)) :
    let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      (positionSlot id borrower + ⟨3⟩) index
    (¬ LiquidateLoopArithmeticSafe collateral price c.lltv c.liquidationCursor maxDebt ∧
      ExecBlock fork config frame evm (liquidateLoopBody.drop 4) .reverted) ∨
    (LiquidateLoopArithmeticSafe collateral price c.lltv c.liquidationCursor maxDebt ∧
      ExecBlock fork config frame evm (liquidateLoopBody.drop 4)
        (.ok (liquidateArithmeticFrame frame collateral price c.lltv c.liquidationCursor
          maxDebt badDebt bitmap index) evm)) := by
  dsimp only
  let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
    (positionSlot id borrower + ⟨3⟩) index
  let fv := liquidateValueFrame frame collateral price c.lltv maxDebt
  let fr := liquidateRecoveryFrame fv collateral price c.lltv c.liquidationCursor
  have hv := liquidateCollateralValueSource (fork := fork) (evm := evm) hcontract hcanon hpos hi hindex hc hp hm
    (liquidateLoopBody.drop 8)
  have hsplit1 : (liquidateLoopBody.drop 4).take 4 ++ liquidateLoopBody.drop 8 =
      liquidateLoopBody.drop 4 := by
    simpa only [List.drop_drop] using List.take_append_drop 4 (liquidateLoopBody.drop 4)
  rw [hsplit1] at hv
  rcases hv with ⟨hbad, hrev⟩ | ⟨hs1, ha1⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hrev⟩
  have hcv : fv.locals.get? "_collateralParam" = some (Model.collateralValue c.value) := by
    simpa only [fv, liquidateValueFrame, wordLocal_get_ne _ _ _ _
      (show "maxDebt" ≠ "_collateralParam" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "_collateralParam" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "_collateralParam" from by decide),
      wordLocal_get_ne _ _ _ _ (show "_collateral" ≠ "_collateralParam" from by decide)] using hc
  have hpv : fv.locals.get? "price" = some (.int price.toNat) := by
    simpa only [fv, liquidateValueFrame, wordLocal_get_ne _ _ _ _
      (show "maxDebt" ≠ "price" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "price" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "price" from by decide),
      wordLocal_get_ne _ _ _ _ (show "_collateral" ≠ "price" from by decide)] using hp
  have hcolv : fv.locals.get? "_collateral" = some (.int collateral.toNat) := by
    simp only [fv, liquidateValueFrame, wordLocal_get_ne _ _ _ _
      (show "maxDebt" ≠ "_collateral" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "_collateral" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "_collateral" from by decide), wordLocal_get]
  have hr := liquidateRecoverySource (fork := fork) (frame := fv) (evm := evm) (c := c)
      (collateral := collateral) (price := price)
      hcontract hcv hcolv hpv (liquidateLoopBody.drop 11)
  have hsplit2 : (liquidateLoopBody.drop 8).take 3 ++ liquidateLoopBody.drop 11 =
      liquidateLoopBody.drop 8 := by
    simpa only [List.drop_drop] using List.take_append_drop 3 (liquidateLoopBody.drop 8)
  rw [hsplit2] at hr
  rcases hr with ⟨hbad, hrev⟩ | ⟨hs2, ha2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2, ha1.run hrev⟩
  have hdr : fr.locals.get? "badDebt" = some (.int badDebt.toNat) := by
    simpa only [fr, fv, liquidateRecoveryFrame, liquidateValueFrame,
      wordLocal_get_ne _ _ _ _ (show "__c8" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c7" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c6" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "badDebt" from by decide),
      wordLocal_get_ne _ _ _ _ (show "_collateral" ≠ "badDebt" from by decide)] using hd
  have hbr : fr.locals.get? "_collateralBitmap" = some (.int bitmap.toNat) := by
    simpa only [fr, fv, liquidateRecoveryFrame, liquidateValueFrame,
      wordLocal_get_ne _ _ _ _ (show "__c8" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c7" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c6" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "_collateralBitmap" from by decide),
      wordLocal_get_ne _ _ _ _ (show "_collateral" ≠ "_collateralBitmap" from by decide)] using hb
  have hir : fr.locals.get? "i" = some (.int index.toNat) := by
    simpa only [fr, fv, liquidateRecoveryFrame, liquidateValueFrame,
      wordLocal_get_ne _ _ _ _ (show "__c8" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c7" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c6" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c5" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "__c4" ≠ "i" from by decide),
      wordLocal_get_ne _ _ _ _ (show "_collateral" ≠ "i" from by decide)] using hi
  have hcr : fr.locals.get? "__c8" =
      some (.int (liquidateRecoveryValue collateral price c.lltv c.liquidationCursor).toNat) :=
    wordLocal_get (wordLocal (wordLocal fv "__c6" (liquidateRoundedValue collateral price))
      "__c7" (maxLif c.lltv c.liquidationCursor)) "__c8"
      (liquidateRecoveryValue collateral price c.lltv c.liquidationCursor)
  have hfc : fr.contract = contract := by
    simp only [fr, fv, liquidateRecoveryFrame, liquidateValueFrame, wordLocal]
    exact hcontract
  have hfinish := @liquidateLoopSourceFinish fork fr evm badDebt
    (liquidateRecoveryValue collateral price c.lltv c.liquidationCursor) bitmap index
    hfc hdr hcr hbr hir (hindex.trans (by decide))
  have hrest := ha2.run hfinish
  have hfull := ha1.run hrest
  exact Or.inr ⟨⟨hs1, hs2⟩, hfull⟩

end Benchmarks.Midnight
