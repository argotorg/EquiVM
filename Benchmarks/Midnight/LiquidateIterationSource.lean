import Benchmarks.Midnight.LiquidateLoopArithmeticSource
import Benchmarks.Midnight.LiquidatePriceChoice

variable {fork : Ethereum.Fork}

/-! Price selection followed by the arithmetic tail of a liquidation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidatePriceFrame_get (frame : Frame) (index target price : UInt256) (name : Ident)
    (hn : "liquidatedCollatPrice" ≠ name) :
    (liquidatePriceFrame frame index target price).locals.get? name = frame.locals.get? name := by
  by_cases he : index = target
  · simp only [liquidatePriceFrame, if_pos he, wordLocal_get_ne _ _ _ _ hn]
  · simp only [liquidatePriceFrame, if_neg he]

set_option maxRecDepth 2000000 in
theorem liquidateIterationSource {frame : Frame} {evm : State} {m : MarketData}
    {id target seized repaid borrower mode bitmap maxDebt savedPrice originalDebt badDebt
      index price : UInt256} {receiver callback : AccountAddress} {data : ByteArray}
    {c : CollateralData}
    (hf : LiquidateSourceFrame frame m id target seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt savedPrice originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value))
    (hp : frame.locals.get? "price" = some (.int price.toNat)) :
    let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      (positionSlot id borrower + ⟨3⟩) index
    (¬ LiquidateLoopArithmeticSafe collateral price c.lltv c.liquidationCursor maxDebt ∧
      ExecBlock fork config frame evm (liquidateLoopBody.drop 3) .reverted) ∨
    (LiquidateLoopArithmeticSafe collateral price c.lltv c.liquidationCursor maxDebt ∧
      ∃ frame', ExecBlock fork config frame evm (liquidateLoopBody.drop 3) (.ok frame' evm) ∧
        LiquidateSourceFrame frame' m id target seized repaid borrower mode receiver callback data ∧
        LiquidateAccumulators frame' (bitmapClear bitmap index)
          (maxDebt + healthCollateralCapacity collateral price c.lltv)
          (if index = target then price else savedPrice) originalDebt
          (zeroFloorSubWord badDebt
            (liquidateRecoveryValue collateral price c.lltv c.liquidationCursor))) := by
  dsimp only
  let fp := liquidatePriceFrame frame index target price
  have hs := liquidatePriceSource (fork := fork) (evm := evm) hi hf.index hp ha.price
  have hf' : LiquidateSourceFrame fp m id target seized repaid borrower mode receiver callback data :=
    liquidatePriceFrame_arguments hf
  have ha' : LiquidateAccumulators fp bitmap maxDebt
      (if index = target then price else savedPrice) originalDebt badDebt :=
    liquidatePriceFrame_accumulators ha
  have hi' : fp.locals.get? "i" = some (.int index.toNat) := by
    rw [liquidatePriceFrame_get _ _ _ _ _ (by decide)]
    exact hi
  have hc' : fp.locals.get? "_collateralParam" = some (Model.collateralValue c.value) := by
    rw [liquidatePriceFrame_get _ _ _ _ _ (by decide)]
    exact hc
  have hp' : fp.locals.get? "price" = some (.int price.toNat) := by
    rw [liquidatePriceFrame_get _ _ _ _ _ (by decide)]
    exact hp
  rcases liquidateLoopArithmeticSource (evm := evm) hf'.contract hcanon hf'.position
      hi' hindex hc' hp' ha'.maxDebt ha'.badDebt ha'.bitmap with
    ⟨hbad, hrev⟩ | ⟨hsafe, hmath⟩
  · exact Or.inl ⟨hbad, ExecBlock.consNormal hs hrev⟩
  · exact Or.inr ⟨hsafe, _, ExecBlock.consNormal hs hmath,
      liquidateArithmeticFrame_arguments hf', liquidateArithmeticFrame_accumulators ha'⟩

end Benchmarks.Midnight
