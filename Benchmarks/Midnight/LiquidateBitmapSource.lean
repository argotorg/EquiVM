import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.PositionBitmapStorage

variable {fork : Ethereum.Fork}

/-! Source guard and optional bitmap clear after seizing collateral. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateClearGuard : Expr :=
  .binary .and (.binary .eq (.var "newCollateral") (.intLit 0))
    (.binary .gt (.var "seizedAssets") (.intLit 0))

def liquidateClearBody : List Stmt :=
  match liquidateAmountsBody[9]! with
  | .ite _ yes _ => yes
  | _ => []

theorem evalLiquidateClearGuard {frame : Frame} {evm : State} {seized value : UInt256}
    (hn : frame.locals.get? "newCollateral" = some (.int value.toNat))
    (ha : frame.locals.get? "seizedAssets" = some (.int seized.toNat)) :
    evalExpr? config frame evm liquidateClearGuard =
      .ok (.bool (decide (value = ⟨0⟩ ∧ seized ≠ ⟨0⟩))) := by
  have hz : value.toNat = 0 ↔ value = ⟨0⟩ := by
    constructor
    · intro h; apply u256_inj; exact h
    · rintro rfl; rfl
  have hs : 0 < seized.toNat ↔ seized ≠ ⟨0⟩ := by
    constructor
    · intro h he; subst seized; exact (by decide : ¬ 0 < (⟨0⟩ : UInt256).toNat) h
    · intro h; by_contra hn; apply h; apply u256_inj; change seized.toNat = 0; omega
  simp only [liquidateClearGuard, evalExpr?, hn, ha, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
    Int.natCast_eq_zero, hz, Int.natCast_pos, hs]
  split <;> simp_all

theorem liquidateBitmapSource {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hcanon : borrower.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hp : evm.executionEnv.perm = true) :
    ExecBlock fork config frame evm liquidateClearBody
      (.ok (wordLocal frame "__c28" (bitmapClear (positionBitmapWord evm id borrower) index))
        (storeHigh128 evm (positionSlot id borrower + ⟨2⟩)
          (bitmapClear (positionBitmapWord evm id borrower) index))) := by
  let bitmap := bitmapClear (positionBitmapWord evm id borrower) index
  have hf1 := hf.insert "__c28" (.int bitmap.toNat) (by decide)
  refine ExecBlock.consNormal (callBitmapClear (bitmap := positionBitmapWord evm id borrower)
    (bit := index) hf.contract ?_ (by omega)) ?_
  · simp only [evalExprs?, evalHealthBitmap hcanon hf.position, evalExpr?, hf.index,
      EvalResult.ofOption, EvalResult.bind, bind, pure, positionBitmapWord]
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hp)
    (evalWordLocal (wordLocal_get ..)) (assignPositionBitmap bitmap hcanon hf1.position))
      ExecBlock.nil

end Benchmarks.Midnight
