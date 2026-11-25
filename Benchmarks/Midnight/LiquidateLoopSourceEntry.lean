import Benchmarks.Midnight.LiquidateSourceFrame
import Benchmarks.Midnight.HealthSourceFrame

variable {fork : Ethereum.Fork}

/-! The source declarations preceding liquidation's collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateLoopBody : List Stmt :=
  match liquidateTransition.body[14]! with
  | .while _ body => body
  | _ => []

def liquidateLoop : Stmt :=
  .while (.binary .ne (.var "_collateralBitmap") (.intLit 0)) liquidateLoopBody

structure LiquidateAccumulators (frame : Frame)
    (bitmap maxDebt price originalDebt badDebt : UInt256) : Prop where
  bitmap : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat)
  maxDebt : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat)
  price : frame.locals.get? "liquidatedCollatPrice" = some (.int price.toNat)
  originalDebt : frame.locals.get? "originalDebt" = some (.int originalDebt.toNat)
  badDebt : frame.locals.get? "badDebt" = some (.int badDebt.toNat)

theorem LiquidateAccumulators.insert {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (name : Ident) (value : Value)
    (hn : name ∉ ["_collateralBitmap", "maxDebt", "liquidatedCollatPrice", "originalDebt", "badDebt"]) :
    LiquidateAccumulators { frame with locals := frame.locals.insert name value }
      bitmap maxDebt price originalDebt badDebt := by
  rcases h with ⟨hb, hm, hp, ho, hd⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

def liquidateLoopInitialFrame (frame : Frame) (debtWord : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal (wordLocal frame
    "maxDebt" ⟨0⟩) "liquidatedCollatPrice" ⟨0⟩) "originalDebt" (low128 debtWord))
    "badDebt" (low128 debtWord)) "_collateralBitmap" (UInt256.shiftRight debtWord ⟨128⟩)

theorem liquidateLoopInitialFrame_accumulators (frame : Frame) (debtWord : UInt256) :
    LiquidateAccumulators (liquidateLoopInitialFrame frame debtWord)
      (UInt256.shiftRight debtWord ⟨128⟩) ⟨0⟩ ⟨0⟩ (low128 debtWord) (low128 debtWord) := by
  constructor <;> simp only [liquidateLoopInitialFrame, wordLocal,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> simp

theorem liquidateLoopInitialFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode debtWord : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateLoopInitialFrame frame debtWord)
      m id index seized repaid borrower mode receiver callback data := by
  exact ((((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert
    _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLoopSourceEntry {frame : Frame} {evm : State} {id borrower : UInt256}
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType)) :
    ExecBlock fork config frame evm (liquidateTransition.body.drop 9 |>.take 5)
      (.ok (liquidateLoopInitialFrame frame (healthPositionWord evm id borrower)) evm) := by
  let f1 := wordLocal frame "maxDebt" ⟨0⟩
  let f2 := wordLocal f1 "liquidatedCollatPrice" ⟨0⟩
  let f3 := wordLocal f2 "originalDebt" (low128 (healthPositionWord evm id borrower))
  let f4 := wordLocal f3 "badDebt" (low128 (healthPositionWord evm id borrower))
  have hp2 : f2.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType) := by
    simpa [f2, f1, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
  have hp4 : f4.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType) := by
    simpa [f4, f3, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp2
  refine ExecBlock.consNormal (stele' := f1) (ExecStmt.letDecl (by simp [evalExpr?, pure]))
    (ExecBlock.consNormal (stele' := f2) (ExecStmt.letDecl (by simp [evalExpr?, pure]))
    (ExecBlock.consNormal (stele' := f3) (ExecStmt.letDecl (evalHealthDebt hcanon hp2))
    (ExecBlock.consNormal (stele' := f4) (ExecStmt.letDecl ?_)
    (ExecBlock.consNormal (ExecStmt.letDecl (evalHealthBitmap hcanon hp4)) (ExecBlock.nil ..)))))
  simp only [evalExpr?, f3, wordLocal_get, EvalResult.ofOption]

end Benchmarks.Midnight
