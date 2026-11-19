import Benchmarks.Midnight.CollateralValidationLoop
import Benchmarks.Midnight.TouchMarketHeaderTrace

/-! The complete validation prefix of a previously uninitialized market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def touchMarketPreviousFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "previousCollateralToken" (.address (AccountAddress.ofNat 0)) }

def touchMarketLoopFrame (frame : Frame) : Frame :=
  { (touchMarketPreviousFrame frame) with locals := (touchMarketPreviousFrame frame).locals.insert "i" (.int 0) }

def collateralLoopInit : List Stmt :=
  [.letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

theorem touchMarketValidation_shape : touchMarketInitBody.drop 5 =
    [.letDecl "previousCollateralToken" (some (.elem .address))
      (.cast (.intLit 0) (.elem .address)),
     .for collateralLoopInit collateralLoopCondition collateralLoopPost collateralLoopBody] ++
       touchMarketInitBody.drop 7 := rfl

theorem touchMarketLoopFrame_inv {frame : Frame} {m : MarketData}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hl : frame.locals.get? "isLltvEnabled" = none)
    (hcu : frame.locals.get? "isLiquidationCursorEnabled" = none) :
    CollateralSourceFrame (touchMarketLoopFrame frame) m 0 (AccountAddress.ofNat 0) := by
  constructor
  · exact hc
  · simpa [touchMarketLoopFrame, touchMarketPreviousFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hm
  · exact store_get_self _ _ _
  · simp [touchMarketLoopFrame, touchMarketPreviousFrame, Std.HashMap.getElem_insert]
  · simpa [touchMarketLoopFrame, touchMarketPreviousFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl
  · simpa [touchMarketLoopFrame, touchMarketPreviousFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hcu

theorem touchMarketLoopFrame_preserved (frame : Frame) :
    CollateralLocalsPreserved frame (touchMarketLoopFrame frame) :=
  (collateralInsert_preserved frame "previousCollateralToken" (.address (AccountAddress.ofNat 0))
    (by decide)).trans (collateralInsert_preserved _ "i" (.int 0) (by decide))

theorem touchMarketLoopInitSource (frame : Frame) (evm : EVM.State) :
    ExecBlock config (touchMarketPreviousFrame frame) evm collateralLoopInit
      (.ok (touchMarketLoopFrame frame) evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem touchMarketPreviousPrefix {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hs : TouchMarketHeaderSafe evm.executionEnv m) :
    ABlock config evm frame touchMarketInitBody (touchMarketPreviousFrame frame)
      (touchMarketInitBody.drop 6) := by
  apply (touchMarketHeaderSource hm hs).letStep
  simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption]
  rfl

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketValidation {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {k C : Nat}
    {R : List UInt256} {frame : Frame} (m : MarketData)
    (hstack : R.length + 15 ≤ 1024) (hm : MarketStored mem ptr arrayPtr root m)
    (hc : frame.contract = contract)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hl : frame.locals.get? "isLltvEnabled" = none)
    (hcu : frame.locals.get? "isLiquidationCursorEnabled" = none)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧ ExecBlock config frame evm touchMarketInitBody .reverted) ∨
    (∃ previous frame' mem' aw' k' C',
      ABlock config evm frame touchMarketInitBody frame' (touchMarketInitBody.drop 7) ∧
      CollateralSourceFrame frame' m m.collaterals.length previous ∧
      CollateralLocalsPreserved frame frame' ∧ MemoryPrefix mem mem' root.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      RD midnightBytecode evm.executionEnv g s0 ⟨21130⟩
        (arrayPtr :: UInt256.ofNat previous.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
          UInt256.ofNat m.collaterals.length :: R) mem' aw' rdata evm.accountMap k' C') := by
  rcases midnightTouchMarketHeader m (by omega) hm rd with ⟨hbad, hr⟩ | ⟨hs, aw1, k1, C1, rd1⟩
  · exact Or.inl ⟨hr, touchMarketHeaderRevert hmarket hbad⟩
  · have hf := touchMarketLoopFrame_inv hc hmarket hl hcu
    rcases midnightCollateralValidationLoop m (AccountAddress.ofNat 0) 0 m.collaterals.length
        (by omega) hstack hm hf rd1 with
      ⟨hr, hloop⟩ | ⟨p, f, mm, aw2, k2, C2, hf2, hlocals, hmem, hfree, hloop, rd2⟩
    · refine Or.inl ⟨hr, (touchMarketPreviousPrefix hmarket hs).run ?_⟩
      exact ExecBlock.consRevert (ExecStmt.for (touchMarketLoopInitSource frame evm) hloop)
    · right
      refine ⟨p, f, mm, aw2, k2, C2, ?_, hf2,
        (touchMarketLoopFrame_preserved frame).trans hlocals, hmem, hfree, rd2⟩
      exact sourceNormalStep (touchMarketPreviousPrefix hmarket hs)
        (ExecStmt.for (touchMarketLoopInitSource frame evm) hloop)

end Benchmarks.Midnight
