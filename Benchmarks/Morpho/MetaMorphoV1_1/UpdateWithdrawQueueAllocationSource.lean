import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueuePrefixSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayAllocationSource

/-! Source success and failure for the queue update's two allocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def updateWithdrawQueueCursorFrame (frame : Frame) (ptr : Nat) : Frame :=
  { frame with locals := frame.locals.insert cursorName (uint256Value (UInt256.ofNat ptr)) }

def updateWithdrawQueueSeenFrame (frame : Frame) (curr : Nat) : Frame :=
  let f := updateWithdrawQueueCursorFrame (updateWithdrawQueueCursorFrame frame 128)
    (160 + 32 * curr)
  { f with locals := f.locals.insert "seen" (.array (List.replicate curr (.bool false))) }

def updateWithdrawQueueAllocatedFrame (frame : Frame) (curr len : Nat) : Frame :=
  let f := updateWithdrawQueueCursorFrame (updateWithdrawQueueSeenFrame frame curr)
    (192 + 32 * curr + 32 * len)
  { f with
    locals := f.locals.insert "newWithdrawQueue"
      (.array (List.replicate len (wordBytes32Value ⟨0⟩))) }

theorem updateWithdrawQueueLengthLimitSource {frame : Frame} {evm : State}
    {name : Ident} {n : Nat} (h : frame.locals.get? name = some (.int (Int.ofNat n))) :
    evalExpr? config frame evm (.binary .le (.var name) (.intLit (Int.ofNat solcMaxU64))) =
      .ok (.bool (decide (n ≤ solcMaxU64))) :=
  naturalLeSource (by simp only [evalExpr?, h, EvalResult.ofOption])
    (by simp only [evalExpr?, pure])

theorem updateWithdrawQueueSeenPrefix {frame : Frame} {evm : State} {curr : Nat}
    (hc : frame.contract = contract)
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hbound : curr ≤ solcMaxU64) (hfit : 160 + 32 * curr < 2 ^ 64) (tail : List Stmt) :
    ABlock config evm frame (updateWithdrawQueueAllocation ++ tail)
      (updateWithdrawQueueSeenFrame frame curr)
      (updateWithdrawQueueAllocation.drop 4 ++ tail) := by
  constructor
  intro result htail
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hbound, decide_true] using updateWithdrawQueueLengthLimitSource hcurr
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) ?_
  refine ExecBlock.consNormal (reserveWordArrayReturns (n := curr) (ptr := ⟨128⟩) hc
    (store_get_self _ _ _) ?_ hbound hfit) ?_
  · rw [store_get_ne _ _ (by decide : (cursorName == "currLength") = false)]
    exact hcurr
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  apply evalExpr_newArrayNat (n := curr) ?_ (by simp only [defaultValue?, pure])
  simp only [evalExpr?, store_get_ne _ _ (by decide : (cursorName == "currLength") = false),
    hcurr, EvalResult.ofOption]

theorem updateWithdrawQueueSeenLength {frame : Frame} {curr len : Nat}
    (h : frame.locals.get? "newLength" = some (.int (Int.ofNat len))) :
    (updateWithdrawQueueSeenFrame frame curr).locals.get? "newLength" =
      some (.int (Int.ofNat len)) := by
  simp only [updateWithdrawQueueSeenFrame, updateWithdrawQueueCursorFrame,
    store_get_ne _ _ (by decide : ("seen" == "newLength") = false),
    store_get_ne _ _ (by decide : (cursorName == "newLength") = false), h]

theorem updateWithdrawQueueSeenCursor (frame : Frame) (curr : Nat) :
    (updateWithdrawQueueSeenFrame frame curr).locals.get? cursorName =
      some (uint256Value (UInt256.ofNat (160 + 32 * curr))) := by
  simp only [updateWithdrawQueueSeenFrame, updateWithdrawQueueCursorFrame,
    store_get_ne _ _ (by decide : ("seen" == cursorName) = false), store_get_self]

theorem updateWithdrawQueueAllocationPass {frame : Frame} {evm : State} {curr len : Nat}
    (hc : frame.contract = contract)
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hlen : frame.locals.get? "newLength" = some (.int (Int.ofNat len)))
    (hcb : curr ≤ solcMaxU64) (hnb : len ≤ solcMaxU64)
    (hcfit : 160 + 32 * curr < 2 ^ 64) (hnfit : 192 + 32 * curr + 32 * len < 2 ^ 64)
    (tail : List Stmt) :
    ABlock config evm frame (updateWithdrawQueueAllocation ++ tail)
      (updateWithdrawQueueAllocatedFrame frame curr len) tail := by
  constructor
  intro result htail
  apply (updateWithdrawQueueSeenPrefix hc hcurr hcb hcfit tail).run
  have hl := updateWithdrawQueueSeenLength (curr := curr) hlen
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hnb, decide_true] using updateWithdrawQueueLengthLimitSource hl
  have hp : (UInt256.ofNat (160 + 32 * curr)).toNat = 160 + 32 * curr :=
    UInt256.toNat_ofNat_of_lt (lt_trans hcfit (by decide))
  have ha := reserveWordArrayReturns (frame := updateWithdrawQueueSeenFrame frame curr)
    (evm := evm) hc (updateWithdrawQueueSeenCursor frame curr) hl hnb
    (by rw [hp]; omega : (UInt256.ofNat (160 + 32 * curr)).toNat + 32 + 32 * len < 2 ^ 64)
  rw [hp, show 160 + 32 * curr + 32 + 32 * len = 192 + 32 * curr + 32 * len by omega] at ha
  refine ExecBlock.consNormal ha ?_
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  apply evalExpr_newArrayNat (n := len) ?_ (by simp only [defaultValue?, pure]; native_decide)
  simp only [evalExpr?, store_get_ne _ _ (by decide : (cursorName == "newLength") = false),
    hl, EvalResult.ofOption]

theorem updateWithdrawQueueCurrentLengthReverts {frame : Frame} {evm : State} {curr : Nat}
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hbad : ¬ curr ≤ solcMaxU64) (tail : List Stmt) :
    ExecBlock config frame evm (updateWithdrawQueueAllocation ++ tail) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [hbad, decide_false] using updateWithdrawQueueLengthLimitSource hcurr))

theorem updateWithdrawQueueSeenAllocationReverts {frame : Frame} {evm : State} {curr : Nat}
    (hc : frame.contract = contract)
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hbound : curr ≤ solcMaxU64) (hbad : ¬ 160 + 32 * curr < 2 ^ 64) (tail : List Stmt) :
    ExecBlock config frame evm (updateWithdrawQueueAllocation ++ tail) .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hbound, decide_true] using updateWithdrawQueueLengthLimitSource hcurr
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) ?_
  exact ExecBlock.consRevert (reserveWordArrayReverts (n := curr) (ptr := ⟨128⟩) hc
    (store_get_self _ _ _) (by
      rw [store_get_ne _ _ (by decide : (cursorName == "currLength") = false)]
      exact hcurr) hbound hbad)

theorem updateWithdrawQueueNewLengthReverts {frame : Frame} {evm : State} {curr len : Nat}
    (hc : frame.contract = contract)
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hlen : frame.locals.get? "newLength" = some (.int (Int.ofNat len)))
    (hcb : curr ≤ solcMaxU64) (hcfit : 160 + 32 * curr < 2 ^ 64)
    (hbad : ¬ len ≤ solcMaxU64) (tail : List Stmt) :
    ExecBlock config frame evm (updateWithdrawQueueAllocation ++ tail) .reverted := by
  apply (updateWithdrawQueueSeenPrefix hc hcurr hcb hcfit tail).run
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [hbad, decide_false] using
      updateWithdrawQueueLengthLimitSource (updateWithdrawQueueSeenLength hlen)))

theorem updateWithdrawQueueArrayAllocationReverts {frame : Frame} {evm : State} {curr len : Nat}
    (hc : frame.contract = contract)
    (hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr)))
    (hlen : frame.locals.get? "newLength" = some (.int (Int.ofNat len)))
    (hcb : curr ≤ solcMaxU64) (hnb : len ≤ solcMaxU64) (hcfit : 160 + 32 * curr < 2 ^ 64)
    (hbad : ¬ 192 + 32 * curr + 32 * len < 2 ^ 64) (tail : List Stmt) :
    ExecBlock config frame evm (updateWithdrawQueueAllocation ++ tail) .reverted := by
  apply (updateWithdrawQueueSeenPrefix hc hcurr hcb hcfit tail).run
  have hl := updateWithdrawQueueSeenLength (curr := curr) hlen
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hnb, decide_true] using updateWithdrawQueueLengthLimitSource hl
  exact ExecBlock.consRevert (reserveWordArrayReverts hc (updateWithdrawQueueSeenCursor frame curr)
    hl hnb (by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans hcfit (by decide))]
      omega))

end Benchmarks.Morpho.MetaMorphoV1_1
