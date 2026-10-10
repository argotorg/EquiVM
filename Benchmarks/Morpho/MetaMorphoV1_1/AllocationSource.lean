import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.MemoryRoutines

/-! Source proofs for explicit compiler allocation, without a memory-size assumption. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem allocateFunction_lookup :
    lookupCallable? contract allocateFunction.name = some allocateFunction.toCallable := by
  rfl

def roundedSize (size : UInt256) : UInt256 :=
  UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)

def nextCursor (ptr size : UInt256) : UInt256 := ptr + roundedSize size

def allocationFits (ptr size : UInt256) : Prop :=
  (nextCursor ptr size).toNat < 2 ^ 64 ∧ ptr.toNat ≤ (nextCursor ptr size).toNat

instance (ptr size : UInt256) : Decidable (allocationFits ptr size) :=
  inferInstanceAs (Decidable (_ ∧ _))

def allocationFrame (frame : Frame) (ptr size : UInt256) : Frame :=
  { frame with
    locals := ((∅ : Store).insert sizeName (uint256Value size)).insert
      cursorName (uint256Value ptr) }

def allocationResultFrame (frame : Frame) (ptr size : UInt256) : Frame :=
  { allocationFrame frame ptr size with
    locals := (allocationFrame frame ptr size).locals.insert nextName
      (uint256Value (nextCursor ptr size)) }

theorem roundedSize_toNat (size : UInt256) :
    (roundedSize size).toNat = ((size.toNat + 31) % UInt256.size) / 32 * 32 := by
  rw [roundedSize, longDataCutoff_toNat, uadd_toNat]
  rfl

theorem nextCursor_toNat (ptr size : UInt256) :
    (nextCursor ptr size).toNat =
      (ptr.toNat + ((size.toNat + 31) % UInt256.size) / 32 * 32) % UInt256.size := by
  rw [nextCursor, uadd_toNat, roundedSize_toNat]

theorem allocationFrame_cursor (frame : Frame) (ptr size : UInt256) :
    (allocationFrame frame ptr size).locals.get? cursorName = some (uint256Value ptr) := by
  exact store_get_self _ _ _

theorem allocationFrame_size (frame : Frame) (ptr size : UInt256) :
    (allocationFrame frame ptr size).locals.get? sizeName = some (uint256Value size) := by
  rw [allocationFrame, store_get_ne _ _ (by decide : (cursorName == sizeName) = false)]
  exact store_get_self _ _ _

theorem roundedSizeSource (cfg : Config) (frame : Frame) (evm : State) (ptr size : UInt256) :
    evalExpr? cfg (allocationFrame frame ptr size) evm roundedSizeExpr =
      .ok (uint256Value (roundedSize size)) := by
  simp only [roundedSizeExpr, evalExpr?, allocationFrame_size, EvalResult.ofOption,
    uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?]
  rw [roundedSize_toNat]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul,
    Int.natCast_ediv, Int.natCast_emod]
  rfl

theorem nextCursorSource (cfg : Config) (frame : Frame) (evm : State) (ptr size : UInt256) :
    evalExpr? cfg (allocationFrame frame ptr size) evm nextCursorExpr =
      .ok (uint256Value (nextCursor ptr size)) := by
  rw [nextCursorExpr, evalExpr_binary_nonshort (by decide) (by decide)]
  rw [naturalAddSource (a := ptr.toNat) (b := (roundedSize size).toNat) (by
    simp only [evalExpr?, allocationFrame_cursor, EvalResult.ofOption, uint256Value])
    (roundedSizeSource cfg frame evm ptr size)]
  simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, uint256Value,
    nextCursor, uadd_toNat, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_emod]
  rfl

-- LIBRARY CANDIDATE: natural-number comparison in an arbitrary source frame.
theorem naturalLtSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .lt lhs rhs) = .ok (.bool (decide (a < b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Nat.cast_lt]

-- LIBRARY CANDIDATE: successful Boolean operands evaluate under short-circuit conjunction.
theorem boolAndSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .and lhs rhs) = .ok (.bool (a && b)) := by
  cases a <;> simp only [evalExpr?, ha, hb, bind, EvalResult.bind, pure,
    Bool.false_and, Bool.true_and]

theorem allocationCheckSource (cfg : Config) (frame : Frame) (evm : State)
    (ptr size : UInt256) :
    evalExpr? cfg (allocationResultFrame frame ptr size) evm allocationCheckExpr =
      .ok (.bool (decide (allocationFits ptr size))) := by
  have hn : evalExpr? cfg (allocationResultFrame frame ptr size) evm (.var nextName) =
      .ok (uint256Value (nextCursor ptr size)) := by
    simp only [evalExpr?, allocationResultFrame, store_get_self, EvalResult.ofOption]
  have hp : evalExpr? cfg (allocationResultFrame frame ptr size) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
    simp only [evalExpr?, allocationResultFrame,
      store_get_ne _ _ (by decide : (nextName == cursorName) = false),
      allocationFrame_cursor, EvalResult.ofOption]
  have hlimit : evalExpr? cfg (allocationResultFrame frame ptr size) evm
      (.intLit (Int.ofNat (2 ^ 64))) = .ok (.int (Int.ofNat (2 ^ 64))) := by
    simp only [evalExpr?, pure]
  simpa only [allocationCheckExpr, allocationFits, Bool.decide_and] using
    boolAndSource (naturalLtSource hn hlimit) (naturalLeSource hp hn)

theorem allocateBodyReturns (cfg : Config) (frame : Frame) (evm : State)
    (ptr size : UInt256) (hfit : allocationFits ptr size) :
    ExecFuncBody cfg (allocationFrame frame ptr size) evm allocateFunction.body
      (.returned (allocationResultFrame frame ptr size) evm
        (some [uint256Value (nextCursor ptr size)])) := by
  apply ExecFuncBody.execBlockRet
  apply (ABlock.start.letStep (nextCursorSource cfg frame evm ptr size)).run
  apply (ABlock.start.requireStep (by
    simpa only [hfit, decide_true] using allocationCheckSource cfg frame evm ptr size)).returns
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]

theorem allocateBodyReverts (cfg : Config) (frame : Frame) (evm : State)
    (ptr size : UInt256) (hfit : ¬ allocationFits ptr size) :
    ExecFuncBody cfg (allocationFrame frame ptr size) evm allocateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.letStep (nextCursorSource cfg frame evm ptr size)).run
  exact ABlock.start.requireRevert (by
    simpa only [hfit, decide_false] using allocationCheckSource cfg frame evm ptr size)

theorem allocateCallReturns {cfg : Config} {frame : Frame} {evm : State}
    {ptrExpr sizeExpr : Expr} {ptr size : UInt256} (retVar : Ident)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hptr : evalExpr? cfg frame evm ptrExpr = .ok (uint256Value ptr))
    (hsize : evalExpr? cfg frame evm sizeExpr = .ok (uint256Value size))
    (hfit : allocationFits ptr size) :
    ExecStmt cfg frame evm (.internalCall allocateFunction.name [ptrExpr, sizeExpr] retVar)
      (.ok { frame with
        locals := frame.locals.insert retVar (uint256Value (nextCursor ptr size)) } evm) := by
  exact internalCallFunctionReturn (callee := allocateFunction)
    (argVals := [uint256Value ptr, uint256Value size])
    (by simp only [evalExprs?, hptr, hsize, bind, EvalResult.bind, pure])
    hlookup rfl (allocateBodyReturns cfg frame evm ptr size hfit)

theorem allocateCallReverts {cfg : Config} {frame : Frame} {evm : State}
    {ptrExpr sizeExpr : Expr} {ptr size : UInt256} (retVar : Ident)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hptr : evalExpr? cfg frame evm ptrExpr = .ok (uint256Value ptr))
    (hsize : evalExpr? cfg frame evm sizeExpr = .ok (uint256Value size))
    (hfit : ¬ allocationFits ptr size) :
    ExecStmt cfg frame evm (.internalCall allocateFunction.name [ptrExpr, sizeExpr] retVar)
      .reverted := by
  exact internalCallFunctionRevert (callee := allocateFunction)
    (argVals := [uint256Value ptr, uint256Value size])
    (by simp only [evalExprs?, hptr, hsize, bind, EvalResult.bind, pure])
    hlookup rfl (allocateBodyReverts cfg frame evm ptr size hfit)

def allocationGuardWord (ptr size : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.gt (nextCursor ptr size)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩))
    (UInt256.lt (nextCursor ptr size) ptr)

theorem allocationGuard_eq_zero_iff (ptr size : UInt256) :
    allocationGuardWord ptr size = ⟨0⟩ ↔ allocationFits ptr size := by
  constructor
  · intro hguard
    have hupper := ugt_eq_zero_to_le (u256_lor_eq_zero_left hguard)
    have hwrap := ult_eq_zero_to_le (u256_lor_eq_zero_right hguard)
    change (nextCursor ptr size).toNat ≤ 2 ^ 64 - 1 at hupper
    exact ⟨by omega, hwrap⟩
  · rintro ⟨hupper, hwrap⟩
    unfold allocationGuardWord
    rw [ugt_zero (by change (nextCursor ptr size).toNat ≤ 2 ^ 64 - 1; omega),
      ult_zero hwrap]
    rfl

theorem allocationFits_iff_sum_lt (ptr size : UInt256) :
    allocationFits ptr size ↔ ptr.toNat + (roundedSize size).toNat < 2 ^ 64 := by
  constructor
  · rintro ⟨hupper, hwrap⟩
    have hsum : ptr.toNat + (roundedSize size).toNat < UInt256.size := by
      by_contra h
      have hover := u256_add_overflow_lt ptr (roundedSize size) (Nat.le_of_not_lt h)
      have hzero := ult_zero hwrap
      rw [nextCursor, hover] at hzero
      exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hzero
    rwa [nextCursor, uadd_toNat, Nat.mod_eq_of_lt hsum] at hupper
  · intro hfit
    exact (allocationGuard_eq_zero_iff ptr size).mp
      (allocationGuard ptr (roundedSize size) hfit)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
