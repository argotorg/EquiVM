import Examples.UniswapV2Pair.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

/-! # Shared pure math source helpers -/

abbrev sqrtFunctionYValue (y : UInt256) : Value :=
  uniswapUint256Value y

abbrev sqrtFunctionCallStore (y : UInt256) : Store :=
  (∅ : Store).insert "y" (sqrtFunctionYValue y)

abbrev sqrtFunctionSmallResultValue (y : UInt256) : Value :=
  if y.toNat = 0 then .int 0 else .int 1

theorem sqrtFunctionCallStore_y (y : UInt256) :
    (sqrtFunctionCallStore y).get? "y" = some (sqrtFunctionYValue y) := by
  rw [sqrtFunctionCallStore, store_get_self]

theorem evalExpr_sqrtFunction_y (evm : EVM.State) (y : UInt256) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.var "y") = .ok (sqrtFunctionYValue y) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [sqrtFunctionCallStore_y]

theorem evalExpr_sqrtFunction_outer_false (evm : EVM.State) (y : UInt256)
    (hsmall : y.toNat ≤ 3) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.binary .gt (.var "y") (.intLit 3)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_sqrtFunction_y evm y, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_sqrtFunction_inner_true (evm : EVM.State) (y : UInt256)
    (hy : y.toNat ≠ 0) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.binary .ne (.var "y") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_sqrtFunction_y evm y, EvalResult.bind, bind]
  simp [evalBinaryOp?, sqrtFunctionYValue, uniswapUint256Value, uint256Value, hy]

theorem evalExpr_sqrtFunction_inner_false (evm : EVM.State) (y : UInt256)
    (hy : y.toNat = 0) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.binary .ne (.var "y") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_sqrtFunction_y evm y, EvalResult.bind, bind]
  simp [evalBinaryOp?, sqrtFunctionYValue, uniswapUint256Value, uint256Value, hy]

theorem evalExpr_sqrtFunction_return_one (evm : EVM.State) (y : UInt256)
    (hy : y.toNat ≠ 0) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.intLit 1) = .ok (sqrtFunctionSmallResultValue y) := by
  simp [evalExpr?, pure, sqrtFunctionSmallResultValue, hy]

theorem evalExpr_sqrtFunction_return_zero (evm : EVM.State) (y : UInt256)
    (hy : y.toNat = 0) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.intLit 0) = .ok (sqrtFunctionSmallResultValue y) := by
  simp [evalExpr?, pure, sqrtFunctionSmallResultValue, hy]

theorem uniswapLookupSqrtFunction :
    lookupCallable? contract "sqrt" = some sqrtFunction.toCallable := by
  rfl

theorem bindParams_sqrtFunction_call (y : UInt256) :
    bindParams? sqrtFunction.params [sqrtFunctionYValue y] = some (sqrtFunctionCallStore y) := by
  simp [bindParams?, sqrtFunction, sqrtFunctionCallStore, sqrtFunctionYValue]

theorem uniswapSqrtFunctionBody_le3 (evm : EVM.State) (y : UInt256)
    (hsmall : y.toNat ≤ 3) :
    ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
      sqrtFunction.body
      (.returned { contract := contract, locals := sqrtFunctionCallStore y } evm
        (some [sqrtFunctionSmallResultValue y])) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := sqrtFunctionCallStore y } evm
    [ .ite (.binary .gt (.var "y") (.intLit 3))
        [ .letDecl "z" (some uint256) (.var "y"),
          .letDecl "x" (some uint256)
            (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary (.div (.uint ⟨256, by decide⟩) .wrapping)
                  (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := sqrtFunctionCallStore y } evm
      (some [sqrtFunctionSmallResultValue y]))
  refine ExecBlock.consReturn (ExecStmt.iteFalse
    (evalExpr_sqrtFunction_outer_false evm y hsmall) ?_)
  by_cases hy : y.toNat = 0
  · exact ExecBlock.consReturn (ExecStmt.iteFalse
      (evalExpr_sqrtFunction_inner_false evm y hy)
      (ExecBlock.consReturn
        (ExecStmt.return (evalExprs?_singleton (evalExpr_sqrtFunction_return_zero evm y hy)))))
  · exact ExecBlock.consReturn (ExecStmt.iteTrue
      (evalExpr_sqrtFunction_inner_true evm y hy)
      (ExecBlock.consReturn
        (ExecStmt.return (evalExprs?_singleton (evalExpr_sqrtFunction_return_one evm y hy)))))

theorem uniswapSqrtFunctionCallSuccess_le3 {caller : Frame} {evm : EVM.State}
    {y : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hsmall : y.toNat ≤ 3)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y]) :
    ExecStmt config caller evm (.internalCall "sqrt" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [sqrtFunctionSmallResultValue y])) evm) := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
    (name := "sqrt") (retVar := retVar) (args := args)
    (argVals := [sqrtFunctionYValue y])
    (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
    (calleeSolm := { contract := contract, locals := sqrtFunctionCallStore y })
    (value := some [sqrtFunctionSmallResultValue y])
    hargs
    (by simpa [hcontract] using uniswapLookupSqrtFunction)
    (bindParams_sqrtFunction_call y)
    (by simpa [hcontract] using uniswapSqrtFunctionBody_le3 evm y hsmall)

abbrev sqrtLoopCond : Expr :=
  .binary .lt (.var "x") (.var "z")

abbrev sqrtLoopNextXExpr : Expr :=
  .binary (.div (.uint ⟨256, by decide⟩) .wrapping)
    (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.var "x")) (.var "x"))
    (.intLit 2)

abbrev sqrtLoopBody : List Stmt :=
  [ .assign .localVar { base := "z" } (.var "x"),
    .assign .localVar { base := "x" } sqrtLoopNextXExpr ]

abbrev sqrtLoopAfterZStore (locals : Store) (x : Int) : Store :=
  locals.insert "z" (.int x)

abbrev sqrtLoopNextX (y x : Int) : Int :=
  (y / x + x) / 2

abbrev sqrtLoopAfterBodyStore (locals : Store) (y x : Int) : Store :=
  (sqrtLoopAfterZStore locals x).insert "x" (.int (sqrtLoopNextX y x))

abbrev sqrtFunctionYInt (y : UInt256) : Int :=
  Int.ofNat y.toNat

abbrev sqrtFunctionInitialX (y : UInt256) : Int :=
  sqrtFunctionYInt y / 2 + 1

abbrev sqrtFunctionAfterZStore (y : UInt256) : Store :=
  (sqrtFunctionCallStore y).insert "z" (sqrtFunctionYValue y)

abbrev sqrtFunctionAfterInitStore (y : UInt256) : Store :=
  (sqrtFunctionAfterZStore y).insert "x" (.int (sqrtFunctionInitialX y))

theorem sqrtFunctionInitialX_toNat (y : UInt256) :
    (sqrtFunctionInitialX y).toNat = y.toNat / 2 + 1 := by
  unfold sqrtFunctionInitialX sqrtFunctionYInt
  have hnonneg : 0 ≤ (Int.ofNat y.toNat / 2 + 1 : Int) := by
    have hdiv : 0 ≤ (Int.ofNat y.toNat : Int) / 2 :=
      Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)
    omega
  have hcast : ((y.toNat / 2 + 1 : Nat) : Int) = Int.ofNat y.toNat / 2 + 1 := by
    rw [Nat.cast_add, Int.natCast_ediv]
    · norm_num
  apply Nat.cast_injective (R := Int)
  rw [Int.toNat_of_nonneg hnonneg]
  exact hcast

theorem sqrtFunctionInitialX_size (y : UInt256) :
    (sqrtFunctionInitialX y).toNat < UInt256.size := by
  rw [sqrtFunctionInitialX_toNat]
  have hyLe : y.toNat ≤ UInt256.size - 1 := Nat.le_pred_of_lt y.val.isLt
  have hdivLe : y.toNat / 2 ≤ (UInt256.size - 1) / 2 := Nat.div_le_div_right hyLe
  have hbound : (UInt256.size - 1) / 2 + 1 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem sqrtFunctionInitialX_matches (y : UInt256) :
    valueMatchesOptionalABIType (some uint256) (.int (sqrtFunctionInitialX y)) = true := by
  have hnonneg : 0 ≤ sqrtFunctionInitialX y := by
    unfold sqrtFunctionInitialX sqrtFunctionYInt
    exact add_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)) (by omega)
  simp only [valueMatchesOptionalABIType, uint256, uint256Int, valueMatchesABIType,
    beq_iff_eq]
  apply normalizeInt_uint_eq_self
  · exact hnonneg
  · rw [← Int.toNat_of_nonneg hnonneg]
    apply Int.ofNat_lt.mpr
    change (sqrtFunctionInitialX y).toNat < UInt256.size
    exact sqrtFunctionInitialX_size y

theorem evalExpr_sqrtFunction_outer_true (evm : EVM.State) (y : UInt256)
    (hlarge : 3 < y.toNat) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.binary .gt (.var "y") (.intLit 3)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_sqrtFunction_y evm y, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_sqrtFunction_initX (evm : EVM.State) (y : UInt256) :
    evalExpr? config { contract := contract, locals := sqrtFunctionAfterZStore y } evm
      (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.intLit 2)) (.intLit 1)) =
        .ok (.int (sqrtFunctionInitialX y)) := by
  have hdivNonneg : 0 ≤ sqrtFunctionYInt y / 2 :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)
  have hdivFit : sqrtFunctionYInt y / 2 < Int.ofNat EVM.wordModulus := by
    have hcast : Int.ofNat (y.toNat / 2) = sqrtFunctionYInt y / 2 := by
      unfold sqrtFunctionYInt
      simp only [Int.ofNat_eq_natCast]
      rw [Int.natCast_ediv]
      norm_num
    rw [← hcast]
    exact Int.ofNat_lt.mpr (lt_of_le_of_lt (Nat.div_le_self _ _) y.val.isLt)
  have haddNonneg : 0 ≤ sqrtFunctionInitialX y := by
    unfold sqrtFunctionInitialX
    exact add_nonneg hdivNonneg (by norm_num)
  have haddFit : sqrtFunctionInitialX y < Int.ofNat EVM.wordModulus := by
    rw [← Int.toNat_of_nonneg haddNonneg]
    apply Int.ofNat_lt.mpr
    change (sqrtFunctionInitialX y).toNat < UInt256.size
    exact sqrtFunctionInitialX_size y
  have hdivEval :
      evalBinaryOp? (.div (.uint ⟨256, by decide⟩) .wrapping)
        (.int (sqrtFunctionYInt y)) (.int 2) =
          .ok (.int (sqrtFunctionYInt y / 2)) := by
    simp only [evalBinaryOp?]
    rw [if_neg (by norm_num)]
    exact evalIntArithResult_wrapping_uint_eq_self _ _ hdivNonneg hdivFit
  have haddEval :
      evalBinaryOp? (.add (.uint ⟨256, by decide⟩) .wrapping)
        (.int (sqrtFunctionYInt y / 2)) (.int 1) =
          .ok (.int (sqrtFunctionInitialX y)) := by
    simpa only [evalBinaryOp?, sqrtFunctionInitialX] using
      evalIntArithResult_wrapping_uint_eq_self
        (⟨256, by decide⟩ : BitWidth) (sqrtFunctionInitialX y) haddNonneg haddFit
  simp only [sqrtFunctionAfterZStore, evalExpr?,
    EvalResult.ofOption, EvalResult.bind, bind]
  rw [store_get_ne _ _ (by decide), sqrtFunctionCallStore_y]
  simp only [sqrtFunctionYValue, uniswapUint256Value, uint256Value, EvalResult.ofOption,
    EvalResult.bind, bind]
  rw [hdivEval]
  simp only [EvalResult.bind, bind]
  exact haddEval

theorem sqrtFunctionAfterInitStore_y (y : UInt256) :
    (sqrtFunctionAfterInitStore y).get? "y" = some (.int (sqrtFunctionYInt y)) := by
  rw [sqrtFunctionAfterInitStore, store_get_ne _ _ (by decide), sqrtFunctionAfterZStore,
    store_get_ne _ _ (by decide), sqrtFunctionCallStore_y]

theorem sqrtFunctionAfterInitStore_x (y : UInt256) :
    (sqrtFunctionAfterInitStore y).get? "x" =
      some (.int (sqrtFunctionInitialX y)) := by
  rw [sqrtFunctionAfterInitStore, store_get_self]

theorem sqrtFunctionAfterInitStore_z (y : UInt256) :
    (sqrtFunctionAfterInitStore y).get? "z" = some (.int (sqrtFunctionYInt y)) := by
  rw [sqrtFunctionAfterInitStore, store_get_ne _ _ (by decide), sqrtFunctionAfterZStore,
    store_get_self]

theorem sqrtFunctionInitialX_pos (y : UInt256) :
    0 < sqrtFunctionInitialX y := by
  unfold sqrtFunctionInitialX sqrtFunctionYInt
  have hdiv : 0 ≤ Int.ofNat y.toNat / 2 := by
    exact Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)
  omega

theorem evalExpr_sqrtLoopCond_true (evm : EVM.State) (locals : Store) (x z : Int)
    (hx : locals.get? "x" = some (.int x)) (hz : locals.get? "z" = some (.int z))
    (hlt : x < z) :
    evalExpr? config ({ contract := contract, locals := locals } : Frame) evm sqrtLoopCond =
      .ok (.bool true) := by
  simp only [sqrtLoopCond, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [hx, hz]
  simp [evalBinaryOp?, hlt]

theorem evalExpr_sqrtLoopCond_false (evm : EVM.State) (locals : Store) (x z : Int)
    (hx : locals.get? "x" = some (.int x)) (hz : locals.get? "z" = some (.int z))
    (hnlt : ¬ x < z) :
    evalExpr? config ({ contract := contract, locals := locals } : Frame) evm sqrtLoopCond =
      .ok (.bool false) := by
  simp only [sqrtLoopCond, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [hx, hz]
  simp [evalBinaryOp?, hnlt]

theorem sqrtLoopNextX_pos (y x : Int) (hy : 0 < y) (hx : 0 < x) :
    0 < sqrtLoopNextX y x := by
  unfold sqrtLoopNextX
  have hsum : 2 ≤ y / x + x := by
    by_cases hx1 : x = 1
    · subst x
      omega
    · have hx2 : 2 ≤ x := by omega
      have hdiv : 0 ≤ y / x := Int.ediv_nonneg (by omega) (by omega)
      omega
  omega

theorem sqrtLoopNextX_nonneg (y x : Int) (hyNonneg : 0 ≤ y) (hxPos : 0 < x) :
    0 ≤ sqrtLoopNextX y x := by
  unfold sqrtLoopNextX
  have hdivNonneg : 0 ≤ y / x := Int.ediv_nonneg hyNonneg (by omega)
  exact Int.ediv_nonneg (by omega) (by omega)

theorem sqrtLoopNextX_toNat (y x : Int) (hyNonneg : 0 ≤ y) (hxPos : 0 < x) :
    (sqrtLoopNextX y x).toNat = (y.toNat / x.toNat + x.toNat) / 2 := by
  have hnextNonneg := sqrtLoopNextX_nonneg y x hyNonneg hxPos
  have hcastDiv : ((y.toNat / x.toNat : Nat) : Int) = y / x := by
    rw [Int.natCast_ediv]
    · simp [Int.toNat_of_nonneg hyNonneg, Int.toNat_of_nonneg (le_of_lt hxPos)]
  have hcastSum :
      ((y.toNat / x.toNat + x.toNat : Nat) : Int) = y / x + x := by
    rw [Nat.cast_add, hcastDiv]
    simp [Int.toNat_of_nonneg (le_of_lt hxPos)]
  have hcastDiv2 :
      (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int) =
        (y / x + x) / 2 := by
    rw [Int.natCast_ediv]
    · rw [hcastSum]
      norm_num
  calc
    (sqrtLoopNextX y x).toNat = ((y / x + x) / 2).toNat := by rfl
    _ = (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int).toNat :=
      (congrArg Int.toNat hcastDiv2).symm
    _ = (y.toNat / x.toNat + x.toNat) / 2 := by rw [Int.toNat_natCast]

theorem sqrtLoopNextX_size_of_add_fit
    (y x : Int)
    (hyNonneg : 0 ≤ y)
    (hxPos : 0 < x)
    (haddFit : y.toNat / x.toNat + x.toNat < UInt256.size) :
    (sqrtLoopNextX y x).toNat < UInt256.size := by
  rw [sqrtLoopNextX_toNat y x hyNonneg hxPos]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) haddFit

theorem sqrtLoop_step_add_le_y_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    y / x + x ≤ y := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hdiv3 : y / x ≤ y / 3 := Nat.div_le_div_left (a := y) hx3 (by norm_num)
    omega

theorem sqrtLoop_step_next_low_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    2 ≤ (y / x + x) / 2 := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hxLeY : x ≤ y := by omega
    have hdivPos : 0 < y / x := Nat.div_pos hxLeY (by omega)
    omega

theorem sqrtLoop_step_next_high_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    (y / x + x) / 2 ≤ y / 2 + 1 := by
  have hsum := sqrtLoop_step_add_le_y_of_bounds y x hy hxLow hxHigh
  have hdiv : (y / x + x) / 2 ≤ y / 2 := Nat.div_le_div_right hsum
  omega

abbrev sqrtLoopRuntimeInv (y x : Int) : Prop :=
  2 ≤ x.toNat ∧ x.toNat ≤ y.toNat / 2 + 1

theorem sqrtLoopRuntimeInv_step_fit
    (y x : Int)
    (hy : 3 < y.toNat)
    (hySize : y.toNat < UInt256.size)
    (hP : sqrtLoopRuntimeInv y x) :
    y.toNat / x.toNat + x.toNat < UInt256.size := by
  exact lt_of_le_of_lt (sqrtLoop_step_add_le_y_of_bounds y.toNat x.toNat hy hP.1 hP.2)
    hySize

theorem sqrtLoopRuntimeInv_step
    (y x : Int)
    (hy : 3 < y.toNat)
    (hP : sqrtLoopRuntimeInv y x)
    (hxPos : 0 < x) :
    sqrtLoopRuntimeInv y (sqrtLoopNextX y x) := by
  change 2 ≤ (sqrtLoopNextX y x).toNat ∧
    (sqrtLoopNextX y x).toNat ≤ y.toNat / 2 + 1
  rw [sqrtLoopNextX_toNat y x (by omega) hxPos]
  constructor
  · exact sqrtLoop_step_next_low_of_bounds y.toNat x.toNat hy hP.1 hP.2
  · exact sqrtLoop_step_next_high_of_bounds y.toNat x.toNat hy hP.1 hP.2

theorem sqrtFunctionInitialX_word_eq (y : UInt256) :
    UInt256.div y (⟨2⟩ : UInt256) + ⟨1⟩ =
      UInt256.ofNat (sqrtFunctionInitialX y).toNat := by
  apply u256_inj
  rw [uadd_toNat, udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from by decide,
    show (⟨1⟩ : UInt256).toNat = 1 from by decide, sqrtFunctionInitialX_toNat]
  rw [ulit_toNat' _ (by
    simpa [sqrtFunctionInitialX_toNat] using sqrtFunctionInitialX_size y)]
  rw [Nat.mod_eq_of_lt (by
    simpa [sqrtFunctionInitialX_toNat] using sqrtFunctionInitialX_size y)]

theorem sqrtFunctionInitialX_runtime_inv (y : UInt256) (hlarge : 3 < y.toNat) :
    sqrtLoopRuntimeInv (sqrtFunctionYInt y) (sqrtFunctionInitialX y) := by
  change 2 ≤ (sqrtFunctionInitialX y).toNat ∧
    (sqrtFunctionInitialX y).toNat ≤ (sqrtFunctionYInt y).toNat / 2 + 1
  rw [sqrtFunctionInitialX_toNat]
  constructor
  · omega
  · unfold sqrtFunctionYInt
    rw [show (Int.ofNat y.toNat).toNat = y.toNat by simp]

theorem assign_sqrtLoop_z (evm : EVM.State) (locals : Store) (x z : Int)
    (hz : locals.get? "z" = some (.int z)) :
    assignStorageRef? config ({ contract := contract, locals := locals } : Frame) evm
      .localVar { base := "z" } (.int x) =
        .ok (({ contract := contract, locals := sqrtLoopAfterZStore locals x } : Frame), evm) := by
  rw [assignStorageRef?, hz]
  simp [sqrtLoopAfterZStore, updateLocalPath?, EvalResult.bind, bind, pure]

theorem sqrtLoopAfterZStore_y (locals : Store) (y x : Int)
    (hy : locals.get? "y" = some (.int y)) :
    (sqrtLoopAfterZStore locals x).get? "y" = some (.int y) := by
  rw [sqrtLoopAfterZStore, store_get_ne _ _ (by decide), hy]

theorem sqrtLoopAfterZStore_x (locals : Store) (x : Int)
    (hx : locals.get? "x" = some (.int x)) :
    (sqrtLoopAfterZStore locals x).get? "x" = some (.int x) := by
  rw [sqrtLoopAfterZStore, store_get_ne _ _ (by decide), hx]

theorem sqrtLoopAfterBodyStore_y (locals : Store) (y x : Int)
    (hy : locals.get? "y" = some (.int y)) :
    (sqrtLoopAfterBodyStore locals y x).get? "y" = some (.int y) := by
  rw [sqrtLoopAfterBodyStore, store_get_ne _ _ (by decide),
    sqrtLoopAfterZStore_y locals y x hy]

theorem sqrtLoopAfterBodyStore_x (locals : Store) (y x : Int) :
    (sqrtLoopAfterBodyStore locals y x).get? "x" = some (.int (sqrtLoopNextX y x)) := by
  rw [sqrtLoopAfterBodyStore, store_get_self]

theorem sqrtLoopAfterBodyStore_z (locals : Store) (y x : Int) :
    (sqrtLoopAfterBodyStore locals y x).get? "z" = some (.int x) := by
  rw [sqrtLoopAfterBodyStore, store_get_ne _ _ (by decide), sqrtLoopAfterZStore,
    store_get_self]

theorem assign_sqrtLoop_x (evm : EVM.State) (locals : Store) (y x : Int)
    (hx : locals.get? "x" = some (.int x)) :
    assignStorageRef? config
      ({ contract := contract, locals := sqrtLoopAfterZStore locals x } : Frame) evm
      .localVar { base := "x" } (.int (sqrtLoopNextX y x)) =
        .ok (({ contract := contract, locals := sqrtLoopAfterBodyStore locals y x } : Frame),
          evm) := by
  have hx' : (sqrtLoopAfterZStore locals x).get? "x" = some (.int x) :=
    sqrtLoopAfterZStore_x locals x hx
  rw [assignStorageRef?, hx']
  simp [sqrtLoopAfterZStore, sqrtLoopAfterBodyStore, updateLocalPath?, EvalResult.bind, bind,
    pure]

theorem execBlock_sqrtLoopBody (evm : EVM.State) (locals : Store) (y x z : Int)
    (hy : locals.get? "y" = some (.int y)) (hx : locals.get? "x" = some (.int x))
    (hz : locals.get? "z" = some (.int z)) (hyNonneg : 0 ≤ y) (hxPos : 0 < x)
    (haddFit : y.toNat / x.toNat + x.toNat < UInt256.size) :
    ExecBlock config ({ contract := contract, locals := locals } : Frame) evm sqrtLoopBody
      (.ok (show Frame from
        { contract := contract, locals := sqrtLoopAfterBodyStore locals y x }) evm) := by
  have hEvalX :
      evalExpr? config ({ contract := contract, locals := locals } : Frame) evm (.var "x") =
        .ok (.int x) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hx]
  have hAssignZ := assign_sqrtLoop_z evm locals x z hz
  have hdivCast : Int.ofNat (y.toNat / x.toNat) = y / x := by
    simp only [Int.ofNat_eq_natCast]
    rw [Int.natCast_ediv]
    simp [Int.toNat_of_nonneg hyNonneg, Int.toNat_of_nonneg (le_of_lt hxPos)]
  have hsumCast : Int.ofNat (y.toNat / x.toNat + x.toNat) = y / x + x := by
    have hxCast : Int.ofNat x.toNat = x := by
      change (x.toNat : Int) = x
      exact Int.toNat_of_nonneg (le_of_lt hxPos)
    simp only [Int.ofNat_eq_natCast]
    rw [Nat.cast_add]
    change Int.ofNat (y.toNat / x.toNat) + Int.ofNat x.toNat = y / x + x
    rw [hdivCast, hxCast]
  have hdivNonneg : 0 ≤ y / x := Int.ediv_nonneg hyNonneg (le_of_lt hxPos)
  have hsumNonneg : 0 ≤ y / x + x := by omega
  have hsumFit : y / x + x < Int.ofNat EVM.wordModulus := by
    rw [← hsumCast]
    exact Int.ofNat_lt.mpr (by simpa [UInt256.size] using haddFit)
  have hdivFit : y / x < Int.ofNat EVM.wordModulus := by omega
  have hnextNonneg : 0 ≤ sqrtLoopNextX y x :=
    Int.ediv_nonneg hsumNonneg (by norm_num)
  have hnextFit : sqrtLoopNextX y x < Int.ofNat EVM.wordModulus := by
    unfold sqrtLoopNextX
    omega
  have hdivEval :
      evalBinaryOp? (.div (.uint ⟨256, by decide⟩) .wrapping) (.int y) (.int x) =
        .ok (.int (y / x)) := by
    simp only [evalBinaryOp?]
    rw [if_neg (ne_of_gt hxPos)]
    rw [Int.tdiv_eq_ediv_of_nonneg hyNonneg]
    exact evalIntArithResult_wrapping_uint_eq_self
      (⟨256, by decide⟩ : BitWidth) _ hdivNonneg hdivFit
  have haddEval :
      evalBinaryOp? (.add (.uint ⟨256, by decide⟩) .wrapping) (.int (y / x)) (.int x) =
        .ok (.int (y / x + x)) := by
    exact evalIntArithResult_wrapping_uint_eq_self _ _ hsumNonneg hsumFit
  have hhalfEval :
      evalBinaryOp? (.div (.uint ⟨256, by decide⟩) .wrapping)
          (.int (y / x + x)) (.int 2) = .ok (.int (sqrtLoopNextX y x)) := by
    simp only [evalBinaryOp?]
    rw [if_neg (by norm_num)]
    rw [Int.tdiv_eq_ediv_of_nonneg hsumNonneg]
    simpa only [sqrtLoopNextX] using
      evalIntArithResult_wrapping_uint_eq_self
        (⟨256, by decide⟩ : BitWidth) _ hnextNonneg hnextFit
  have hEvalNext :
      evalExpr? config
        ({ contract := contract, locals := sqrtLoopAfterZStore locals x } : Frame) evm
        sqrtLoopNextXExpr = .ok (.int (sqrtLoopNextX y x)) := by
    simp only [sqrtLoopNextXExpr, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [sqrtLoopAfterZStore_y locals y x hy, sqrtLoopAfterZStore_x locals x hx]
    simp only [EvalResult.ofOption, EvalResult.bind, bind]
    rw [hdivEval]
    simp only [EvalResult.bind, bind]
    rw [haddEval]
    simp only [EvalResult.bind, bind]
    exact hhalfEval
  have hAssignX := assign_sqrtLoop_x evm locals y x hx
  refine ExecBlock.consNormal (ExecStmt.assign hEvalX hAssignZ) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hEvalNext hAssignX) ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem execStmt_sqrtLoopTerminates (evm : EVM.State) (y : Int) (hypos : 0 < y)
    (hySize : y.toNat < UInt256.size) (hyLarge : 3 < y.toNat) :
    ∀ fuel, ∀ locals x z,
      z.toNat = fuel → 0 < x → 0 ≤ z → sqrtLoopRuntimeInv y x →
      locals.get? "y" = some (.int y) → locals.get? "x" = some (.int x) →
      locals.get? "z" = some (.int z) →
      ∃ locals' result,
        ExecStmt config ({ contract := contract, locals := locals } : Frame) evm
          (.while sqrtLoopCond sqrtLoopBody)
          (.ok (show Frame from { contract := contract, locals := locals' }) evm) ∧
        locals'.get? "z" = some (.int result) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro locals x z hzFuel hxpos hznonneg hP hy hx hz
      by_cases hlt : x < z
      · have hcond := evalExpr_sqrtLoopCond_true evm locals x z hx hz hlt
        have haddFit := sqrtLoopRuntimeInv_step_fit y x hyLarge hySize hP
        have hbody := execBlock_sqrtLoopBody evm locals y x z hy hx hz
          (le_of_lt hypos) hxpos haddFit
        have hzpos : 0 < z := by omega
        have hmeasure : x.toNat < fuel := by
          rw [← hzFuel]
          exact (Int.toNat_lt_toNat hzpos).mpr hlt
        obtain ⟨locals', result, hwhile, hzFinal⟩ := ih x.toNat hmeasure
          (sqrtLoopAfterBodyStore locals y x) (sqrtLoopNextX y x) x rfl
          (sqrtLoopNextX_pos y x hypos hxpos) (by omega)
          (sqrtLoopRuntimeInv_step y x hyLarge hP hxpos)
          (sqrtLoopAfterBodyStore_y locals y x hy) (sqrtLoopAfterBodyStore_x locals y x)
          (sqrtLoopAfterBodyStore_z locals y x)
        exact ⟨locals', result, ExecStmt.whileTrue hcond hbody hwhile, hzFinal⟩
      · have hcond := evalExpr_sqrtLoopCond_false evm locals x z hx hz hlt
        exact ⟨locals, z, ExecStmt.whileFalse hcond, hz⟩

set_option maxHeartbeats 1000000 in
theorem execStmt_sqrtLoopTerminates_bound (evm : EVM.State) (y : Int) (hypos : 0 < y)
    (hySize : y.toNat < UInt256.size) (hyLarge : 3 < y.toNat) :
    ∀ fuel, ∀ locals x z,
      z.toNat = fuel → 0 < x → 0 ≤ z → sqrtLoopRuntimeInv y x →
      locals.get? "y" = some (.int y) → locals.get? "x" = some (.int x) →
      locals.get? "z" = some (.int z) →
      ∃ locals' result,
        ExecStmt config ({ contract := contract, locals := locals } : Frame) evm
          (.while sqrtLoopCond sqrtLoopBody)
          (.ok (show Frame from { contract := contract, locals := locals' }) evm) ∧
        locals'.get? "z" = some (.int result) ∧
        0 ≤ result ∧ result.toNat ≤ fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro locals x z hzFuel hxpos hznonneg hP hy hx hz
      by_cases hlt : x < z
      · have hcond := evalExpr_sqrtLoopCond_true evm locals x z hx hz hlt
        have haddFit := sqrtLoopRuntimeInv_step_fit y x hyLarge hySize hP
        have hbody := execBlock_sqrtLoopBody evm locals y x z hy hx hz
          (le_of_lt hypos) hxpos haddFit
        have hzpos : 0 < z := by omega
        have hmeasure : x.toNat < fuel := by
          rw [← hzFuel]
          exact (Int.toNat_lt_toNat hzpos).mpr hlt
        obtain ⟨locals', result, hwhile, hzFinal, hresultNonneg, hresultFuel⟩ :=
          ih x.toNat hmeasure
            (sqrtLoopAfterBodyStore locals y x) (sqrtLoopNextX y x) x rfl
            (sqrtLoopNextX_pos y x hypos hxpos) (by omega)
            (sqrtLoopRuntimeInv_step y x hyLarge hP hxpos)
            (sqrtLoopAfterBodyStore_y locals y x hy) (sqrtLoopAfterBodyStore_x locals y x)
            (sqrtLoopAfterBodyStore_z locals y x)
        exact ⟨locals', result, ExecStmt.whileTrue hcond hbody hwhile, hzFinal,
          hresultNonneg, le_trans hresultFuel (Nat.le_of_lt hmeasure)⟩
      · have hcond := evalExpr_sqrtLoopCond_false evm locals x z hx hz hlt
        exact ⟨locals, z, ExecStmt.whileFalse hcond, hz, hznonneg, by
          rw [hzFuel]⟩

theorem uniswapSqrtFunctionBody_gt3 (evm : EVM.State) (y : UInt256)
    (hlarge : 3 < y.toNat) :
    ∃ locals' result,
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [.int result])) := by
  have hypos : 0 < sqrtFunctionYInt y := by
    unfold sqrtFunctionYInt
    have hyNat : 0 < y.toNat := by omega
    exact Int.ofNat_lt.mpr hyNat
  have hySize : (sqrtFunctionYInt y).toNat < UInt256.size := by
    change y.toNat < UInt256.size
    exact y.val.isLt
  have hyLarge : 3 < (sqrtFunctionYInt y).toNat := by
    simpa [sqrtFunctionYInt] using hlarge
  obtain ⟨locals', result, hwhile, hzFinal⟩ :=
    execStmt_sqrtLoopTerminates evm (sqrtFunctionYInt y) hypos hySize hyLarge y.toNat
      (sqrtFunctionAfterInitStore y) (sqrtFunctionInitialX y) (sqrtFunctionYInt y)
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_pos y) (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_runtime_inv y hlarge)
      (sqrtFunctionAfterInitStore_y y) (sqrtFunctionAfterInitStore_x y)
      (sqrtFunctionAfterInitStore_z y)
  refine ⟨locals', result, ExecFuncBody.execBlockRet ?_⟩
  change ExecBlock config { contract := contract, locals := sqrtFunctionCallStore y } evm
    [ .ite (.binary .gt (.var "y") (.intLit 3))
        [ .letDecl "z" (some uint256) (.var "y"),
          .letDecl "x" (some uint256)
            (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary (.div (.uint ⟨256, by decide⟩) .wrapping)
                  (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_sqrtFunction_outer_true evm y hlarge) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_y evm y)
    (valueMatchesOptionalABIType_uint256_word y)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_initX evm y)
    (sqrtFunctionInitialX_matches y)) ?_
  have hwhile' :
      ExecStmt config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
        evm (.while sqrtLoopCond sqrtLoopBody)
        (.ok ({ contract := contract, locals := locals' } : Frame) evm) := by
    simpa using hwhile
  change ExecBlock config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
    evm [ .while sqrtLoopCond sqrtLoopBody, .return [(.var "z")] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consNormal hwhile' ?_
  have hret :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "z") =
        .ok (.int result) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hzFinal]
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret))

theorem uniswapSqrtFunctionBody_gt3_bound (evm : EVM.State) (y : UInt256)
    (hlarge : 3 < y.toNat) :
    ∃ locals' result,
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [.int result])) ∧
      0 ≤ result ∧ result.toNat < UInt256.size := by
  have hypos : 0 < sqrtFunctionYInt y := by
    unfold sqrtFunctionYInt
    have hyNat : 0 < y.toNat := by omega
    exact Int.ofNat_lt.mpr hyNat
  have hySize : (sqrtFunctionYInt y).toNat < UInt256.size := by
    change y.toNat < UInt256.size
    exact y.val.isLt
  have hyLarge : 3 < (sqrtFunctionYInt y).toNat := by
    simpa [sqrtFunctionYInt] using hlarge
  obtain ⟨locals', result, hwhile, hzFinal, hresultNonneg, hresultFuel⟩ :=
    execStmt_sqrtLoopTerminates_bound evm (sqrtFunctionYInt y) hypos hySize hyLarge y.toNat
      (sqrtFunctionAfterInitStore y) (sqrtFunctionInitialX y) (sqrtFunctionYInt y)
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_pos y) (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_runtime_inv y hlarge)
      (sqrtFunctionAfterInitStore_y y) (sqrtFunctionAfterInitStore_x y)
      (sqrtFunctionAfterInitStore_z y)
  have hresultSize : result.toNat < UInt256.size :=
    lt_of_le_of_lt hresultFuel y.val.isLt
  refine ⟨locals', result, ?_, hresultNonneg, hresultSize⟩
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := sqrtFunctionCallStore y } evm
    [ .ite (.binary .gt (.var "y") (.intLit 3))
        [ .letDecl "z" (some uint256) (.var "y"),
          .letDecl "x" (some uint256)
            (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary (.div (.uint ⟨256, by decide⟩) .wrapping)
                  (.binary (.add (.uint ⟨256, by decide⟩) .wrapping) (.binary (.div (.uint ⟨256, by decide⟩) .wrapping) (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_sqrtFunction_outer_true evm y hlarge) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_y evm y)
    (valueMatchesOptionalABIType_uint256_word y)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_initX evm y)
    (sqrtFunctionInitialX_matches y)) ?_
  have hwhile' :
      ExecStmt config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
        evm (.while sqrtLoopCond sqrtLoopBody)
        (.ok ({ contract := contract, locals := locals' } : Frame) evm) := by
    simpa using hwhile
  change ExecBlock config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
    evm [ .while sqrtLoopCond sqrtLoopBody, .return [(.var "z")] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consNormal hwhile' ?_
  have hret :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "z") =
        .ok (.int result) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hzFinal]
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret))

theorem uniswapSqrtFunctionBody_exists (evm : EVM.State) (y : UInt256) :
    ∃ locals' value,
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [value])) := by
  by_cases hsmall : y.toNat ≤ 3
  · exact ⟨sqrtFunctionCallStore y, sqrtFunctionSmallResultValue y,
      uniswapSqrtFunctionBody_le3 evm y hsmall⟩
  · have hlarge : 3 < y.toNat := by omega
    obtain ⟨locals', result, hbody⟩ := uniswapSqrtFunctionBody_gt3 evm y hlarge
    exact ⟨locals', .int result, hbody⟩

theorem uniswapSqrtFunctionBody_intExists (evm : EVM.State) (y : UInt256) :
    ∃ locals' result,
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [.int result])) := by
  by_cases hsmall : y.toNat ≤ 3
  · by_cases hy : y.toNat = 0
    · refine ⟨sqrtFunctionCallStore y, 0, ?_⟩
      simpa [sqrtFunctionSmallResultValue, hy] using
        uniswapSqrtFunctionBody_le3 evm y hsmall
    · refine ⟨sqrtFunctionCallStore y, 1, ?_⟩
      simpa [sqrtFunctionSmallResultValue, hy] using
        uniswapSqrtFunctionBody_le3 evm y hsmall
  · have hlarge : 3 < y.toNat := by omega
    exact uniswapSqrtFunctionBody_gt3 evm y hlarge

theorem uniswapSqrtFunctionBody_intExistsBounded (evm : EVM.State) (y : UInt256) :
    ∃ locals' result,
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [.int result])) ∧
      0 ≤ result ∧ result.toNat < UInt256.size := by
  by_cases hsmall : y.toNat ≤ 3
  · by_cases hy : y.toNat = 0
    · refine ⟨sqrtFunctionCallStore y, 0, ?_, by omega, by norm_num [UInt256.size]⟩
      simpa [sqrtFunctionSmallResultValue, hy] using
        uniswapSqrtFunctionBody_le3 evm y hsmall
    · refine ⟨sqrtFunctionCallStore y, 1, ?_, by omega, by norm_num [UInt256.size]⟩
      simpa [sqrtFunctionSmallResultValue, hy] using
        uniswapSqrtFunctionBody_le3 evm y hsmall
  · have hlarge : 3 < y.toNat := by omega
    exact uniswapSqrtFunctionBody_gt3_bound evm y hlarge

theorem uniswapSqrtFunctionCallSuccess {caller : Frame} {evm : EVM.State}
    {y : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y]) :
    ∃ value,
      ExecStmt config caller evm (.internalCall "sqrt" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [value])) evm) := by
  obtain ⟨locals', value, hbody⟩ := uniswapSqrtFunctionBody_exists evm y
  exact ⟨value,
    internalCallFunctionReturn
      (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
      (name := "sqrt") (retVar := retVar) (args := args)
      (argVals := [sqrtFunctionYValue y])
      (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
      (calleeSolm := { contract := contract, locals := locals' })
      (value := some [value])
      hargs
      (by simpa [hcontract] using uniswapLookupSqrtFunction)
      (bindParams_sqrtFunction_call y)
      (by simpa [hcontract] using hbody)⟩

theorem uniswapSqrtFunctionCallSuccessInt {caller : Frame} {evm : EVM.State}
    {y : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y]) :
    ∃ result,
      ExecStmt config caller evm (.internalCall "sqrt" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) := by
  obtain ⟨locals', result, hbody⟩ := uniswapSqrtFunctionBody_intExists evm y
  exact ⟨result,
    internalCallFunctionReturn
      (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
      (name := "sqrt") (retVar := retVar) (args := args)
      (argVals := [sqrtFunctionYValue y])
      (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
      (calleeSolm := { contract := contract, locals := locals' })
      (value := some [.int result])
      hargs
      (by simpa [hcontract] using uniswapLookupSqrtFunction)
      (bindParams_sqrtFunction_call y)
      (by simpa [hcontract] using hbody)⟩

theorem uniswapSqrtFunctionCallSuccessIntBounded {caller : Frame} {evm : EVM.State}
    {y : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y]) :
    ∃ result,
      ExecStmt config caller evm (.internalCall "sqrt" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) ∧
      0 ≤ result ∧ result.toNat < UInt256.size := by
  obtain ⟨locals', result, hbody, hresultNonneg, hresultSize⟩ :=
    uniswapSqrtFunctionBody_intExistsBounded evm y
  refine ⟨result, ?_, hresultNonneg, hresultSize⟩
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
    (name := "sqrt") (retVar := retVar) (args := args)
    (argVals := [sqrtFunctionYValue y])
    (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
    (calleeSolm := { contract := contract, locals := locals' })
    (value := some [.int result])
    hargs
    (by simpa [hcontract] using uniswapLookupSqrtFunction)
    (bindParams_sqrtFunction_call y)
    (by simpa [hcontract] using hbody)

abbrev minFunctionXValue (x : UInt256) : Value :=
  uniswapUint256Value x

abbrev minFunctionYValue (y : UInt256) : Value :=
  uniswapUint256Value y

abbrev minFunctionCallStore (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (minFunctionYValue y)).insert "x" (minFunctionXValue x)

def minFunctionResultWord (x y : UInt256) : UInt256 :=
  if x.toNat < y.toNat then x else y

abbrev minFunctionResultValue (x y : UInt256) : Value :=
  uniswapUint256Value (minFunctionResultWord x y)

theorem minFunctionCallStore_x (x y : UInt256) :
    (minFunctionCallStore x y).get? "x" = some (minFunctionXValue x) := by
  rw [minFunctionCallStore, store_get_self]

theorem minFunctionCallStore_y (x y : UInt256) :
    (minFunctionCallStore x y).get? "y" = some (minFunctionYValue y) := by
  rw [minFunctionCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_minFunction_x (evm : EVM.State) (x y : UInt256) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.var "x") = .ok (minFunctionXValue x) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [minFunctionCallStore_x]

theorem evalExpr_minFunction_y (evm : EVM.State) (x y : UInt256) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.var "y") = .ok (minFunctionYValue y) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [minFunctionCallStore_y]

theorem evalExpr_minFunction_cond_true (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.binary .lt (.var "x") (.var "y")) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_minFunction_x evm x y, evalExpr_minFunction_y evm x y,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hlt

theorem evalExpr_minFunction_cond_false (evm : EVM.State) (x y : UInt256)
    (hnlt : ¬ x.toNat < y.toNat) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.binary .lt (.var "x") (.var "y")) = .ok (.bool false) := by
  have hge : y.toNat ≤ x.toNat := by omega
  simp only [evalExpr?, evalExpr_minFunction_x evm x y, evalExpr_minFunction_y evm x y,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hge

theorem evalExpr_minFunction_return_true (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.ite (.binary .lt (.var "x") (.var "y")) (.var "x") (.var "y")) =
        .ok (minFunctionResultValue x y) := by
  simp only [evalExpr?, evalExpr_minFunction_cond_true evm x y hlt, EvalResult.bind, bind]
  rw [minFunctionCallStore_x]
  simp [EvalResult.ofOption, minFunctionResultValue, minFunctionResultWord, hlt]

theorem evalExpr_minFunction_return_false (evm : EVM.State) (x y : UInt256)
    (hnlt : ¬ x.toNat < y.toNat) :
    evalExpr? config { contract := contract, locals := minFunctionCallStore x y } evm
      (.ite (.binary .lt (.var "x") (.var "y")) (.var "x") (.var "y")) =
        .ok (minFunctionResultValue x y) := by
  simp only [evalExpr?, evalExpr_minFunction_cond_false evm x y hnlt, EvalResult.bind, bind]
  rw [minFunctionCallStore_y]
  simp [EvalResult.ofOption, minFunctionResultValue, minFunctionResultWord, hnlt]

theorem uniswapLookupMinFunction :
    lookupCallable? contract "min" = some minFunction.toCallable := by
  rfl

theorem bindParams_minFunction_call (x y : UInt256) :
    bindParams? minFunction.params [minFunctionXValue x, minFunctionYValue y] =
      some (minFunctionCallStore x y) := by
  simp [bindParams?, minFunction, minFunctionCallStore, minFunctionXValue, minFunctionYValue]

theorem uniswapMinFunctionBody_lt (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := minFunctionCallStore x y } evm
      minFunction.body
      (.returned { contract := contract, locals := minFunctionCallStore x y } evm
        (some [minFunctionResultValue x y])) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := minFunctionCallStore x y } evm
    [ .return [(.ite (.binary .lt (.var "x") (.var "y")) (.var "x") (.var "y"))] ]
    (.returned { contract := contract, locals := minFunctionCallStore x y } evm
      (some [minFunctionResultValue x y]))
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (evalExpr_minFunction_return_true evm x y hlt)))

theorem uniswapMinFunctionBody_ge (evm : EVM.State) (x y : UInt256)
    (hnlt : ¬ x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := minFunctionCallStore x y } evm
      minFunction.body
      (.returned { contract := contract, locals := minFunctionCallStore x y } evm
        (some [minFunctionResultValue x y])) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := minFunctionCallStore x y } evm
    [ .return [(.ite (.binary .lt (.var "x") (.var "y")) (.var "x") (.var "y"))] ]
    (.returned { contract := contract, locals := minFunctionCallStore x y } evm
      (some [minFunctionResultValue x y]))
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (evalExpr_minFunction_return_false evm x y hnlt)))

theorem uniswapMinFunctionBody (evm : EVM.State) (x y : UInt256) :
    ExecFuncBody config { contract := contract, locals := minFunctionCallStore x y } evm
      minFunction.body
      (.returned { contract := contract, locals := minFunctionCallStore x y } evm
        (some [minFunctionResultValue x y])) := by
  by_cases hlt : x.toNat < y.toNat
  · exact uniswapMinFunctionBody_lt evm x y hlt
  · exact uniswapMinFunctionBody_ge evm x y hlt

theorem uniswapMinFunctionCallSuccess {caller : Frame} {evm : EVM.State}
    {x y : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [minFunctionXValue x, minFunctionYValue y]) :
    ExecStmt config caller evm (.internalCall "min" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [minFunctionResultValue x y])) evm) := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
    (name := "min") (retVar := retVar) (args := args)
    (argVals := [minFunctionXValue x, minFunctionYValue y])
    (callee := minFunction) (locals := minFunctionCallStore x y)
    (calleeSolm := { contract := contract, locals := minFunctionCallStore x y })
    (value := some [minFunctionResultValue x y])
    hargs
    (by simpa [hcontract] using uniswapLookupMinFunction)
    (bindParams_minFunction_call x y)
    (by simpa [hcontract] using uniswapMinFunctionBody evm x y)

end UniswapV2Pair
