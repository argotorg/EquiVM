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
            (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary .div
                  (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
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
  .binary .div
    (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
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

theorem evalExpr_sqrtFunction_outer_true (evm : EVM.State) (y : UInt256)
    (hlarge : 3 < y.toNat) :
    evalExpr? config { contract := contract, locals := sqrtFunctionCallStore y } evm
      (.binary .gt (.var "y") (.intLit 3)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_sqrtFunction_y evm y, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_sqrtFunction_initX (evm : EVM.State) (y : UInt256) :
    evalExpr? config { contract := contract, locals := sqrtFunctionAfterZStore y } evm
      (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)) =
        .ok (.int (sqrtFunctionInitialX y)) := by
  simp only [sqrtFunctionAfterZStore, sqrtFunctionInitialX, sqrtFunctionYInt, evalExpr?,
    EvalResult.ofOption, EvalResult.bind, bind]
  rw [store_get_ne _ _ (by decide), sqrtFunctionCallStore_y]
  simp [evalBinaryOp?]

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
    (hz : locals.get? "z" = some (.int z)) (hx0 : x ≠ 0) :
    ExecBlock config ({ contract := contract, locals := locals } : Frame) evm sqrtLoopBody
      (.ok (show Frame from
        { contract := contract, locals := sqrtLoopAfterBodyStore locals y x }) evm) := by
  have hEvalX :
      evalExpr? config ({ contract := contract, locals := locals } : Frame) evm (.var "x") =
        .ok (.int x) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hx]
  have hAssignZ := assign_sqrtLoop_z evm locals x z hz
  have hEvalNext :
      evalExpr? config
        ({ contract := contract, locals := sqrtLoopAfterZStore locals x } : Frame) evm
        sqrtLoopNextXExpr = .ok (.int (sqrtLoopNextX y x)) := by
    simp only [sqrtLoopNextXExpr, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [sqrtLoopAfterZStore_y locals y x hy, sqrtLoopAfterZStore_x locals x hx]
    simp [evalBinaryOp?, sqrtLoopNextX, hx0]
  have hAssignX := assign_sqrtLoop_x evm locals y x hx
  refine ExecBlock.consNormal (ExecStmt.assign hEvalX hAssignZ) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hEvalNext hAssignX) ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem execStmt_sqrtLoopTerminates (evm : EVM.State) (y : Int) (hypos : 0 < y) :
    ∀ fuel, ∀ locals x z,
      z.toNat = fuel → 0 < x → 0 ≤ z →
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
      intro locals x z hzFuel hxpos hznonneg hy hx hz
      by_cases hlt : x < z
      · have hcond := evalExpr_sqrtLoopCond_true evm locals x z hx hz hlt
        have hbody := execBlock_sqrtLoopBody evm locals y x z hy hx hz (ne_of_gt hxpos)
        have hzpos : 0 < z := by omega
        have hmeasure : x.toNat < fuel := by
          rw [← hzFuel]
          exact (Int.toNat_lt_toNat hzpos).mpr hlt
        obtain ⟨locals', result, hwhile, hzFinal⟩ := ih x.toNat hmeasure
          (sqrtLoopAfterBodyStore locals y x) (sqrtLoopNextX y x) x rfl
          (sqrtLoopNextX_pos y x hypos hxpos) (by omega)
          (sqrtLoopAfterBodyStore_y locals y x hy) (sqrtLoopAfterBodyStore_x locals y x)
          (sqrtLoopAfterBodyStore_z locals y x)
        exact ⟨locals', result, ExecStmt.whileTrue hcond hbody hwhile, hzFinal⟩
      · have hcond := evalExpr_sqrtLoopCond_false evm locals x z hx hz hlt
        exact ⟨locals, z, ExecStmt.whileFalse hcond, hz⟩

set_option maxHeartbeats 1000000 in
theorem execStmt_sqrtLoopTerminates_bound (evm : EVM.State) (y : Int) (hypos : 0 < y) :
    ∀ fuel, ∀ locals x z,
      z.toNat = fuel → 0 < x → 0 ≤ z →
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
      intro locals x z hzFuel hxpos hznonneg hy hx hz
      by_cases hlt : x < z
      · have hcond := evalExpr_sqrtLoopCond_true evm locals x z hx hz hlt
        have hbody := execBlock_sqrtLoopBody evm locals y x z hy hx hz (ne_of_gt hxpos)
        have hzpos : 0 < z := by omega
        have hmeasure : x.toNat < fuel := by
          rw [← hzFuel]
          exact (Int.toNat_lt_toNat hzpos).mpr hlt
        obtain ⟨locals', result, hwhile, hzFinal, hresultNonneg, hresultFuel⟩ :=
          ih x.toNat hmeasure
            (sqrtLoopAfterBodyStore locals y x) (sqrtLoopNextX y x) x rfl
            (sqrtLoopNextX_pos y x hypos hxpos) (by omega)
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
  obtain ⟨locals', result, hwhile, hzFinal⟩ :=
    execStmt_sqrtLoopTerminates evm (sqrtFunctionYInt y) hypos y.toNat
      (sqrtFunctionAfterInitStore y) (sqrtFunctionInitialX y) (sqrtFunctionYInt y)
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_pos y) (by simp [sqrtFunctionYInt])
      (sqrtFunctionAfterInitStore_y y) (sqrtFunctionAfterInitStore_x y)
      (sqrtFunctionAfterInitStore_z y)
  refine ⟨locals', result, ExecFuncBody.execBlockRet ?_⟩
  change ExecBlock config { contract := contract, locals := sqrtFunctionCallStore y } evm
    [ .ite (.binary .gt (.var "y") (.intLit 3))
        [ .letDecl "z" (some uint256) (.var "y"),
          .letDecl "x" (some uint256)
            (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary .div
                  (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_sqrtFunction_outer_true evm y hlarge) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_y evm y)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_initX evm y)) ?_
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
  obtain ⟨locals', result, hwhile, hzFinal, hresultNonneg, hresultFuel⟩ :=
    execStmt_sqrtLoopTerminates_bound evm (sqrtFunctionYInt y) hypos y.toNat
      (sqrtFunctionAfterInitStore y) (sqrtFunctionInitialX y) (sqrtFunctionYInt y)
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_pos y) (by simp [sqrtFunctionYInt])
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
            (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary .div
                  (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_sqrtFunction_outer_true evm y hlarge) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_y evm y)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_initX evm y)) ?_
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
