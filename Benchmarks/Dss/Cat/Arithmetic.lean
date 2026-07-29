import Benchmarks.Dss.Cat.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-!
# Cat DSMath / min internal helpers (Solm-side `ExecFuncBody` + `evalExpr` facts)

`min` (used by `bite`) and `sub` (used by `claw`) are proved as `ExecFuncBody`; the `add`/`sub`/`mul`
helpers are also inlined in `bite` (`checkedAddUintInto`/…), so the `evalExpr_*` overflow facts here
are reused directly there. `add`/`mul` are never *called* as functions (always inlined), so no
`ExecFuncBody` is needed for them.
-/

namespace Benchmarks.Dss.Cat

/-! ## `evalExpr` scalar / arithmetic facts -/

theorem evalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_sub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) = .revert := by
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro hle
  exact False.elim (not_le.mpr hlt hle)

theorem evalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

theorem evalExpr_le_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

theorem evalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_gt_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hgt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .gt lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hgt

theorem evalExpr_gt_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .gt lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

/-! ## Local-store helpers -/

abbrev uintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev uintBinaryLocalsZ (x y z : UInt256) : Store :=
  (uintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem uintBinaryLocals_get_x (x y : UInt256) :
    (uintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocals, store_get_self]

theorem uintBinaryLocals_get_y (x y : UInt256) :
    (uintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintBinaryLocalsZ_get_x (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_x]

theorem uintBinaryLocalsZ_get_z (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_self]

/-! ## `sub` internal function (used by `claw`) -/

theorem execSubFunctionReturn (evm : EVM.State) {x y diff : UInt256}
    (hdiff : diff = UInt256.sub x y) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      subFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZ x y diff } evm
        (some [.int (Int.ofNat diff.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y diff
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hSub :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat diff.toNat)) :=
    evalExpr_sub256_ok hx hy hdiff hle
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := diff) (uintBinaryLocalsZ_get_z x y diff)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x) (uintBinaryLocalsZ_get_x x y diff)
  have hdiffNat : diff.toNat = x.toNat - y.toNat := by
    rw [hdiff, usub_toNat hle]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "z") (.var "x")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hz hxZ (by rw [hdiffNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat diff.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hSub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [subFunction, checkedSubUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execSubFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      subFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hSubRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .revert :=
    evalExpr_sub256_revert hx hy hlt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hSubRev)
  simpa [subFunction, checkedSubUintInto, locals] using ExecFuncBody.execBlockRevert hblock

/-! ## `min` internal function (used by `bite`)

`min(x,y) = if (x > y) return y else return x`.  Returns directly in each branch (no `z` local), so
the result frame keeps `uintBinaryLocals x y`. -/

theorem execMinFunctionReturnY (evm : EVM.State) {x y : UInt256}
    (hgt : y.toNat < x.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      minFunction.body
      (.returned { contract := contract, locals := uintBinaryLocals x y } evm
        (some [.int (Int.ofNat y.toNat)])) := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.var "x") (.var "y")) = .ok (.bool true) :=
    evalExpr_gt_uint256_true hx hy hgt
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .return [.var "y"] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat y.toNat)])) :=
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hy))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .gt (.var "x") (.var "y")) [ .return [.var "y"] ] [ .return [.var "x"] ] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat y.toNat)])) :=
    ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
  simpa [minFunction, locals] using ExecFuncBody.execBlockRet hblock

theorem execMinFunctionReturnX (evm : EVM.State) {x y : UInt256}
    (hle : x.toNat ≤ y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      minFunction.body
      (.returned { contract := contract, locals := uintBinaryLocals x y } evm
        (some [.int (Int.ofNat x.toNat)])) := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.var "x") (.var "y")) = .ok (.bool false) :=
    evalExpr_gt_uint256_false hx hy hle
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .return [.var "x"] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat x.toNat)])) :=
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hx))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .gt (.var "x") (.var "y")) [ .return [.var "y"] ] [ .return [.var "x"] ] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat x.toNat)])) :=
    ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)
  simpa [minFunction, locals] using ExecFuncBody.execBlockRet hblock

end Benchmarks.Dss.Cat
