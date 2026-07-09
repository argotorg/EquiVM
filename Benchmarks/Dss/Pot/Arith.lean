import Benchmarks.Dss.Pot.ArithExpr

/-!
# MakerDAO/Sky DSS Pot internal arithmetic helpers (`_add`, `_sub`, `_mul`, `_rmul`)

Source-level (`ExecFuncBody`) return/revert lemmas for Pot's four checked-arithmetic internal
functions.  `_add` mirrors Jug's `_add` verbatim; `_sub` uses Pot's simple truncating `sub256`
(reverting on underflow — Pot has no signed `_diff`); `_mul` is the checked multiply; and `_rmul`
composes a genuine `.internalCall "_mul"` (discharged with `internalCallFunctionReturn`/`Revert`)
followed by division by `ONE = 10^27`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-- `ONE = 10^27` as a machine word (Pot's ray scale, used by `_rmul`). -/
abbrev potRay : UInt256 := ⟨1000000000000000000000000000⟩

theorem potRay_toNat : potRay.toNat = 1000000000000000000000000000 := by
  change (UInt256.ofNat 1000000000000000000000000000).toNat = 1000000000000000000000000000
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem one_eq_potRay_toNat : one = Int.ofNat potRay.toNat := by
  simp [one, potRay_toNat]

theorem potRay_ne_zero : potRay ≠ (⟨0⟩ : UInt256) := fun h => by
  have hz : potRay.toNat = 0 := by rw [h]; rfl
  rw [potRay_toNat] at hz
  exact absurd hz (by norm_num)

/-! ## `_add(x, y)` : checked addition -/

theorem execAddFunctionReturn (evm : EVM.State) {x y sum : UInt256}
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      addFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZ x y sum } evm
        (some [.int (Int.ofNat sum.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y sum
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
  have hAdd :
      evalExpr? config { contract := contract, locals := locals } evm
        (add256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat sum.toNat)) :=
    evalExpr_add256_ok hx hy hsum hfit
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := sum) (uintBinaryLocalsZ_get_z x y sum)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x) (uintBinaryLocalsZ_get_x x y sum)
  have hsumNat : sum.toNat = x.toNat + y.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .ge (.var "z") (.var "x")) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hz hxZ (by rw [hsumNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (add256 (.var "x") (.var "y")),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat sum.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hAdd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [addFunction, checkedAddUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execAddFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      addFunction.body .reverted := by
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
  have hAddRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (add256 (.var "x") (.var "y")) = .revert :=
    evalExpr_add256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (add256 (.var "x") (.var "y")),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.letDeclRevert hAddRev)
  simpa [addFunction, checkedAddUintInto, locals] using ExecFuncBody.execBlockRevert hblock

/-! ## `_sub(x, y)` : truncating checked subtraction (reverts on underflow) -/

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
        .reverted :=
    ExecBlock.consRevert (ExecStmt.letDeclRevert hSubRev)
  simpa [subFunction, checkedSubUintInto, locals] using ExecFuncBody.execBlockRevert hblock

/-! ## `_mul(x, y)` : checked multiplication -/

theorem execMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y prod
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
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x) (uintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y) (uintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod) (uintBinaryLocalsZ_get_z x y prod)
  have hZeroLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .or
          (.binary .eq (.var "y") (.intLit 0))
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
        .ok (.bool true) := by
    by_cases hy0 : y = (⟨0⟩ : UInt256)
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact evalExpr_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_eq_int_false hyZ hZeroLit
        intro hbad
        exact hy0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hyNatNe : y.toNat ≠ 0 := by
        intro hzero
        exact hy0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div prod y = x := by
        apply u256_inj
        rw [udiv_toNat]
        have hprodNat : prod.toNat = x.toNat * y.toNat := by
          rw [hprod, umul_toNat x y hfit]
        rw [hprodNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)
      have hDivY :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) :=
        evalExpr_eq_int_true hDivY hxZ rfl
      exact evalExpr_or_false_right hyEqZero hRight
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, checkedMulUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      mulFunction.body .reverted := by
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
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .revert :=
    evalExpr_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [mulFunction, checkedMulUintInto, locals] using ExecFuncBody.execBlockRevert hblock

/-! ## `_rmul(x, y)` : `_mul(x, y) / ONE` (composes an internal call to `_mul`) -/

theorem execRmulFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size)
    (hq : q = UInt256.div prod potRay) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZAssigned x y prod q } evm
        (some [.int (Int.ofNat q.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y prod
  let localsQ := uintBinaryLocalsZAssigned x y prod q
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
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, EvalResult.bind, bind, pure, hx, hy]
  have hlookup : lookupCallable? contract "_mul" = some mulFunction.toCallable := by rfl
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] = some locals := by
    simp [mulFunction, uintBinaryLocals, bindParams?, locals]
  have hcallBody :
      ExecFuncBody config { contract := contract, locals := locals } evm mulFunction.body
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) :=
    execMulFunctionReturn evm hprod hfit
  have hMulCall :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "_mul" [.var "x", .var "y"] "z")
        (.ok { contract := contract, locals := localsZ } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (calleeEvm := evm) (name := "_mul") (retVar := "z")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := locals)
      (calleeSolm := { contract := contract, locals := localsZ })
      (value := some [.int (Int.ofNat prod.toNat)])
      hargs hlookup hbind hcallBody
    simpa [resumeAfterInternalCall, collapseReturns, localsZ, uintBinaryLocalsZ, locals] using h
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod) (uintBinaryLocalsZ_get_z x y prod)
  have hRayLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit one) =
        .ok (.int (Int.ofNat potRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_potRay_toNat]
  have hDivRay :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "z") (.intLit one)) = .ok (.int (Int.ofNat q.toNat)) :=
    evalExpr_div_uint256_ok hzZ hRayLit potRay_ne_zero hq
  have hAssign :
      assignStorageRef? config { contract := contract, locals := localsZ } evm .localVar
          { base := "z" } (.int (Int.ofNat q.toNat)) =
        .ok ({ contract := contract, locals := localsQ }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsQ,
      uintBinaryLocalsZAssigned, localsZ, uintBinaryLocalsZ]
  have hzQ :
      evalExpr? config { contract := contract, locals := localsQ } evm (.var "z") =
        .ok (.int (Int.ofNat q.toNat)) := by
    simpa [localsQ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsQ) (name := "z") (value := q)
      (uintBinaryLocalsZAssigned_get_z x y prod q)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "_mul" [.var "x", .var "y"] "z",
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsQ } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal hMulCall ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivRay hAssign) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzQ))
  simpa [rmulFunction, locals, localsZ, localsQ] using ExecFuncBody.execBlockRet hblock

theorem execRmulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      rmulFunction.body .reverted := by
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
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, EvalResult.bind, bind, pure, hx, hy]
  have hlookup : lookupCallable? contract "_mul" = some mulFunction.toCallable := by rfl
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] = some locals := by
    simp [mulFunction, uintBinaryLocals, bindParams?, locals]
  have hcallRev :
      ExecFuncBody config { contract := contract, locals := locals } evm mulFunction.body
        .reverted :=
    execMulFunctionRevert evm hover
  have hMulCall :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "_mul" [.var "x", .var "y"] "z") .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "_mul") (retVar := "z")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := locals)
      hargs hlookup hbind hcallRev
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "_mul" [.var "x", .var "y"] "z",
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
          .return [.var "z"] ]
        .reverted :=
    ExecBlock.consRevert hMulCall
  simpa [rmulFunction, locals] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Pot
