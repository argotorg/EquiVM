import Benchmarks.Dss.Jug.ArithmeticLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

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
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hAddRev)
  simpa [addFunction, checkedAddUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem execDiffFunctionReturn (evm : EVM.State) {x y : UInt256}
    (hxMax : (x.toNat : Int) ≤ maxInt256) (hyMax : (y.toNat : Int) ≤ maxInt256) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body
      (.returned
        { contract := contract,
          locals := uintBinaryLocalsIntZ x y ((x.toNat : Int) - (y.toNat : Int)) } evm
        (some [.int ((x.toNat : Int) - (y.toNat : Int))])) := by
  let locals := uintBinaryLocals x y
  let z : Int := (x.toNat : Int) - (y.toNat : Int)
  let localsZ := uintBinaryLocalsIntZ x y z
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
        (.binary .sub (.var "x") (.var "y")) = .ok (.int z) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, z]
  have hLo : -((2 : Int) ^ 255) ≤ z := by
    have hxNonneg : 0 ≤ (x.toNat : Int) := Int.natCast_nonneg _
    have hyLe : (y.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
      simpa [maxInt256] using hyMax
    dsimp [z]
    omega
  have hHi : z < (2 : Int) ^ 255 := by
    have hyNonneg : 0 ≤ (y.toNat : Int) := Int.natCast_nonneg _
    have hxLe : (x.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
      simpa [maxInt256] using hxMax
    dsimp [z]
    omega
  have hLetZ :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .sub (.var "x") (.var "y"))) = .ok (.int z) :=
    evalExpr_s256_ok hSub hLo hHi
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "x") (value := Int.ofNat x.toNat)
      (uintBinaryLocalsIntZ_get_x x y z)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "y") (value := Int.ofNat y.toNat)
      (uintBinaryLocalsIntZ_get_y x y z)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int z) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "z") (value := z)
      (uintBinaryLocalsIntZ_get_z x y z)
  have hMaxLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit maxInt256) =
        .ok (.int maxInt256) := by
    simp [evalExpr?, pure]
  have hReqX :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "x") (.intLit maxInt256)) = .ok (.bool true) :=
    evalExpr_le_int_true hxZ hMaxLit hxMax
  have hReqY :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "y") (.intLit maxInt256)) = .ok (.bool true) :=
    evalExpr_le_int_true hyZ hMaxLit hyMax
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256) (s256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm (some [.int z])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetZ) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReqX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReqY) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRet hblock

theorem execDiffFunctionRevertCast (evm : EVM.State) {x y : UInt256}
    (hbad : (x.toNat : Int) - (y.toNat : Int) < -((2 : Int) ^ 255) ∨
      (x.toNat : Int) - (y.toNat : Int) ≥ (2 : Int) ^ 255) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  let z : Int := (x.toNat : Int) - (y.toNat : Int)
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
        (.binary .sub (.var "x") (.var "y")) = .ok (.int z) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, z]
  have hLetRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .sub (.var "x") (.var "y"))) = .revert := by
    exact evalExpr_s256_revert hSub (by simpa [z] using hbad)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256) (s256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hLetRev)
  simpa [diffFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem execDiffFunctionRevertXBound (evm : EVM.State) {x y : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ (x.toNat : Int) - (y.toNat : Int))
    (hhi : (x.toNat : Int) - (y.toNat : Int) < (2 : Int) ^ 255)
    (hxGt : maxInt256 < (x.toNat : Int)) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  let z : Int := (x.toNat : Int) - (y.toNat : Int)
  let localsZ := uintBinaryLocalsIntZ x y z
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
        (.binary .sub (.var "x") (.var "y")) = .ok (.int z) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, z]
  have hLetZ :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .sub (.var "x") (.var "y"))) = .ok (.int z) :=
    evalExpr_s256_ok hSub (by simpa [z] using hlo) (by simpa [z] using hhi)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "x") (value := Int.ofNat x.toNat)
      (uintBinaryLocalsIntZ_get_x x y z)
  have hMaxLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit maxInt256) =
        .ok (.int maxInt256) := by
    simp [evalExpr?, pure]
  have hReqX :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "x") (.intLit maxInt256)) = .ok (.bool false) :=
    evalExpr_le_int_false hxZ hMaxLit hxGt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256) (s256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetZ) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hReqX)
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRevert hblock

theorem execDiffFunctionRevertYBound (evm : EVM.State) {x y : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ (x.toNat : Int) - (y.toNat : Int))
    (hhi : (x.toNat : Int) - (y.toNat : Int) < (2 : Int) ^ 255)
    (hxMax : (x.toNat : Int) ≤ maxInt256) (hyGt : maxInt256 < (y.toNat : Int)) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  let z : Int := (x.toNat : Int) - (y.toNat : Int)
  let localsZ := uintBinaryLocalsIntZ x y z
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
        (.binary .sub (.var "x") (.var "y")) = .ok (.int z) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, z]
  have hLetZ :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .sub (.var "x") (.var "y"))) = .ok (.int z) :=
    evalExpr_s256_ok hSub (by simpa [z] using hlo) (by simpa [z] using hhi)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "x") (value := Int.ofNat x.toNat)
      (uintBinaryLocalsIntZ_get_x x y z)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_varInt (evm := evm)
      (locals := localsZ) (name := "y") (value := Int.ofNat y.toNat)
      (uintBinaryLocalsIntZ_get_y x y z)
  have hMaxLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit maxInt256) =
        .ok (.int maxInt256) := by
    simp [evalExpr?, pure]
  have hReqX :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "x") (.intLit maxInt256)) = .ok (.bool true) :=
    evalExpr_le_int_true hxZ hMaxLit hxMax
  have hReqY :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "y") (.intLit maxInt256)) = .ok (.bool false) :=
    evalExpr_le_int_false hyZ hMaxLit hyGt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256) (s256 (.binary .sub (.var "x") (.var "y"))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetZ) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReqX) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hReqY)
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Jug
