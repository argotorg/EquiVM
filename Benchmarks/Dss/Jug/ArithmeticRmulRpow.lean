import Benchmarks.Dss.Jug.ArithmeticAddDiff
import Benchmarks.Dss.Jug.ArithmeticRpowLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

theorem execRmulFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size)
    (hq : q = UInt256.div prod jugRay) :
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
              .ok (.bool true) := by
        exact evalExpr_eq_int_true hDivY hxZ rfl
      exact evalExpr_or_false_right hyEqZero hRight
  have hRayLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit one) =
        .ok (.int (Int.ofNat jugRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_jugRay_toNat]
  have hDivRay :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "z") (.intLit one)) = .ok (.int (Int.ofNat q.toNat)) :=
    evalExpr_div_uint256_ok hzZ hRayLit (by decide +native) hq
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
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsQ } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivRay hAssign) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzQ))
  simpa [rmulFunction, checkedMulUintInto, locals, localsZ, localsQ]
    using ExecFuncBody.execBlockRet hblock

theorem execRmulFunctionRevertMul (evm : EVM.State) {x y : UInt256}
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
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [rmulFunction, checkedMulUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem execRpowFunctionReturnXNonzeroNZero (evm : EVM.State) {x b : UInt256}
    (hxz : x ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x ⟨0⟩ b } evm
      rpowFunction.body
      (.returned
        { contract := contract,
          locals := rpowLocalsZHN x ⟨0⟩ b b (UInt256.div b ⟨2⟩) ⟨0⟩ } evm
        (some [.int (Int.ofNat b.toNat)])) := by
  let locals := uintTernaryLocals x ⟨0⟩ b
  let half := UInt256.div b ⟨2⟩
  let localsZ := rpowLocalsZ x ⟨0⟩ b b
  let localsZH := rpowLocalsZH x ⟨0⟩ b b half
  let localsDone := rpowLocalsZHN x ⟨0⟩ b b half ⟨0⟩
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x ⟨0⟩ b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_n x ⟨0⟩ b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "b") (value := b) (uintTernaryLocals_get_b x ⟨0⟩ b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) = .ok (.int 0) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [jugUInt256Two_toNat])
      (by simp [jugUInt256Two_toNat])
  have hModEq :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) :=
    evalExpr_eq_int_true hMod hzeroLit rfl
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "b") (.var "x")) = .ok (.int (Int.ofNat b.toNat)) :=
    evalExpr_ite_true hModEq hb
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "b") (value := b) (rpowLocalsZ_get_b x ⟨0⟩ b b)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "b") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by decide +native) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [localsZH, half] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := (⟨0⟩ : UInt256))
      (rpowLocalsZH_get_n x ⟨0⟩ b b half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsZH)
      (x := .var "n") (y := .intLit 2) (a := (⟨0⟩ : UInt256)) (b := (⟨2⟩ : UInt256))
      (q := (⟨0⟩ : UInt256)) hnZH htwoLitZH jugUInt256Two_ne_zero
      (by simp [jugUInt256DivZeroTwo])
    simpa using h
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) =
        .ok ({ contract := contract, locals := localsDone }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsDone,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
  have hnDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [localsDone] using evalExpr_varUInt256 (evm := evm)
      (locals := localsDone) (name := "n") (value := (⟨0⟩ : UInt256))
      (rpowLocalsZHN_get_n x ⟨0⟩ b b half ⟨0⟩)
  have hzeroLitDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hWhileCond :
      evalExpr? config { contract := contract, locals := localsDone } evm
        (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
    evalExpr_ne_int_false hnDone hzeroLitDone rfl
  have hzDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.var "z") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsDone, half] using evalExpr_varUInt256 (evm := evm)
      (locals := localsDone) (name := "z") (value := b)
      (rpowLocalsZHN_get_z x ⟨0⟩ b b half ⟨0⟩)
  have hElseBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256)
            (.ite
              (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
              (.var "b")
              (.var "x")),
          .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
          .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
          .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsDone } evm
          (some [.int (Int.ofNat b.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    refine ExecBlock.consNormal (ExecStmt.whileFalse hWhileCond) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzDone))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := localsDone } evm
          (some [.int (Int.ofNat b.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hxZero hElseBlock)
  simpa [locals, localsDone, half] using ExecFuncBody.execBlockRet hblock

theorem execRpowFunctionReturnXNonzeroNOne (evm : EVM.State) {x b : UInt256}
    (hxz : x ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x ⟨1⟩ b } evm
      rpowFunction.body
      (.returned
        { contract := contract,
          locals := rpowLocalsZHN x ⟨1⟩ b x (UInt256.div b ⟨2⟩) ⟨0⟩ } evm
        (some [.int (Int.ofNat x.toNat)])) := by
  let locals := uintTernaryLocals x ⟨1⟩ b
  let half := UInt256.div b ⟨2⟩
  let localsZ := rpowLocalsZ x ⟨1⟩ b x
  let localsZH := rpowLocalsZH x ⟨1⟩ b x half
  let localsDone := rpowLocalsZHN x ⟨1⟩ b x half ⟨0⟩
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x ⟨1⟩ b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := (⟨1⟩ : UInt256))
      (uintTernaryLocals_get_n x ⟨1⟩ b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "b") (value := b) (uintTernaryLocals_get_b x ⟨1⟩ b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) = .ok (.int 1) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [jugUInt256Two_toNat])
      (by simp [jugUInt256One_toNat, jugUInt256Two_toNat])
  have hModEq :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool false) := by
    apply evalExpr_eq_int_false hMod hzeroLit
    norm_num
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "b") (.var "x")) = .ok (.int (Int.ofNat x.toNat)) :=
    evalExpr_ite_false hModEq hx
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "b") (value := b) (rpowLocalsZ_get_b x ⟨1⟩ b x)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "b") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by decide +native) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by
    simpa [localsZH, half] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := (⟨1⟩ : UInt256))
      (rpowLocalsZH_get_n x ⟨1⟩ b x half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsZH)
      (x := .var "n") (y := .intLit 2) (a := (⟨1⟩ : UInt256)) (b := (⟨2⟩ : UInt256))
      (q := (⟨0⟩ : UInt256)) hnZH htwoLitZH jugUInt256Two_ne_zero
      (by simp [jugUInt256DivOneTwo])
    simpa using h
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) =
        .ok ({ contract := contract, locals := localsDone }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsDone,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
  have hnDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [localsDone] using evalExpr_varUInt256 (evm := evm)
      (locals := localsDone) (name := "n") (value := (⟨0⟩ : UInt256))
      (rpowLocalsZHN_get_n x ⟨1⟩ b x half ⟨0⟩)
  have hzeroLitDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hWhileCond :
      evalExpr? config { contract := contract, locals := localsDone } evm
        (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
    evalExpr_ne_int_false hnDone hzeroLitDone rfl
  have hzDone :
      evalExpr? config { contract := contract, locals := localsDone } evm (.var "z") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsDone, half] using evalExpr_varUInt256 (evm := evm)
      (locals := localsDone) (name := "z") (value := x)
      (rpowLocalsZHN_get_z x ⟨1⟩ b x half ⟨0⟩)
  have hElseBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256)
            (.ite
              (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
              (.var "b")
              (.var "x")),
          .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
          .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
          .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsDone } evm
          (some [.int (Int.ofNat x.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    refine ExecBlock.consNormal (ExecStmt.whileFalse hWhileCond) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzDone))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := localsDone } evm
          (some [.int (Int.ofNat x.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hxZero hElseBlock)
  simpa [locals, localsDone, half] using ExecFuncBody.execBlockRet hblock

theorem execRpowFunctionReturnXZeroNZero (evm : EVM.State) {b : UInt256} :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals ⟨0⟩ ⟨0⟩ b } evm
      rpowFunction.body
      (.returned { contract := contract, locals := uintTernaryLocals ⟨0⟩ ⟨0⟩ b } evm
        (some [.int (Int.ofNat b.toNat)])) := by
  let locals := uintTernaryLocals ⟨0⟩ ⟨0⟩ b
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_x ⟨0⟩ ⟨0⟩ b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_n ⟨0⟩ ⟨0⟩ b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "b") (value := b)
      (uintTernaryLocals_get_b ⟨0⟩ ⟨0⟩ b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) :=
    evalExpr_eq_int_true hx hzeroLit rfl
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool true) :=
    evalExpr_eq_int_true hn hzeroLit rfl
  have hinner :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .eq (.var "n") (.intLit 0))
            [ .return [.var "b"] ]
            [ .return [.intLit 0] ] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat b.toNat)])) := by
    exact ExecBlock.consReturn (ExecStmt.iteTrue hnZero
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hb))))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat b.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hxZero hinner)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

theorem execRpowFunctionReturnXZeroNNonzero (evm : EVM.State) {n b : UInt256}
    (hnz : n ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals ⟨0⟩ n b } evm
      rpowFunction.body
      (.returned { contract := contract, locals := uintTernaryLocals ⟨0⟩ n b } evm
        (some [.int 0])) := by
  let locals := uintTernaryLocals ⟨0⟩ n b
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_x ⟨0⟩ n b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n)
      (uintTernaryLocals_get_n ⟨0⟩ n b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hzeroRet :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) :=
    evalExpr_eq_int_true hx hzeroLit rfl
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hn hzeroLit
    intro hbad
    exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hinner :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .eq (.var "n") (.intLit 0))
            [ .return [.var "b"] ]
            [ .return [.intLit 0] ] ]
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) := by
    exact ExecBlock.consReturn (ExecStmt.iteFalse hnZero
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzeroRet))))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hxZero hinner)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

end Benchmarks.Dss.Jug
