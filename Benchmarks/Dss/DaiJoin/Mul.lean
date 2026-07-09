import Benchmarks.Dss.DaiJoin.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

abbrev daiJoinONEWord : UInt256 :=
  UInt256.ofNat ONE.natAbs

abbrev daiJoinRadWord (wad : UInt256) : UInt256 :=
  UInt256.mul daiJoinONEWord wad

theorem daiJoinONEWord_toNat :
    daiJoinONEWord.toNat = 1000000000000000000000000000 := by
  native_decide

theorem daiJoinONE_eq_ONEWord_toNat :
    ONE = Int.ofNat daiJoinONEWord.toNat := by
  simp [ONE, daiJoinONEWord_toNat]

abbrev daiJoinUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev daiJoinUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (daiJoinUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem daiJoinUintBinaryLocals_get_x (x y : UInt256) :
    (daiJoinUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [daiJoinUintBinaryLocals, store_get_self]

theorem daiJoinUintBinaryLocals_get_y (x y : UInt256) :
    (daiJoinUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [daiJoinUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem daiJoinUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (daiJoinUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [daiJoinUintBinaryLocalsZ, store_get_ne _ _ (by decide),
    daiJoinUintBinaryLocals_get_x]

theorem daiJoinUintBinaryLocalsZ_get_y (x y z : UInt256) :
    (daiJoinUintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [daiJoinUintBinaryLocalsZ, store_get_ne _ _ (by decide),
    daiJoinUintBinaryLocals_get_y]

theorem daiJoinUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (daiJoinUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [daiJoinUintBinaryLocalsZ, store_get_self]

theorem evalExpr_daiJoin_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_daiJoin_mul256_ok {evm : EVM.State} {locals : Store}
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
    rw [hprod, umul_toNat a b hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_daiJoin_mul256_revert {evm : EVM.State} {locals : Store}
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

theorem evalExpr_daiJoin_div_uint256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem evalExpr_daiJoin_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_daiJoin_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_daiJoin_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_daiJoin_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem daiJoinMulGuard_of_fit {x y : UInt256}
    (hy : y ≠ ⟨0⟩) (hfit : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  have hyNatNe : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simpa [Nat.mul_comm] using
    Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)

theorem daiJoinMulOverflow_of_guard_fail {x y : UInt256}
    (hy : y ≠ ⟨0⟩)
    (hguard : UInt256.div (UInt256.mul x y) y ≠ x) :
    UInt256.size ≤ x.toNat * y.toNat := by
  by_contra hnot
  exact hguard (daiJoinMulGuard_of_fit hy (Nat.lt_of_not_ge hnot))

theorem daiJoinMulGuard_ne_of_overflow (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul x y) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_toNat] at hnat
  have hremLt : x.toNat * y.toNat % UInt256.size < x.toNat * y.toNat := by
    have hmodLt : x.toNat * y.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    omega
  have hle0 :=
    Nat.mul_div_le (x.toNat * y.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : x.toNat * y.toNat ≤ x.toNat * y.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem daiJoinMulFit_of_guard {x y : UInt256}
    (hguard : UInt256.div (UInt256.mul x y) y = x) :
    x.toNat * y.toNat < UInt256.size := by
  by_contra hnot
  exact (daiJoinMulGuard_ne_of_overflow x y (Nat.le_of_not_gt hnot)) hguard

theorem execDaiJoinMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := daiJoinUintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := daiJoinUintBinaryLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := daiJoinUintBinaryLocals x y
  let localsZ := daiJoinUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (daiJoinUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (daiJoinUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_daiJoin_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (daiJoinUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (daiJoinUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (daiJoinUintBinaryLocalsZ_get_z x y prod)
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
        apply evalExpr_daiJoin_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact evalExpr_daiJoin_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_daiJoin_eq_int_false hyZ hZeroLit
        intro hbad
        exact hy0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hdivWord : UInt256.div prod y = x := by
        rw [hprod]
        exact daiJoinMulGuard_of_fit hy0 hfit
      have hDivY :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := evalExpr_daiJoin_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact evalExpr_daiJoin_eq_int_true hDivY hxZ rfl
      exact evalExpr_daiJoin_or_false_right hyEqZero hRight
  have hzRet :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := hzZ
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm mulFunction.body
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzRet))
  simpa [locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execDaiJoinMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := daiJoinUintBinaryLocals x y } evm
      mulFunction.body .reverted := by
  let locals := daiJoinUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (daiJoinUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_daiJoin_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (daiJoinUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .revert :=
    evalExpr_daiJoin_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm mulFunction.body
        .reverted := by
    simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [locals] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinMulRoutine_success {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256}
    (h : RD code ee g s0 ⟨1678⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hguard : y = ⟨0⟩ ∨ UInt256.div (UInt256.mul x y) y = x)
    (hret : (D_J code 0).contains ret = true)
    (hshape :
      decode code ⟨1678⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1679⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
      decode code ⟨1681⟩ = some (.DUP2, .none) ∧
      decode code ⟨1682⟩ = some (.ISZERO, .none) ∧
      decode code ⟨1683⟩ = some (.DUP1, .none) ∧
      decode code ⟨1684⟩ = some (.Push .PUSH2, some (⟨1705⟩, 2)) ∧
      decode code ⟨1687⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1688⟩ = some (.POP, .none) ∧
      decode code ⟨1689⟩ = some (.POP, .none) ∧
      decode code ⟨1690⟩ = some (.DUP1, .none) ∧
      decode code ⟨1691⟩ = some (.DUP3, .none) ∧
      decode code ⟨1692⟩ = some (.MUL, .none) ∧
      decode code ⟨1693⟩ = some (.DUP3, .none) ∧
      decode code ⟨1694⟩ = some (.DUP3, .none) ∧
      decode code ⟨1695⟩ = some (.DUP3, .none) ∧
      decode code ⟨1696⟩ = some (.DUP2, .none) ∧
      decode code ⟨1697⟩ = some (.Push .PUSH2, some (⟨1702⟩, 2)) ∧
      decode code ⟨1700⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1702⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1703⟩ = some (.DIV, .none) ∧
      decode code ⟨1704⟩ = some (.EQ, .none) ∧
      decode code ⟨1705⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1706⟩ = some (.Push .PUSH2, some (⟨1714⟩, 2)) ∧
      decode code ⟨1709⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1714⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1715⟩ = some (.SWAP3, .none) ∧
      decode code ⟨1716⟩ = some (.SWAP2, .none) ∧
      decode code ⟨1717⟩ = some (.POP, .none) ∧
      decode code ⟨1718⟩ = some (.POP, .none) ∧
      decode code ⟨1719⟩ = some (.JUMP, .none) ∧
      (D_J code 0).contains ⟨1705⟩ = true ∧
      (D_J code 0).contains ⟨1702⟩ = true ∧
      (D_J code 0).contains ⟨1714⟩ = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (UInt256.mul x y :: R) mem aw rdata acc k' C' := by
  rcases hshape with
    ⟨hd1678, hd1679, hd1681, hd1682, hd1683, hd1684, hd1687, hd1688, hd1689,
      hd1690, hd1691, hd1692, hd1693, hd1694, hd1695, hd1696, hd1697, hd1700,
      hd1702, hd1703, hd1704, hd1705, hd1706, hd1709, hd1714, hd1715, hd1716,
      hd1717, hd1718, hd1719, hjd1705, hjd1702, hjd1714⟩
  by_cases hy : y = ⟨0⟩
  · subst y
    have rd1687 := evm_run h with [
      raw jumpdest hd1678 (by evm_ov),
      raw push1 ⟨0⟩ hd1679 (by evm_ov),
      raw dup2 hd1681 (by evm_ov),
      raw iszero hd1682 (by evm_ov),
      raw dup1 hd1683 (by evm_ov),
      raw push2 ⟨1705⟩ hd1684 (by evm_ov)]
    have rd1705 := rd1687.jumpiT hd1687 (by decide) hjd1705 (by evm_ov)
    have rd1709 := evm_run rd1705 with [
      raw jumpdest hd1705 (by evm_ov),
      raw push2 ⟨1714⟩ hd1706 (by evm_ov)]
    have rd1714 := rd1709.jumpiT hd1709 (by decide) hjd1714 (by evm_ov)
    have rd1719 := evm_run rd1714 with [
      raw jumpdest hd1714 (by evm_ov),
      raw swap3 hd1715 (by evm_ov),
      raw swap2 hd1716 (by evm_ov),
      raw pop hd1717 (by evm_ov),
      raw pop hd1718 (by evm_ov)]
    have rdret := RD.jump (a := ret) (t := UInt256.mul x ⟨0⟩ :: R) rd1719
      hd1719 hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩
  · have hIsZero : UInt256.isZero y = ⟨0⟩ :=
      Reasoning.Theory.isZero_eq_zero_of_ne hy
    have rd1687 := evm_run h with [
      raw jumpdest hd1678 (by evm_ov),
      raw push1 ⟨0⟩ hd1679 (by evm_ov),
      raw dup2 hd1681 (by evm_ov),
      raw iszero hd1682 (by evm_ov),
      raw dup1 hd1683 (by evm_ov),
      raw push2 ⟨1705⟩ hd1684 (by evm_ov)]
    rw [hIsZero] at rd1687
    have rd1688 := rd1687.jumpiNT hd1687 rfl (by evm_ov)
    have rd1700 := evm_run rd1688 with [
      raw pop hd1688 (by evm_ov),
      raw pop hd1689 (by evm_ov),
      raw dup1 hd1690 (by evm_ov),
      raw dup3 hd1691 (by evm_ov),
      raw mul hd1692 (by evm_ov),
      raw dup3 hd1693 (by evm_ov),
      raw dup3 hd1694 (by evm_ov),
      raw dup3 hd1695 (by evm_ov),
      raw dup2 hd1696 (by evm_ov),
      raw push2 ⟨1702⟩ hd1697 (by simp only [List.length_cons]; omega)]
    have rd1702 := rd1700.jumpiT hd1700 hy hjd1702 (by evm_ov)
    have rd1709 := evm_run rd1702 with [
      raw jumpdest hd1702 (by evm_ov),
      raw div hd1703 (by evm_ov),
      raw eq hd1704 (by evm_ov),
      raw jumpdest hd1705 (by evm_ov),
      raw push2 ⟨1714⟩ hd1706 (by evm_ov)]
    have hdiv : UInt256.div (UInt256.mul x y) y = x := by
      cases hguard with
      | inl hzero => contradiction
      | inr h => exact h
    rw [hdiv, u256_eq_refl] at rd1709
    have rd1714 := rd1709.jumpiT hd1709 one_ne_zero_uint hjd1714 (by evm_ov)
    have rd1719 := evm_run rd1714 with [
      raw jumpdest hd1714 (by evm_ov),
      raw swap3 hd1715 (by evm_ov),
      raw swap2 hd1716 (by evm_ov),
      raw pop hd1717 (by evm_ov),
      raw pop hd1718 (by evm_ov)]
    have rdret := RD.jump (a := ret) (t := UInt256.mul x y :: R) rd1719
      hd1719 hret (by evm_ov)
    exact ⟨_, _, rdret⟩

theorem daiJoinMulRoutine_revert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256}
    (h : RD code ee g s0 ⟨1678⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hy : y ≠ ⟨0⟩)
    (hguard : UInt256.div (UInt256.mul x y) y ≠ x)
    (hshape :
      decode code ⟨1678⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1679⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
      decode code ⟨1681⟩ = some (.DUP2, .none) ∧
      decode code ⟨1682⟩ = some (.ISZERO, .none) ∧
      decode code ⟨1683⟩ = some (.DUP1, .none) ∧
      decode code ⟨1684⟩ = some (.Push .PUSH2, some (⟨1705⟩, 2)) ∧
      decode code ⟨1687⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1688⟩ = some (.POP, .none) ∧
      decode code ⟨1689⟩ = some (.POP, .none) ∧
      decode code ⟨1690⟩ = some (.DUP1, .none) ∧
      decode code ⟨1691⟩ = some (.DUP3, .none) ∧
      decode code ⟨1692⟩ = some (.MUL, .none) ∧
      decode code ⟨1693⟩ = some (.DUP3, .none) ∧
      decode code ⟨1694⟩ = some (.DUP3, .none) ∧
      decode code ⟨1695⟩ = some (.DUP3, .none) ∧
      decode code ⟨1696⟩ = some (.DUP2, .none) ∧
      decode code ⟨1697⟩ = some (.Push .PUSH2, some (⟨1702⟩, 2)) ∧
      decode code ⟨1700⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1702⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1703⟩ = some (.DIV, .none) ∧
      decode code ⟨1704⟩ = some (.EQ, .none) ∧
      decode code ⟨1705⟩ = some (.JUMPDEST, .none) ∧
      decode code ⟨1706⟩ = some (.Push .PUSH2, some (⟨1714⟩, 2)) ∧
      decode code ⟨1709⟩ = some (.JUMPI, .none) ∧
      decode code ⟨1710⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
      decode code ⟨1712⟩ = some (.DUP1, .none) ∧
      decode code ⟨1713⟩ = some (.REVERT, .none) ∧
      (D_J code 0).contains ⟨1702⟩ = true)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hshape with
    ⟨hd1678, hd1679, hd1681, hd1682, hd1683, hd1684, hd1687, hd1688, hd1689,
      hd1690, hd1691, hd1692, hd1693, hd1694, hd1695, hd1696, hd1697, hd1700,
      hd1702, hd1703, hd1704, hd1705, hd1706, hd1709, hd1710, hd1712, hd1713,
      hjd1702⟩
  have hIsZero : UInt256.isZero y = ⟨0⟩ :=
    Reasoning.Theory.isZero_eq_zero_of_ne hy
  have rd1687 := evm_run h with [
    raw jumpdest hd1678 (by evm_ov),
    raw push1 ⟨0⟩ hd1679 (by evm_ov),
    raw dup2 hd1681 (by evm_ov),
    raw iszero hd1682 (by evm_ov),
    raw dup1 hd1683 (by evm_ov),
    raw push2 ⟨1705⟩ hd1684 (by evm_ov)]
  rw [hIsZero] at rd1687
  have rd1688 := rd1687.jumpiNT hd1687 rfl (by evm_ov)
  have rd1700 := evm_run rd1688 with [
    raw pop hd1688 (by evm_ov),
    raw pop hd1689 (by evm_ov),
    raw dup1 hd1690 (by evm_ov),
    raw dup3 hd1691 (by evm_ov),
    raw mul hd1692 (by evm_ov),
    raw dup3 hd1693 (by evm_ov),
    raw dup3 hd1694 (by evm_ov),
    raw dup3 hd1695 (by evm_ov),
    raw dup2 hd1696 (by evm_ov),
    raw push2 ⟨1702⟩ hd1697 (by simp only [List.length_cons]; omega)]
  have rd1702 := rd1700.jumpiT hd1700 hy hjd1702 (by evm_ov)
  have rd1709 := evm_run rd1702 with [
    raw jumpdest hd1702 (by evm_ov),
    raw div hd1703 (by evm_ov),
    raw eq hd1704 (by evm_ov),
    raw jumpdest hd1705 (by evm_ov),
    raw push2 ⟨1714⟩ hd1706 (by evm_ov)]
  have heq0 : UInt256.eq (UInt256.div (UInt256.mul x y) y) x = ⟨0⟩ := by
    exact u256_eq_of_ne hguard
  rw [heq0] at rd1709
  have rd1710 := rd1709.jumpiNT hd1709 rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd1710 hd1710 hd1712 hd1713 (by evm_ov)

theorem daiJoinMulRoutine_shape :
    decode daiJoinBytecode ⟨1678⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1679⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
    decode daiJoinBytecode ⟨1681⟩ = some (.DUP2, .none) ∧
    decode daiJoinBytecode ⟨1682⟩ = some (.ISZERO, .none) ∧
    decode daiJoinBytecode ⟨1683⟩ = some (.DUP1, .none) ∧
    decode daiJoinBytecode ⟨1684⟩ = some (.Push .PUSH2, some (⟨1705⟩, 2)) ∧
    decode daiJoinBytecode ⟨1687⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1688⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1689⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1690⟩ = some (.DUP1, .none) ∧
    decode daiJoinBytecode ⟨1691⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1692⟩ = some (.MUL, .none) ∧
    decode daiJoinBytecode ⟨1693⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1694⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1695⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1696⟩ = some (.DUP2, .none) ∧
    decode daiJoinBytecode ⟨1697⟩ = some (.Push .PUSH2, some (⟨1702⟩, 2)) ∧
    decode daiJoinBytecode ⟨1700⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1702⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1703⟩ = some (.DIV, .none) ∧
    decode daiJoinBytecode ⟨1704⟩ = some (.EQ, .none) ∧
    decode daiJoinBytecode ⟨1705⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1706⟩ = some (.Push .PUSH2, some (⟨1714⟩, 2)) ∧
    decode daiJoinBytecode ⟨1709⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1714⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1715⟩ = some (.SWAP3, .none) ∧
    decode daiJoinBytecode ⟨1716⟩ = some (.SWAP2, .none) ∧
    decode daiJoinBytecode ⟨1717⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1718⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1719⟩ = some (.JUMP, .none) ∧
    (D_J daiJoinBytecode 0).contains ⟨1705⟩ = true ∧
    (D_J daiJoinBytecode 0).contains ⟨1702⟩ = true ∧
    (D_J daiJoinBytecode 0).contains ⟨1714⟩ = true := by
  and_intros <;> native_decide

theorem daiJoinMulRoutine_revert_shape :
    decode daiJoinBytecode ⟨1678⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1679⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
    decode daiJoinBytecode ⟨1681⟩ = some (.DUP2, .none) ∧
    decode daiJoinBytecode ⟨1682⟩ = some (.ISZERO, .none) ∧
    decode daiJoinBytecode ⟨1683⟩ = some (.DUP1, .none) ∧
    decode daiJoinBytecode ⟨1684⟩ = some (.Push .PUSH2, some (⟨1705⟩, 2)) ∧
    decode daiJoinBytecode ⟨1687⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1688⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1689⟩ = some (.POP, .none) ∧
    decode daiJoinBytecode ⟨1690⟩ = some (.DUP1, .none) ∧
    decode daiJoinBytecode ⟨1691⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1692⟩ = some (.MUL, .none) ∧
    decode daiJoinBytecode ⟨1693⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1694⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1695⟩ = some (.DUP3, .none) ∧
    decode daiJoinBytecode ⟨1696⟩ = some (.DUP2, .none) ∧
    decode daiJoinBytecode ⟨1697⟩ = some (.Push .PUSH2, some (⟨1702⟩, 2)) ∧
    decode daiJoinBytecode ⟨1700⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1702⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1703⟩ = some (.DIV, .none) ∧
    decode daiJoinBytecode ⟨1704⟩ = some (.EQ, .none) ∧
    decode daiJoinBytecode ⟨1705⟩ = some (.JUMPDEST, .none) ∧
    decode daiJoinBytecode ⟨1706⟩ = some (.Push .PUSH2, some (⟨1714⟩, 2)) ∧
    decode daiJoinBytecode ⟨1709⟩ = some (.JUMPI, .none) ∧
    decode daiJoinBytecode ⟨1710⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
    decode daiJoinBytecode ⟨1712⟩ = some (.DUP1, .none) ∧
    decode daiJoinBytecode ⟨1713⟩ = some (.REVERT, .none) ∧
    (D_J daiJoinBytecode 0).contains ⟨1702⟩ = true := by
  and_intros <;> native_decide

end Benchmarks.Dss.DaiJoin
