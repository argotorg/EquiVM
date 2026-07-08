import Benchmarks.Dss.ExponentialDecrease.RpowArithmeticLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.ExponentialDecrease

theorem rpow_div_two_toNat_le_pred {n : UInt256} {v : ℕ}
    (hnz : n ≠ ⟨0⟩) (hle : n.toNat ≤ v + 1) :
    (UInt256.div n ⟨2⟩).toNat ≤ v := by
  have hnNatNe : n.toNat ≠ 0 := by
    intro hzero
    exact hnz (uint256_toNat_eq_zero hzero)
  have hnPos : 0 < n.toNat := Nat.pos_of_ne_zero hnNatNe
  have hlt : (UInt256.div n ⟨2⟩).toNat < n.toNat := by
    rw [udiv_toNat, rpowUInt256Two_toNat]
    exact Nat.div_lt_self hnPos (by decide : 1 < 2)
  omega

theorem execRpowLoopBodyRevertXX {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hover : UInt256.size ≤ x.toNat * x.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody .reverted := by
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "x")) = .revert :=
    evalExpr_mul256_revert hstore.eval_x hstore.eval_x hover
  exact ExecBlock.consRevert (by
    simpa [rpowLoopBody, checkedMulUintInto] using
      (ExecStmt.letDeclRevert
        (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
        (name := "xx") (ty := some uint256) (expr := mul256 (.var "x") (.var "x"))
        hmul))

theorem execRpowLoopBodyRevertXXRound {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hfit : x.toNat * x.toNat < UInt256.size)
    (hover : UInt256.size ≤ (x * x).toNat + half.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody .reverted := by
  let xx := x * x
  let localsXX := locals.insert "xx" (.int (Int.ofNat xx.toNat))
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "x")) = .ok (.int (Int.ofNat xx.toNat)) :=
    evalExpr_mul256_ok hstore.eval_x hstore.eval_x rfl hfit
  have hstoreXX : RpowLoopStore x n b z half localsXX :=
    hstore.insert_ne "xx" (.int (Int.ofNat xx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxx :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsXX) (name := "xx")
      (value := xx) (store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := hstoreXX.eval_x
  have hzeroLitXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulReq :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (.binary .or
          (.binary .eq (.var "x") (.intLit 0))
          (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x"))) =
        .ok (.bool true) := by
    by_cases hx0 : x = ⟨0⟩
    · have hxZero :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_eq_int_true hxXX hzeroLitXX
        rw [hx0]
      exact evalExpr_or_true_left hxZero
    · have hxEqZero :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_eq_int_false hxXX hzeroLitXX
        intro hbad
        exact hx0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div xx x = x := by
        apply u256_inj
        rw [udiv_toNat]
        have hxxNat : xx.toNat = x.toNat * x.toNat := by
          change (x * x).toNat = x.toNat * x.toNat
          rw [umul_toNat x x hfit]
        rw [hxxNat]
        exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .div (.var "xx") (.var "x")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsXX)
          (x := .var "xx") (y := .var "x") (a := xx) (b := x)
          (q := UInt256.div xx x) hxx hxXX hx0 rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x")) =
            .ok (.bool true) :=
        evalExpr_eq_int_true hdiv hxXX rfl
      exact evalExpr_or_false_right hxEqZero hright
  have hadd :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (add256 (.var "xx") (.var "half")) = .revert :=
    evalExpr_add256_revert hxx hstoreXX.eval_half (by simpa [xx] using hover)
  refine ExecBlock.consNormal (by
    simpa [rpowLoopBody, checkedMulUintInto, xx, localsXX] using
      (ExecStmt.letDecl
        (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
        (name := "xx") (ty := some uint256) (expr := mul256 (.var "x") (.var "x"))
        (value := .int (Int.ofNat xx.toNat)) hmul)) ?_
  refine ExecBlock.consNormal (by
    simpa [rpowLoopBody, checkedMulUintInto, checkedAddUintInto, xx, localsXX] using
      (ExecStmt.requireTrue
        (cfg := config) (solm := { contract := contract, locals := localsXX }) (evm := evm)
        (condExpr :=
          .binary .or
            (.binary .eq (.var "x") (.intLit 0))
            (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x")))
        hmulReq)) ?_
  exact ExecBlock.consRevert (by
    simpa [rpowLoopBody, checkedMulUintInto, checkedAddUintInto, xx, localsXX] using
      (ExecStmt.letDeclRevert
        (cfg := config) (solm := { contract := contract, locals := localsXX }) (evm := evm)
        (name := "xxRound") (ty := some uint256)
        (expr := add256 (.var "xx") (.var "half")) hadd))

theorem execRpowLoopBodyOkEven {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hfit : x.toNat * x.toNat < UInt256.size)
    (hroundFit : (x * x).toNat + half.toNat < UInt256.size)
    (heven : n.toNat % 2 = 0) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ locals',
      ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody
        (.ok { contract := contract, locals := locals' } evm) ∧
      RpowLoopStore x' n' b z half locals' := by
  intro xx xxRound x' n'
  let localsXX := locals.insert "xx" (.int (Int.ofNat xx.toNat))
  let localsRound := localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))
  let localsX := localsRound.insert "x" (.int (Int.ofNat x'.toNat))
  let localsN := localsX.insert "n" (.int (Int.ofNat n'.toNat))
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "x")) = .ok (.int (Int.ofNat xx.toNat)) := by
    simpa [xx] using evalExpr_mul256_ok hstore.eval_x hstore.eval_x rfl hfit
  have hstoreXX : RpowLoopStore x n b z half localsXX :=
    hstore.insert_ne "xx" (.int (Int.ofNat xx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxx :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsXX) (name := "xx")
      (value := xx) (store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := hstoreXX.eval_x
  have hzeroLitXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulReq :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (.binary .or
          (.binary .eq (.var "x") (.intLit 0))
          (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x"))) =
        .ok (.bool true) := by
    by_cases hx0 : x = ⟨0⟩
    · have hxZero :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_eq_int_true hxXX hzeroLitXX
        rw [hx0]
      exact evalExpr_or_true_left hxZero
    · have hxEqZero :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_eq_int_false hxXX hzeroLitXX
        intro hbad
        exact hx0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div xx x = x := by
        apply u256_inj
        rw [udiv_toNat]
        have hxxNat : xx.toNat = x.toNat * x.toNat := by
          simp [xx, umul_toNat x x hfit]
        rw [hxxNat]
        exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .div (.var "xx") (.var "x")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsXX)
          (x := .var "xx") (y := .var "x") (a := xx) (b := x)
          (q := UInt256.div xx x) hxx hxXX hx0 rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? config { contract := contract, locals := localsXX } evm
            (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x")) =
            .ok (.bool true) :=
        evalExpr_eq_int_true hdiv hxXX rfl
      exact evalExpr_or_false_right hxEqZero hright
  have hadd :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (add256 (.var "xx") (.var "half")) = .ok (.int (Int.ofNat xxRound.toNat)) := by
    simpa [xxRound] using evalExpr_add256_ok hxx hstoreXX.eval_half rfl hroundFit
  have hstoreRound : RpowLoopStore x n b z half localsRound :=
    hstoreXX.insert_ne "xxRound" (.int (Int.ofNat xxRound.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxxRound :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xxRound") =
        .ok (.int (Int.ofNat xxRound.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xxRound")
      (value := xxRound)
      (store_get_self localsXX "xxRound" (.int (Int.ofNat xxRound.toNat)))
  have hxxRoundXX :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) := by
    have h := hstoreXX.insert_ne "xxRound" (.int (Int.ofNat xxRound.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
    exact evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xx")
      (value := xx) (by
        change (localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))).get? "xx" =
          some (.int (Int.ofNat xx.toNat))
        rw [store_get_ne localsXX (k := "xxRound") (a := "xx")
          (.int (Int.ofNat xxRound.toNat)) (by decide)]
        exact store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hroundFit)]
  have haddReq :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .ge (.var "xxRound") (.var "xx")) = .ok (.bool true) := by
    apply evalExpr_ge_uint256_true hxxRound hxxRoundXX
    rw [hxxRoundNat]
    omega
  have hdivX :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .div (.var "xxRound") (.var "b")) =
          .ok (.int (Int.ofNat x'.toNat)) := by
    exact evalExpr_div_uint256_ok hxxRound hstoreRound.eval_b hb rfl
  have hassignX :
      assignStorageRef? config { contract := contract, locals := localsRound } evm .localVar
          { base := "x" } (.int (Int.ofNat x'.toNat)) =
        .ok ({ contract := contract, locals := localsX }, evm) := by
    simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
    change (match localsRound.get? "x" with
      | some _ =>
          EvalResult.ok
            (({ contract := contract,
                locals := localsRound.insert "x" (.int (Int.ofNat x'.toNat)) } : Frame),
              evm)
      | none => EvalResult.error EvalError.unboundVariable) =
        EvalResult.ok (({ contract := contract, locals := localsX } : Frame), evm)
    rw [hstoreRound.get_x]
  have hstoreX : RpowLoopStore x' n b z half localsX :=
    hstoreRound.set_x x'
  have htwoLitX :
      evalExpr? config { contract := contract, locals := localsX } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hmod :
      evalExpr? config { contract := contract, locals := localsX } evm
        (.binary .mod (.var "n") (.intLit 2)) = .ok (.int 0) := by
    exact evalExpr_mod_int_ok hstoreX.eval_n htwoLitX
      (by simp [rpowUInt256Two_toNat])
      (by
        rw [rpowUInt256Two_toNat]
        norm_num
        exact_mod_cast heven.symm)
  have hzeroLitX :
      evalExpr? config { contract := contract, locals := localsX } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hoddCond :
      evalExpr? config { contract := contract, locals := localsX } evm
        (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_ne_int_false hmod hzeroLitX rfl
  have hdivN :
      evalExpr? config { contract := contract, locals := localsX } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) := by
    exact evalExpr_div_uint256_ok hstoreX.eval_n htwoLitX rpowUInt256Two_ne_zero rfl
  have hassignN :
      assignStorageRef? config { contract := contract, locals := localsX } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsN }, evm) := by
    simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
    change (match localsX.get? "n" with
      | some _ =>
          EvalResult.ok
            (({ contract := contract,
                locals := localsX.insert "n" (.int (Int.ofNat n'.toNat)) } : Frame), evm)
      | none => EvalResult.error EvalError.unboundVariable) =
        EvalResult.ok (({ contract := contract, locals := localsN } : Frame), evm)
    rw [hstoreX.get_n]
  have hstoreN : RpowLoopStore x' n' b z half localsN :=
    hstoreX.set_n n'
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "xx" (some uint256) (mul256 (.var "x") (.var "x")),
          .require
            (.binary .or
              (.binary .eq (.var "x") (.intLit 0))
              (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x"))),
          .letDecl "xxRound" (some uint256) (add256 (.var "xx") (.var "half")),
          .require (.binary .ge (.var "xxRound") (.var "xx")),
          .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "b")),
          .ite
            (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
            (checkedMulUintInto "zx" (.var "z") (.var "x") ++
              checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
              [ .assign .localVar { base := "z" }
                  (.binary .div (.var "zxRound") (.var "b")) ])
            [],
          .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]
        (.ok { contract := contract, locals := localsN } evm) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hmul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hmulReq) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue haddReq) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hdivX hassignX) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hoddCond ExecBlock.nil) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdivN hassignN) ExecBlock.nil
  exact ⟨localsN, by
    simpa [rpowLoopBody, checkedMulUintInto, checkedAddUintInto, xx, xxRound, x', n',
      localsXX, localsRound, localsX, localsN] using hblock, hstoreN⟩

end Benchmarks.Dss.ExponentialDecrease
