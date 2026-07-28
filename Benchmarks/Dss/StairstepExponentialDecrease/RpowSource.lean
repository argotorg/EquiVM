import Benchmarks.Dss.StairstepExponentialDecrease.RpowArithmeticLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.StairstepExponentialDecrease

theorem assignLocalVarBase_ok {evm : EVM.State} {locals : Store}
    {name : Ident} {old value : Value}
    (hget : locals.get? name = some old) :
    assignStorageRef? config { contract := contract, locals := locals } evm .localVar
        { base := name } value =
      .ok ({ contract := contract, locals := locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match locals.get? name with
    | some _ =>
        EvalResult.ok (({ contract := contract, locals := locals.insert name value } : Frame),
          evm)
    | none => EvalResult.error EvalError.unboundVariable) =
      EvalResult.ok (({ contract := contract, locals := locals.insert name value } : Frame), evm)
  rw [hget]

theorem u256_add_overflow_lt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.lt (a + b) a = ⟨1⟩ := by
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  exact ult_one (by
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega)

theorem u256_land_zero_left (a : UInt256) :
    UInt256.land (⟨0⟩ : UInt256) a = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  change Nat.land 0 a.toNat % UInt256.size = 0
  have hzero : Nat.land 0 a.toNat = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (0 &&& a.toNat).testBit i = (0 : Nat).testBit i
    rw [Nat.testBit_and]
    simp
  simpa [hzero]

theorem u256_land_zero_right (a : UInt256) :
    UInt256.land a (⟨0⟩ : UInt256) = ⟨0⟩ := by
  rw [u256_land_comm]
  exact u256_land_zero_left a

theorem RpowLoopStore.eval_odd_true {evm : EVM.State} {x n b z half : UInt256}
    {locals : Store} (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) := by
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hmod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [rpowUInt256Two_toNat])
      (by
        rw [rpowUInt256Two_toNat]
        norm_num)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_true hmod hzeroLit (by
    intro hbad
    apply hodd
    exact Nat.cast_injective hbad)

def rpowLoopPrefix : List Stmt :=
  checkedMulUintInto "xx" (.var "x") (.var "x") ++
    checkedAddUintInto "xxRound" (.var "xx") (.var "half") ++
    [ .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "b")) ]

def rpowLoopTail : List Stmt :=
  [ .ite
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
      (checkedMulUintInto "zx" (.var "z") (.var "x") ++
        checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
        [ .assign .localVar { base := "z" } (.binary .div (.var "zxRound") (.var "b")) ])
      [],
    .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]

theorem rpowLoopBody_eq_prefix_tail :
    rpowLoopBody = rpowLoopPrefix ++ rpowLoopTail := by
  simp [rpowLoopBody, rpowLoopPrefix, rpowLoopTail, checkedMulUintInto, checkedAddUintInto]

set_option maxHeartbeats 1000000 in
theorem execRpowLoopPrefixOk {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    ∃ locals',
      ExecBlock config { contract := contract, locals := locals } evm rpowLoopPrefix
        (.ok { contract := contract, locals := locals' } evm) ∧
      RpowLoopStore x' n b z half locals' := by
  intro xx xxRound x'
  let localsXX := locals.insert "xx" (.int (Int.ofNat xx.toNat))
  let localsRound := localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))
  let localsX := localsRound.insert "x" (.int (Int.ofNat x'.toNat))
  have hmulXX :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "x")) = .ok (.int (Int.ofNat xx.toNat)) := by
    simpa [xx] using evalExpr_mul256_ok hstore.eval_x hstore.eval_x rfl hfitXX
  have hstoreXX : RpowLoopStore x n b z half localsXX :=
    hstore.insert_ne "xx" (.int (Int.ofNat xx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxx :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsXX) (name := "xx")
      (value := xx) (store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := hstoreXX.eval_x
  have hzeroLitXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulXXReq :
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
          simp [xx, umul_toNat x x hfitXX]
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
  have haddXX :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (add256 (.var "xx") (.var "half")) = .ok (.int (Int.ofNat xxRound.toNat)) := by
    simpa [xxRound] using evalExpr_add256_ok hxx hstoreXX.eval_half rfl hfitXXRound
  have hstoreRound : RpowLoopStore x n b z half localsRound :=
    hstoreXX.insert_ne "xxRound" (.int (Int.ofNat xxRound.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxxRound :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xxRound") =
        .ok (.int (Int.ofNat xxRound.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xxRound")
      (value := xxRound)
      (store_get_self localsXX "xxRound" (.int (Int.ofNat xxRound.toNat)))
  have hxxRoundXX :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xx")
      (value := xx) (by
        change (localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))).get? "xx" =
          some (.int (Int.ofNat xx.toNat))
        rw [store_get_ne localsXX (k := "xxRound") (a := "xx")
          (.int (Int.ofNat xxRound.toNat)) (by decide)]
        exact store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have haddXXReq :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .ge (.var "xxRound") (.var "xx")) = .ok (.bool true) := by
    apply evalExpr_ge_uint256_true hxxRound hxxRoundXX
    rw [hxxRoundNat]
    omega
  have hdivX :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .div (.var "xxRound") (.var "b")) =
          .ok (.int (Int.ofNat x'.toNat)) :=
    evalExpr_div_uint256_ok hxxRound hstoreRound.eval_b hb rfl
  have hassignX :
      assignStorageRef? config { contract := contract, locals := localsRound } evm .localVar
          { base := "x" } (.int (Int.ofNat x'.toNat)) =
        .ok ({ contract := contract, locals := localsX }, evm) := by
    exact assignLocalVarBase_ok (evm := evm) (locals := localsRound) (name := "x")
      (old := .int (Int.ofNat x.toNat)) (value := .int (Int.ofNat x'.toNat))
      hstoreRound.get_x
  have hstoreX : RpowLoopStore x' n b z half localsX :=
    hstoreRound.set_x x'
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "xx" (some uint256) (mul256 (.var "x") (.var "x")),
          .require
            (.binary .or
              (.binary .eq (.var "x") (.intLit 0))
              (.binary .eq (.binary .div (.var "xx") (.var "x")) (.var "x"))),
          .letDecl "xxRound" (some uint256) (add256 (.var "xx") (.var "half")),
          .require (.binary .ge (.var "xxRound") (.var "xx")),
          .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "b")) ]
        (.ok { contract := contract, locals := localsX } evm) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulXX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hmulXXReq) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl haddXX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue haddXXReq) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdivX hassignX) ExecBlock.nil
  exact ⟨localsX, by
    simpa [rpowLoopPrefix, checkedMulUintInto, checkedAddUintInto, xx, xxRound, x',
      localsXX, localsRound, localsX] using hblock, hstoreX⟩

set_option maxHeartbeats 2000000 in
theorem execRpowLoopBodyOkOdd {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hfitZXRound :
      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat < UInt256.size) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let zx := z * x'
    let zxRound := zx + half
    let z' := UInt256.div zxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ locals',
      ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody
        (.ok { contract := contract, locals := locals' } evm) ∧
      RpowLoopStore x' n' b z' half locals' := by
  intro xx xxRound x' zx zxRound z' n'
  let localsXX := locals.insert "xx" (.int (Int.ofNat xx.toNat))
  let localsRound := localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))
  let localsX := localsRound.insert "x" (.int (Int.ofNat x'.toNat))
  let localsZX := localsX.insert "zx" (.int (Int.ofNat zx.toNat))
  let localsZXRound := localsZX.insert "zxRound" (.int (Int.ofNat zxRound.toNat))
  let localsZ := localsZXRound.insert "z" (.int (Int.ofNat z'.toNat))
  let localsN := localsZ.insert "n" (.int (Int.ofNat n'.toNat))
  have hmulXX :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "x")) = .ok (.int (Int.ofNat xx.toNat)) := by
    simpa [xx] using evalExpr_mul256_ok hstore.eval_x hstore.eval_x rfl hfitXX
  have hstoreXX : RpowLoopStore x n b z half localsXX :=
    hstore.insert_ne "xx" (.int (Int.ofNat xx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxx :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsXX) (name := "xx")
      (value := xx) (store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := hstoreXX.eval_x
  have hzeroLitXX :
      evalExpr? config { contract := contract, locals := localsXX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulXXReq :
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
          simp [xx, umul_toNat x x hfitXX]
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
  have haddXX :
      evalExpr? config { contract := contract, locals := localsXX } evm
        (add256 (.var "xx") (.var "half")) = .ok (.int (Int.ofNat xxRound.toNat)) := by
    simpa [xxRound] using evalExpr_add256_ok hxx hstoreXX.eval_half rfl hfitXXRound
  have hstoreRound : RpowLoopStore x n b z half localsRound :=
    hstoreXX.insert_ne "xxRound" (.int (Int.ofNat xxRound.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hxxRound :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xxRound") =
        .ok (.int (Int.ofNat xxRound.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xxRound")
      (value := xxRound)
      (store_get_self localsXX "xxRound" (.int (Int.ofNat xxRound.toNat)))
  have hxxRoundXX :
      evalExpr? config { contract := contract, locals := localsRound } evm (.var "xx") =
        .ok (.int (Int.ofNat xx.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsRound) (name := "xx")
      (value := xx) (by
        change (localsXX.insert "xxRound" (.int (Int.ofNat xxRound.toNat))).get? "xx" =
          some (.int (Int.ofNat xx.toNat))
        rw [store_get_ne localsXX (k := "xxRound") (a := "xx")
          (.int (Int.ofNat xxRound.toNat)) (by decide)]
        exact store_get_self locals "xx" (.int (Int.ofNat xx.toNat)))
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have haddXXReq :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .ge (.var "xxRound") (.var "xx")) = .ok (.bool true) := by
    apply evalExpr_ge_uint256_true hxxRound hxxRoundXX
    rw [hxxRoundNat]
    omega
  have hdivX :
      evalExpr? config { contract := contract, locals := localsRound } evm
        (.binary .div (.var "xxRound") (.var "b")) =
          .ok (.int (Int.ofNat x'.toNat)) :=
    evalExpr_div_uint256_ok hxxRound hstoreRound.eval_b hb rfl
  have hassignX :
      assignStorageRef? config { contract := contract, locals := localsRound } evm .localVar
          { base := "x" } (.int (Int.ofNat x'.toNat)) =
        .ok ({ contract := contract, locals := localsX }, evm) := by
    exact assignLocalVarBase_ok (evm := evm) (locals := localsRound) (name := "x")
      (old := .int (Int.ofNat x.toNat)) (value := .int (Int.ofNat x'.toNat))
      hstoreRound.get_x
  have hstoreX : RpowLoopStore x' n b z half localsX :=
    hstoreRound.set_x x'
  have hoddCond :
      evalExpr? config { contract := contract, locals := localsX } evm
        (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
          .ok (.bool true) :=
    hstoreX.eval_odd_true hodd
  have hmulZX :
      evalExpr? config { contract := contract, locals := localsX } evm
        (mul256 (.var "z") (.var "x")) = .ok (.int (Int.ofNat zx.toNat)) := by
    simpa [zx, x', xxRound, xx] using
      evalExpr_mul256_ok hstoreX.eval_z hstoreX.eval_x rfl hfitZX
  have hstoreZX : RpowLoopStore x' n b z half localsZX :=
    hstoreX.insert_ne "zx" (.int (Int.ofNat zx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hzx :
      evalExpr? config { contract := contract, locals := localsZX } evm (.var "zx") =
        .ok (.int (Int.ofNat zx.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsZX) (name := "zx")
      (value := zx) (store_get_self localsX "zx" (.int (Int.ofNat zx.toNat)))
  have hxZX :
      evalExpr? config { contract := contract, locals := localsZX } evm (.var "x") =
        .ok (.int (Int.ofNat x'.toNat)) := hstoreZX.eval_x
  have hzeroLitZX :
      evalExpr? config { contract := contract, locals := localsZX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulZXReq :
      evalExpr? config { contract := contract, locals := localsZX } evm
        (.binary .or
          (.binary .eq (.var "x") (.intLit 0))
          (.binary .eq (.binary .div (.var "zx") (.var "x")) (.var "z"))) =
        .ok (.bool true) := by
    by_cases hx0 : x' = ⟨0⟩
    · have hxZero :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_eq_int_true hxZX hzeroLitZX
        rw [hx0]
      exact evalExpr_or_true_left hxZero
    · have hxEqZero :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_eq_int_false hxZX hzeroLitZX
        intro hbad
        exact hx0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hxNatNe : x'.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div zx x' = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x'.toNat := by
          simp [zx, umul_toNat z x' hfitZX]
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .div (.var "zx") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
        have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsZX)
          (x := .var "zx") (y := .var "x") (a := zx) (b := x')
          (q := UInt256.div zx x') hzx hxZX hx0 rfl
        simpa [hdivWord] using h
      have hzZX :
          evalExpr? config { contract := contract, locals := localsZX } evm (.var "z") =
            .ok (.int (Int.ofNat z.toNat)) := hstoreZX.eval_z
      have hright :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.binary .div (.var "zx") (.var "x")) (.var "z")) =
            .ok (.bool true) :=
        evalExpr_eq_int_true hdiv hzZX rfl
      exact evalExpr_or_false_right hxEqZero hright
  have haddZX :
      evalExpr? config { contract := contract, locals := localsZX } evm
        (add256 (.var "zx") (.var "half")) = .ok (.int (Int.ofNat zxRound.toNat)) := by
    simpa [zxRound, zx, x', xxRound, xx] using
      evalExpr_add256_ok hzx hstoreZX.eval_half rfl hfitZXRound
  have hstoreZXRound : RpowLoopStore x' n b z half localsZXRound :=
    hstoreZX.insert_ne "zxRound" (.int (Int.ofNat zxRound.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hzxRound :
      evalExpr? config { contract := contract, locals := localsZXRound } evm (.var "zxRound") =
        .ok (.int (Int.ofNat zxRound.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsZXRound) (name := "zxRound")
      (value := zxRound)
      (store_get_self localsZX "zxRound" (.int (Int.ofNat zxRound.toNat)))
  have hzxRoundZX :
      evalExpr? config { contract := contract, locals := localsZXRound } evm (.var "zx") =
        .ok (.int (Int.ofNat zx.toNat)) := by
    exact evalExpr_varUInt256 (evm := evm) (locals := localsZXRound) (name := "zx")
      (value := zx) (by
        change (localsZX.insert "zxRound" (.int (Int.ofNat zxRound.toNat))).get? "zx" =
          some (.int (Int.ofNat zx.toNat))
        rw [store_get_ne localsZX (k := "zxRound") (a := "zx")
          (.int (Int.ofNat zxRound.toNat)) (by decide)]
        exact store_get_self localsX "zx" (.int (Int.ofNat zx.toNat)))
  have hzxRoundNat : zxRound.toNat = zx.toNat + half.toNat := by
    change (zx + half).toNat = zx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [zx, x', xxRound, xx] using hfitZXRound)]
  have haddZXReq :
      evalExpr? config { contract := contract, locals := localsZXRound } evm
        (.binary .ge (.var "zxRound") (.var "zx")) = .ok (.bool true) := by
    apply evalExpr_ge_uint256_true hzxRound hzxRoundZX
    rw [hzxRoundNat]
    omega
  have hdivZ :
      evalExpr? config { contract := contract, locals := localsZXRound } evm
        (.binary .div (.var "zxRound") (.var "b")) =
          .ok (.int (Int.ofNat z'.toNat)) :=
    evalExpr_div_uint256_ok hzxRound hstoreZXRound.eval_b hb rfl
  have hassignZ :
      assignStorageRef? config { contract := contract, locals := localsZXRound } evm .localVar
          { base := "z" } (.int (Int.ofNat z'.toNat)) =
        .ok ({ contract := contract, locals := localsZ }, evm) := by
    exact assignLocalVarBase_ok (evm := evm) (locals := localsZXRound) (name := "z")
      (old := .int (Int.ofNat z.toNat)) (value := .int (Int.ofNat z'.toNat))
      hstoreZXRound.get_z
  have hstoreZ : RpowLoopStore x' n b z' half localsZ :=
    hstoreZXRound.set_z z'
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hdivN :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) :=
    evalExpr_div_uint256_ok hstoreZ.eval_n htwoLitZ rpowUInt256Two_ne_zero rfl
  have hassignN :
      assignStorageRef? config { contract := contract, locals := localsZ } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsN }, evm) := by
    exact assignLocalVarBase_ok (evm := evm) (locals := localsZ) (name := "n")
      (old := .int (Int.ofNat n.toNat)) (value := .int (Int.ofNat n'.toNat))
      hstoreZ.get_n
  have hstoreN : RpowLoopStore x' n' b z' half localsN :=
    hstoreZ.set_n n'
  have hthen :
      ExecBlock config { contract := contract, locals := localsX } evm
        (checkedMulUintInto "zx" (.var "z") (.var "x") ++
          checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
          [ .assign .localVar { base := "z" }
              (.binary .div (.var "zxRound") (.var "b")) ])
        (.ok { contract := contract, locals := localsZ } evm) := by
    simp only [checkedMulUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulZX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hmulZXReq) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl haddZX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue haddZXReq) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdivZ hassignZ) ExecBlock.nil
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
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulXX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hmulXXReq) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl haddXX) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue haddXXReq) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hdivX hassignX) ?_
    refine ExecBlock.consNormal (ExecStmt.iteTrue hoddCond hthen) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdivN hassignN) ExecBlock.nil
  exact ⟨localsN, by
    simpa [rpowLoopBody, checkedMulUintInto, checkedAddUintInto, xx, xxRound, x', zx,
      zxRound, z', n', localsXX, localsRound, localsX, localsZX, localsZXRound, localsZ,
      localsN] using hblock, hstoreN⟩

theorem execRpowOddTailRevertZX {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0)
    (hover : UInt256.size ≤ z.toNat * x.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .ite
          (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (checkedMulUintInto "zx" (.var "z") (.var "x") ++
            checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
            [ .assign .localVar { base := "z" }
                (.binary .div (.var "zxRound") (.var "b")) ])
          [],
        .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]
      .reverted := by
  have hoddCond :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
          .ok (.bool true) :=
    hstore.eval_odd_true hodd
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "z") (.var "x")) = .revert :=
    evalExpr_mul256_revert hstore.eval_z hstore.eval_x hover
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "zx" (.var "z") (.var "x") ++
          checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
          [ .assign .localVar { base := "z" }
              (.binary .div (.var "zxRound") (.var "b")) ])
        .reverted := by
    simp only [checkedMulUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)
  exact ExecBlock.consRevert (ExecStmt.iteTrue hoddCond hthen)

theorem execRpowOddTailRevertZXRound {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0)
    (hfit : z.toNat * x.toNat < UInt256.size)
    (hover : UInt256.size ≤ (z * x).toNat + half.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .ite
          (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (checkedMulUintInto "zx" (.var "z") (.var "x") ++
            checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
            [ .assign .localVar { base := "z" }
                (.binary .div (.var "zxRound") (.var "b")) ])
          [],
        .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]
      .reverted := by
  let zx := z * x
  let localsZX := locals.insert "zx" (.int (Int.ofNat zx.toNat))
  have hoddCond :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
          .ok (.bool true) :=
    hstore.eval_odd_true hodd
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "z") (.var "x")) = .ok (.int (Int.ofNat zx.toNat)) := by
    simpa [zx] using evalExpr_mul256_ok hstore.eval_z hstore.eval_x rfl hfit
  have hstoreZX : RpowLoopStore x n b z half localsZX :=
    hstore.insert_ne "zx" (.int (Int.ofNat zx.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hzx :
      evalExpr? config { contract := contract, locals := localsZX } evm (.var "zx") =
        .ok (.int (Int.ofNat zx.toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := localsZX) (name := "zx")
      (value := zx) (store_get_self locals "zx" (.int (Int.ofNat zx.toNat)))
  have hxZX :
      evalExpr? config { contract := contract, locals := localsZX } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := hstoreZX.eval_x
  have hzeroLitZX :
      evalExpr? config { contract := contract, locals := localsZX } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hmulReq :
      evalExpr? config { contract := contract, locals := localsZX } evm
        (.binary .or
          (.binary .eq (.var "x") (.intLit 0))
          (.binary .eq (.binary .div (.var "zx") (.var "x")) (.var "z"))) =
        .ok (.bool true) := by
    by_cases hx0 : x = ⟨0⟩
    · have hxZero :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_eq_int_true hxZX hzeroLitZX
        rw [hx0]
      exact evalExpr_or_true_left hxZero
    · have hxEqZero :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_eq_int_false hxZX hzeroLitZX
        intro hbad
        exact hx0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div zx x = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x.toNat := by
          simp [zx, umul_toNat z x hfit]
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .div (.var "zx") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
        have h := evalExpr_div_uint256_ok (evm := evm) (locals := localsZX)
          (x := .var "zx") (y := .var "x") (a := zx) (b := x)
          (q := UInt256.div zx x) hzx hxZX hx0 rfl
        simpa [hdivWord] using h
      have hzZX :
          evalExpr? config { contract := contract, locals := localsZX } evm (.var "z") =
            .ok (.int (Int.ofNat z.toNat)) := hstoreZX.eval_z
      have hright :
          evalExpr? config { contract := contract, locals := localsZX } evm
            (.binary .eq (.binary .div (.var "zx") (.var "x")) (.var "z")) =
            .ok (.bool true) :=
        evalExpr_eq_int_true hdiv hzZX rfl
      exact evalExpr_or_false_right hxEqZero hright
  have hadd :
      evalExpr? config { contract := contract, locals := localsZX } evm
        (add256 (.var "zx") (.var "half")) = .revert :=
    evalExpr_add256_revert hzx hstoreZX.eval_half (by simpa [zx] using hover)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedMulUintInto "zx" (.var "z") (.var "x") ++
          checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
          [ .assign .localVar { base := "z" }
              (.binary .div (.var "zxRound") (.var "b")) ])
        .reverted := by
    simp only [checkedMulUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hmul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hmulReq) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)
  exact ExecBlock.consRevert (ExecStmt.iteTrue hoddCond hthen)

theorem execRpowLoopBodyRevertZX {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hover :
      UInt256.size ≤ z.toNat * (UInt256.div ((x * x) + half) b).toNat) :
    ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody .reverted := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  obtain ⟨localsX, hprefix, hstoreX⟩ :=
    execRpowLoopPrefixOk (evm := evm) (locals := locals) hstore hb hfitXX hfitXXRound
  have htail :
      ExecBlock config { contract := contract, locals := localsX } evm rpowLoopTail .reverted := by
    simpa [rpowLoopTail, x', xxRound, xx, checkedMulUintInto, checkedAddUintInto] using
      (execRpowOddTailRevertZX (evm := evm) (locals := localsX)
        (x := x') (n := n) (b := b) (z := z) (half := half) hstoreX hodd
        (by simpa [x', xxRound, xx] using hover))
  have happ := execBlock_append (cfg := config) (s2 := rpowLoopTail) hprefix htail
  simpa [rpowLoopBody_eq_prefix_tail] using happ
theorem execRpowLoopBodyRevertZXRound {evm : EVM.State} {locals : Store}
    {x n b z half : UInt256}
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hover :
      UInt256.size ≤
        (z * UInt256.div ((x * x) + half) b).toNat + half.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm rpowLoopBody .reverted := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  obtain ⟨localsX, hprefix, hstoreX⟩ :=
    execRpowLoopPrefixOk (evm := evm) (locals := locals) hstore hb hfitXX hfitXXRound
  have htail :
      ExecBlock config { contract := contract, locals := localsX } evm rpowLoopTail .reverted := by
    simpa [rpowLoopTail, x', xxRound, xx, checkedMulUintInto, checkedAddUintInto] using
      (execRpowOddTailRevertZXRound (evm := evm) (locals := localsX)
        (x := x') (n := n) (b := b) (z := z) (half := half) hstoreX hodd
        (by simpa [x', xxRound, xx] using hfitZX)
        (by simpa [x', xxRound, xx] using hover))
  have happ := execBlock_append (cfg := config) (s2 := rpowLoopTail) hprefix htail
  simpa [rpowLoopBody_eq_prefix_tail] using happ

theorem execRpowFunctionReturnXNonzeroWithLoop
    (evm : EVM.State) {x n b xFinal zFinal : UInt256} {localsFinal : Store}
    (hxz : x ≠ ⟨0⟩)
    (hnz : n ≠ ⟨0⟩)
    (hfinalStore :
      RpowLoopStore xFinal ⟨0⟩ b zFinal (UInt256.div b ⟨2⟩) localsFinal)
    (hwhile :
      ExecStmt config
        { contract := contract,
          locals :=
            rpowLocalsZHN x n b (if n.toNat % 2 = 0 then b else x)
              (UInt256.div b ⟨2⟩) (UInt256.div n ⟨2⟩) }
        evm (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody)
        (.ok { contract := contract, locals := localsFinal } evm)) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
      rpowFunction.body
      (.returned { contract := contract, locals := localsFinal } evm
        (some [.int (Int.ofNat zFinal.toNat)])) := by
  let locals := uintTernaryLocals x n b
  let z := if n.toNat % 2 = 0 then b else x
  let half := UInt256.div b ⟨2⟩
  let n' := UInt256.div n ⟨2⟩
  let localsZ := rpowLocalsZ x n b z
  let localsZH := rpowLocalsZH x n b z half
  let localsLoop := rpowLocalsZHN x n b z half n'
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x n b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n) (uintTernaryLocals_get_n x n b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "b") (value := b) (uintTernaryLocals_get_b x n b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hn hzeroLit
    intro hbad
    exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [rpowUInt256Two_toNat])
      (by
        rw [rpowUInt256Two_toNat]
        norm_num)
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "b") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
    by_cases heven : n.toNat % 2 = 0
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool true) := by
        simpa [heven] using evalExpr_eq_int_true hMod hzeroLit (by simp [heven])
      simpa [z, heven] using evalExpr_ite_true hModEq hb
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool false) := by
        apply evalExpr_eq_int_false hMod hzeroLit
        intro hbad
        exact heven (Int.ofNat.inj hbad)
      simpa [z, heven] using evalExpr_ite_false hModEq hx
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "b") (value := b) (rpowLocalsZ_get_b x n b z)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "b") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by native_decide) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [localsZH, half, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := n) (rpowLocalsZH_get_n x n b z half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) := by
    simpa [n'] using evalExpr_div_uint256_ok hnZH htwoLitZH rpowUInt256Two_ne_zero rfl
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsLoop }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsLoop,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
  have hzDone :
      evalExpr? config { contract := contract, locals := localsFinal } evm (.var "z") =
        .ok (.int (Int.ofNat zFinal.toNat)) := hfinalStore.eval_z
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
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    refine ExecBlock.consNormal (by simpa [localsLoop, z, half, n'] using hwhile) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzDone))
  have hXBranch :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .eq (.var "x") (.intLit 0))
            [ .return [.intLit 0] ]
            [ .letDecl "z" (some uint256)
                (.ite
                  (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                  (.var "b")
                  (.var "x")),
              .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
              .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
              .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
              .return [.var "z"] ] ]
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) := by
    exact ExecBlock.consReturn (ExecStmt.iteFalse hxZero hElseBlock)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hnZero hXBranch)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

theorem execRpowFunctionRevertXNonzeroWithLoop
    (evm : EVM.State) {x n b : UInt256}
    (hxz : x ≠ ⟨0⟩)
    (hnz : n ≠ ⟨0⟩)
    (hwhile :
      ExecStmt config
        { contract := contract,
          locals :=
            rpowLocalsZHN x n b (if n.toNat % 2 = 0 then b else x)
              (UInt256.div b ⟨2⟩) (UInt256.div n ⟨2⟩) }
        evm (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody) .reverted) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
      rpowFunction.body .reverted := by
  let locals := uintTernaryLocals x n b
  let z := if n.toNat % 2 = 0 then b else x
  let half := UInt256.div b ⟨2⟩
  let n' := UInt256.div n ⟨2⟩
  let localsZ := rpowLocalsZ x n b z
  let localsZH := rpowLocalsZH x n b z half
  let localsLoop := rpowLocalsZHN x n b z half n'
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x n b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n) (uintTernaryLocals_get_n x n b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "b") (value := b) (uintTernaryLocals_get_b x n b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hn hzeroLit
    intro hbad
    exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [rpowUInt256Two_toNat])
      (by
        rw [rpowUInt256Two_toNat]
        norm_num)
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "b") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
    by_cases heven : n.toNat % 2 = 0
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool true) := by
        simpa [heven] using evalExpr_eq_int_true hMod hzeroLit (by simp [heven])
      simpa [z, heven] using evalExpr_ite_true hModEq hb
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool false) := by
        apply evalExpr_eq_int_false hMod hzeroLit
        intro hbad
        exact heven (Int.ofNat.inj hbad)
      simpa [z, heven] using evalExpr_ite_false hModEq hx
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "b") (value := b) (rpowLocalsZ_get_b x n b z)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "b") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by native_decide) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [localsZH, half, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := n) (rpowLocalsZH_get_n x n b z half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, rpowUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) := by
    simpa [n'] using evalExpr_div_uint256_ok hnZH htwoLitZH rpowUInt256Two_ne_zero rfl
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsLoop }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsLoop,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
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
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    exact ExecBlock.consRevert (by simpa [localsLoop, z, half, n'] using hwhile)
  have hXBranch :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.binary .eq (.var "x") (.intLit 0))
            [ .return [.intLit 0] ]
            [ .letDecl "z" (some uint256)
                (.ite
                  (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                  (.var "b")
                  (.var "x")),
              .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
              .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
              .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
              .return [.var "z"] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hxZero hElseBlock)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        .reverted := by
    simpa [rpowFunction] using ExecBlock.consRevert (ExecStmt.iteFalse hnZero hXBranch)
  simpa [locals] using ExecFuncBody.execBlockRevert hblock

theorem execRpowFunctionReturnXZeroNNonzero (evm : EVM.State) {n b : UInt256}
    (hnz : n ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals ⟨0⟩ n b }
      evm rpowFunction.body
      (.returned { contract := contract, locals := uintTernaryLocals ⟨0⟩ n b } evm
        (some [.int 0])) := by
  let locals := uintTernaryLocals ⟨0⟩ n b
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n)
      (uintTernaryLocals_get_n ⟨0⟩ n b)
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int 0) := by
    have hx0 := evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_x ⟨0⟩ n b)
    simpa [locals, rpowUInt256Zero_toNat] using hx0
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hn hzeroLit
    intro hbad
    exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) :=
    evalExpr_eq_int_true hx hzeroLit rfl
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .return [.intLit 0] ]
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) :=
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzeroLit))
  have hinner :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite
            (.binary .eq (.var "x") (.intLit 0))
            [ .return [.intLit 0] ]
            [ .letDecl "z" (some uint256)
                (.ite
                  (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                  (.var "b")
                  (.var "x")),
              .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
              .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
              .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
              .return [.var "z"] ] ]
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) :=
    ExecBlock.consReturn (ExecStmt.iteTrue hxZero hthen)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hnZero hinner)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

end Benchmarks.Dss.StairstepExponentialDecrease
