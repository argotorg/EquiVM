import Benchmarks.Dss.Jug.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

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
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hmod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [jugUInt256Two_toNat])
      (by
        rw [jugUInt256Two_toNat]
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
    simp [evalExpr?, pure, jugUInt256Two_toNat]
  have hdivN :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) :=
    evalExpr_div_uint256_ok hstoreZ.eval_n htwoLitZ jugUInt256Two_ne_zero rfl
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

theorem RD.jugDripRpowLoopExit
    {cA gh bl σ σ₀ A I} {g half scratch z b x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (rd2196 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2196⟩
      (half :: scratch :: z :: b :: ⟨0⟩ :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (z :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have rd2202 := evm_run rd2196 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2307⟩ (by native_decide) (by evm_ov)]
  have hnDone : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd2307 := rd2202.jumpiT (by native_decide) hnDone (by jump_dest) (by evm_ov)
  have rd2335pre := evm_run rd2307 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨2335⟩ (by native_decide) (by evm_ov)]
  have rd2335 := rd2335pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2342 := evm_run rd2335 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd1524⟩

theorem RD.jugDripRpowLoopBodyEntry
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hnz : n ≠ ⟨0⟩)
    (rd2196 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2196⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k' C' := by
  have rd2202 := evm_run rd2196 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2307⟩ (by native_decide) (by evm_ov)]
  have hnNonzero : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  have rd2203 := rd2202.jumpiNT (by native_decide) hnNonzero (by evm_ov)
  exact ⟨_, _, by simpa using rd2203⟩

theorem RD.jugDripRpowLoopRevertXX
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hover : UInt256.size ≤ x.toNat * x.toNat)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hdivNe : UInt256.div (x * x) x ≠ x :=
    u256_mul_div_overflow_ne x x hover
  have rd2214 := evm_run rd2203 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2219⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * x) x) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rdFallthrough := rd2214.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripRpowLoopRevertXXRound
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfit : x.toNat * x.toNat < UInt256.size)
    (hover : UInt256.size ≤ (x * x).toNat + half.toNat)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let xx := x * x
  have hdivWord : UInt256.div xx x = x := by
    by_cases hx0 : x = ⟨0⟩
    · subst x
      native_decide
    · apply u256_inj
      rw [udiv_toNat]
      have hxxNat : xx.toNat = x.toNat * x.toNat := by
        simp [xx, umul_toNat x x hfit]
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      rw [hxxNat]
      exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
  have rd2214 := evm_run rd2203 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2219⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * x) x) x ≠ ⟨0⟩ := by
    rw [show UInt256.div (x * x) x = x by simpa [xx] using hdivWord, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2219 := rd2214.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
  have hlt : UInt256.lt (xx + half) xx = ⟨1⟩ :=
    u256_add_overflow_lt xx half (by simpa [xx] using hover)
  have rd2230 := evm_run rd2219 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2235⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.lt (xx + half) xx) = ⟨0⟩ := by
    rw [hlt]
    native_decide
  have rdFallthrough := rd2230.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripRpowLoopOddTailEntry
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2251⟩
      (half :: scratch :: z :: b :: n :: x' :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k' C' := by
  intro xx xxRound x'
  have hdivXXWord : UInt256.div xx x = x := by
    by_cases hx0 : x = ⟨0⟩
    · subst x
      native_decide
    · apply u256_inj
      rw [udiv_toNat]
      have hxxNat : xx.toNat = x.toNat * x.toNat := by
        simp [xx, umul_toNat x x hfitXX]
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      rw [hxxNat]
      exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
  have rd2214 := evm_run rd2203 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2219⟩ (by native_decide) (by evm_ov)]
  have heqXXCond : UInt256.eq (UInt256.div (x * x) x) x ≠ ⟨0⟩ := by
    rw [show UInt256.div (x * x) x = x by simpa [xx] using hdivXXWord,
      u256_eq_refl]
    exact one_ne_zero_uint
  have rd2219 := rd2214.jumpiT (by native_decide) heqXXCond (by jump_dest) (by evm_ov)
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have hltXX : UInt256.lt xxRound xx = ⟨0⟩ := by
    apply ult_zero
    rw [hxxRoundNat]
    omega
  have rd2230 := evm_run rd2219 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2235⟩ (by native_decide) (by evm_ov)]
  have hcondXXAdd : UInt256.isZero (UInt256.lt xxRound xx) ≠ ⟨0⟩ := by
    rw [hltXX]
    native_decide
  have rd2235 := rd2230.jumpiT (by native_decide) hcondXXAdd (by jump_dest) (by evm_ov)
  have rd2247 := evm_run rd2235 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap7 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2296⟩ (by native_decide) (by evm_ov)]
  have hlandNe : UInt256.land n ⟨1⟩ ≠ ⟨0⟩ := by
    intro hland
    apply hodd
    rw [← uInt256_land_one_toNat n, hland]
    native_decide
  have hcondOdd : UInt256.isZero (UInt256.land n ⟨1⟩) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlandNe
  have rd2251 := rd2247.jumpiNT (by native_decide) hcondOdd (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x'] using rd2251⟩

theorem RD.jugDripRpowLoopRevertZX
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hover :
      UInt256.size ≤ z.toNat * (UInt256.div ((x * x) + half) b).toNat)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  let zx := z * x'
  obtain ⟨_, _, rd2251⟩ :=
    RD.jugDripRpowLoopOddTailEntry (R := R) hRlen (hfitXX := hfitXX)
      (hfitXXRound := hfitXXRound) hodd rd2203
  have hdivNe : UInt256.div zx x' ≠ z := by
    have h := u256_mul_div_overflow_ne z x'
      (by simpa [zx, x', xxRound, xx] using hover)
    have hcomm : zx = x' * z := by
      simpa [zx] using u256_mul_comm z x'
    simpa [hcomm] using h
  have hxNatNe : x'.toNat ≠ 0 := by
    intro hzero
    have hzLt : z.toNat < UInt256.size := z.val.isLt
    have hbad : UInt256.size ≤ 0 := by
      simpa [x', xxRound, xx, hzero] using hover
    omega
  have hxNe : x' ≠ ⟨0⟩ := by
    intro hx
    exact hxNatNe (by rw [hx]; rfl)
  have hmulGuardFail :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) =
        ⟨0⟩ := by
    have hleft : UInt256.isZero (UInt256.isZero x') = ⟨1⟩ := by
      rw [isZero_eq_zero_of_ne hxNe]
      native_decide
    have hright :
        UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨1⟩ := by
      rw [u256_eq_of_ne hdivNe]
      native_decide
    rw [hleft, hright]
    native_decide
  have rd2268 := evm_run rd2251 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2273⟩ (by native_decide) (by evm_ov)]
  have rdFallthrough := rd2268.jumpiNT (by native_decide) hmulGuardFail (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.jugDripRpowLoopRevertZXRound
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hover :
      UInt256.size ≤
        (z * UInt256.div ((x * x) + half) b).toNat + half.toNat)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  let zx := z * x'
  obtain ⟨_, _, rd2251⟩ :=
    RD.jugDripRpowLoopOddTailEntry (R := R) hRlen (hfitXX := hfitXX)
      (hfitXXRound := hfitXXRound) hodd rd2203
  have hmulGuard :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) ≠
        ⟨0⟩ := by
    by_cases hx0 : x' = ⟨0⟩
    · have hleft : UInt256.isZero (UInt256.isZero x') = ⟨0⟩ := by
        rw [hx0]
        native_decide
      rw [hleft, u256_land_zero_left]
      native_decide
    · have hdivZXWord : UInt256.div zx x' = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x'.toNat := by
          simp [zx, x', xxRound, xx, umul_toNat z x' (by
            simpa [x', xxRound, xx] using hfitZX)]
        have hxNatNe : x'.toNat ≠ 0 := by
          intro hzero
          exact hx0 (uint256_toNat_eq_zero hzero)
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hright :
          UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨0⟩ := by
        rw [show UInt256.div zx x' = z by exact hdivZXWord, u256_eq_refl]
        native_decide
      rw [hright, u256_land_zero_right]
      native_decide
  have rd2268 := evm_run rd2251 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2273⟩ (by native_decide) (by evm_ov)]
  have rd2273 := rd2268.jumpiT (by native_decide) hmulGuard (by jump_dest) (by evm_ov)
  have hlt : UInt256.lt (zx + half) zx = ⟨1⟩ :=
    u256_add_overflow_lt zx half (by simpa [zx, x', xxRound, xx] using hover)
  have rd2284 := evm_run rd2273 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2289⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.lt (zx + half) zx) = ⟨0⟩ := by
    rw [hlt]
    native_decide
  have rdFallthrough := rd2284.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.jugDripRpowLoopStepEven
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (heven : n.toNat % 2 = 0)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2196⟩
      (half :: scratch :: z :: b :: n' :: x' :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k' C' := by
  intro xx xxRound x' n'
  have hdivWord : UInt256.div xx x = x := by
    by_cases hx0 : x = ⟨0⟩
    · subst x
      native_decide
    · apply u256_inj
      rw [udiv_toNat]
      have hxxNat : xx.toNat = x.toNat * x.toNat := by
        simp [xx, umul_toNat x x hfitXX]
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      rw [hxxNat]
      exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
  have rd2214 := evm_run rd2203 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2219⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * x) x) x ≠ ⟨0⟩ := by
    rw [show UInt256.div (x * x) x = x by simpa [xx] using hdivWord, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2219 := rd2214.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have hlt : UInt256.lt xxRound xx = ⟨0⟩ := by
    apply ult_zero
    rw [hxxRoundNat]
    omega
  have rd2230 := evm_run rd2219 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2235⟩ (by native_decide) (by evm_ov)]
  have hcondAdd : UInt256.isZero (UInt256.lt xxRound xx) ≠ ⟨0⟩ := by
    rw [hlt]
    native_decide
  have rd2235 := rd2230.jumpiT (by native_decide) hcondAdd (by jump_dest) (by evm_ov)
  have rd2247 := evm_run rd2235 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap7 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2296⟩ (by native_decide) (by evm_ov)]
  have hland : UInt256.land n ⟨1⟩ = ⟨0⟩ := by
    apply u256_inj
    rw [uInt256_land_one_toNat, heven]
    native_decide
  have hcondEven : UInt256.isZero (UInt256.land n ⟨1⟩) ≠ ⟨0⟩ := by
    rw [hland]
    native_decide
  have rd2296 := rd2247.jumpiT (by native_decide) hcondEven (by jump_dest) (by evm_ov)
  have rd2303 := evm_run rd2296 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨2196⟩ (by native_decide) (by evm_ov)]
  have rd2196 := rd2303.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x', n', hland] using rd2196⟩

theorem RD.jugDripRpowLoopStepOdd
    {cA gh bl σ σ₀ A I} {g half scratch z b n x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hfitZXRound :
      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat < UInt256.size)
    (rd2203 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2203⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let zx := z * x'
    let zxRound := zx + half
    let z' := UInt256.div zxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2196⟩
      (half :: scratch :: z' :: b :: n' :: x' :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k' C' := by
  intro xx xxRound x' zx zxRound z' n'
  have hdivXXWord : UInt256.div xx x = x := by
    by_cases hx0 : x = ⟨0⟩
    · subst x
      native_decide
    · apply u256_inj
      rw [udiv_toNat]
      have hxxNat : xx.toNat = x.toNat * x.toNat := by
        simp [xx, umul_toNat x x hfitXX]
      have hxNatNe : x.toNat ≠ 0 := by
        intro hzero
        exact hx0 (uint256_toNat_eq_zero hzero)
      rw [hxxNat]
      exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hxNatNe)
  have rd2214 := evm_run rd2203 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨2219⟩ (by native_decide) (by evm_ov)]
  have heqXXCond : UInt256.eq (UInt256.div (x * x) x) x ≠ ⟨0⟩ := by
    rw [show UInt256.div (x * x) x = x by simpa [xx] using hdivXXWord,
      u256_eq_refl]
    exact one_ne_zero_uint
  have rd2219 := rd2214.jumpiT (by native_decide) heqXXCond (by jump_dest) (by evm_ov)
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have hltXX : UInt256.lt xxRound xx = ⟨0⟩ := by
    apply ult_zero
    rw [hxxRoundNat]
    omega
  have rd2230 := evm_run rd2219 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2235⟩ (by native_decide) (by evm_ov)]
  have hcondXXAdd : UInt256.isZero (UInt256.lt xxRound xx) ≠ ⟨0⟩ := by
    rw [hltXX]
    native_decide
  have rd2235 := rd2230.jumpiT (by native_decide) hcondXXAdd (by jump_dest) (by evm_ov)
  have rd2247 := evm_run rd2235 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap7 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2296⟩ (by native_decide) (by evm_ov)]
  have hlandNe : UInt256.land n ⟨1⟩ ≠ ⟨0⟩ := by
    intro hland
    apply hodd
    rw [← uInt256_land_one_toNat n, hland]
    native_decide
  have hcondOdd : UInt256.isZero (UInt256.land n ⟨1⟩) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlandNe
  have rd2251 := rd2247.jumpiNT (by native_decide) hcondOdd (by evm_ov)
  have hmulGuard :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) ≠
        ⟨0⟩ := by
    by_cases hx0 : x' = ⟨0⟩
    · have hleft : UInt256.isZero (UInt256.isZero x') = ⟨0⟩ := by
        rw [hx0]
        native_decide
      rw [hleft, u256_land_zero_left]
      native_decide
    · have hdivZXWord : UInt256.div zx x' = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x'.toNat := by
          simp [zx, x', xxRound, xx, umul_toNat z x' (by
            simpa [x', xxRound, xx] using hfitZX)]
        have hxNatNe : x'.toNat ≠ 0 := by
          intro hzero
          exact hx0 (uint256_toNat_eq_zero hzero)
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hright :
          UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨0⟩ := by
        rw [show UInt256.div zx x' = z by exact hdivZXWord, u256_eq_refl]
        native_decide
      rw [hright, u256_land_zero_right]
      native_decide
  have rd2268 := evm_run rd2251 with [
    raw dup6 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2273⟩ (by native_decide) (by evm_ov)]
  have rd2273 := rd2268.jumpiT (by native_decide) hmulGuard (by jump_dest) (by evm_ov)
  have hzxRoundNat : zxRound.toNat = zx.toNat + half.toNat := by
    change (zx + half).toNat = zx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [zx, x', xxRound, xx] using hfitZXRound)]
  have hltZX : UInt256.lt zxRound zx = ⟨0⟩ := by
    apply ult_zero
    rw [hzxRoundNat]
    omega
  have rd2284 := evm_run rd2273 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2289⟩ (by native_decide) (by evm_ov)]
  have hcondZXAdd : UInt256.isZero (UInt256.lt zxRound zx) ≠ ⟨0⟩ := by
    rw [hltZX]
    native_decide
  have rd2289 := rd2284.jumpiT (by native_decide) hcondZXAdd (by jump_dest) (by evm_ov)
  have rd2296 := evm_run rd2289 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2303 := evm_run rd2296 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨2196⟩ (by native_decide) (by evm_ov)]
  have rd2196 := rd2303.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x', zx, zxRound, z', n'] using rd2196⟩

set_option maxHeartbeats 4000000 in
theorem rpowLoopCoupled
    {cA gh bl σ σ₀ A I} {g half scratch x n b z : UInt256}
    {evm : EVM.State} {locals : Store}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C v : ℕ}
    (hRlen : R.length ≤ 1000)
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hle : n.toNat ≤ v)
    (rd2196 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2196⟩
      (half :: scratch :: z :: b :: n :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    (∃ xFinal zFinal localsFinal k' C',
      RpowLoopStore xFinal ⟨0⟩ b zFinal half localsFinal ∧
      ExecStmt config { contract := contract, locals := locals } evm
        (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody)
        (.ok { contract := contract, locals := localsFinal } evm) ∧
      RD jugBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
        (zFinal :: R) mem (UInt256.ofNat 6) out acc k' C') ∨
    (ExecStmt config { contract := contract, locals := locals } evm
        (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody) .reverted ∧
      RDrev jugBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  revert x n z locals k C
  induction v with
  | zero =>
      intro x n z locals k C hstore hle rd2196
      have hnNat : n.toNat = 0 := by omega
      have hn : n = ⟨0⟩ := uint256_toNat_eq_zero hnNat
      subst n
      have hwhile : evalExpr? config { contract := contract, locals := locals } evm
          (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
        hstore.eval_while_false
      obtain ⟨k', C', rd1524⟩ :=
        RD.jugDripRpowLoopExit (R := R) hRlen (by simpa using rd2196)
      exact .inl ⟨x, z, locals, k', C', hstore,
        ExecStmt.whileFalse hwhile, rd1524⟩
  | succ v ih =>
      intro x n z locals k C hstore hle rd2196
      by_cases hnz : n = ⟨0⟩
      · subst n
        have hwhile : evalExpr? config { contract := contract, locals := locals } evm
            (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
          hstore.eval_while_false
        obtain ⟨k', C', rd1524⟩ :=
          RD.jugDripRpowLoopExit (R := R) hRlen (by simpa using rd2196)
        exact .inl ⟨x, z, locals, k', C', hstore,
          ExecStmt.whileFalse hwhile, rd1524⟩
      · have hcond : evalExpr? config { contract := contract, locals := locals } evm
            (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) :=
          hstore.eval_while_true hnz
        obtain ⟨_, _, rd2203⟩ :=
          RD.jugDripRpowLoopBodyEntry (R := R) hRlen hnz rd2196
        by_cases hoverXX : UInt256.size ≤ x.toNat * x.toNat
        · have hbody : ExecBlock config { contract := contract, locals := locals } evm
              rpowLoopBody .reverted :=
            execRpowLoopBodyRevertXX hstore hoverXX
          have hrev := RD.jugDripRpowLoopRevertXX (R := R) hRlen hoverXX rd2203
          exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
        · have hfitXX : x.toNat * x.toNat < UInt256.size := Nat.lt_of_not_ge hoverXX
          by_cases hoverXXRound : UInt256.size ≤ (x * x).toNat + half.toNat
          · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                rpowLoopBody .reverted :=
              execRpowLoopBodyRevertXXRound hstore hfitXX hoverXXRound
            have hrev := RD.jugDripRpowLoopRevertXXRound
              (R := R) hRlen hfitXX hoverXXRound rd2203
            exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
          · have hfitXXRound : (x * x).toNat + half.toNat < UInt256.size :=
              Nat.lt_of_not_ge hoverXXRound
            have hnextLe : (UInt256.div n ⟨2⟩).toNat ≤ v :=
              rpow_div_two_toNat_le_pred hnz hle
            by_cases hodd : n.toNat % 2 ≠ 0
            · by_cases hoverZX :
                  UInt256.size ≤ z.toNat * (UInt256.div ((x * x) + half) b).toNat
              · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                    rpowLoopBody .reverted :=
                  execRpowLoopBodyRevertZX hstore hb hfitXX hfitXXRound hodd hoverZX
                have hrev := RD.jugDripRpowLoopRevertZX
                  (R := R) hRlen hfitXX hfitXXRound hodd hoverZX rd2203
                exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
              · have hfitZX :
                    z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size :=
                  Nat.lt_of_not_ge hoverZX
                by_cases hoverZXRound :
                    UInt256.size ≤
                      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat
                · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                      rpowLoopBody .reverted :=
                    execRpowLoopBodyRevertZXRound hstore hb hfitXX hfitXXRound hodd
                      hfitZX hoverZXRound
                  have hrev := RD.jugDripRpowLoopRevertZXRound
                    (R := R) hRlen hfitXX hfitXXRound hodd hfitZX hoverZXRound rd2203
                  exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
                · have hfitZXRound :
                      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat <
                        UInt256.size :=
                    Nat.lt_of_not_ge hoverZXRound
                  obtain ⟨locals', hbody, hstore'⟩ :=
                    execRpowLoopBodyOkOdd (evm := evm) (locals := locals)
                      hstore hb hfitXX hfitXXRound hodd hfitZX hfitZXRound
                  obtain ⟨_, _, rdNext⟩ := RD.jugDripRpowLoopStepOdd
                    (R := R) hRlen hfitXX hfitXXRound hodd hfitZX hfitZXRound rd2203
                  have hrec := ih
                    (x := UInt256.div ((x * x) + half) b)
                    (n := UInt256.div n ⟨2⟩)
                    (z := UInt256.div
                      ((z * UInt256.div ((x * x) + half) b) + half) b)
                    (locals := locals') hstore' hnextLe (by simpa using rdNext)
                  cases hrec with
                  | inl hsucc =>
                      rcases hsucc with
                        ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                          hwhileRec, rd1524⟩
                      exact .inl ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                        ExecStmt.whileTrue hcond hbody hwhileRec, rd1524⟩
                  | inr hrev =>
                      rcases hrev with ⟨hwhileRec, hrdRev⟩
                      exact .inr ⟨ExecStmt.whileTrue hcond hbody hwhileRec, hrdRev⟩
            · have heven : n.toNat % 2 = 0 := by
                omega
              obtain ⟨locals', hbody, hstore'⟩ :=
                execRpowLoopBodyOkEven (evm := evm) (locals := locals)
                  hstore hb hfitXX hfitXXRound heven
              obtain ⟨_, _, rdNext⟩ := RD.jugDripRpowLoopStepEven
                (R := R) hRlen hfitXX hfitXXRound heven rd2203
              have hrec := ih
                (x := UInt256.div ((x * x) + half) b)
                (n := UInt256.div n ⟨2⟩)
                (z := z)
                (locals := locals') hstore' hnextLe (by simpa using rdNext)
              cases hrec with
              | inl hsucc =>
                  rcases hsucc with
                    ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                      hwhileRec, rd1524⟩
                  exact .inl ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                    ExecStmt.whileTrue hcond hbody hwhileRec, rd1524⟩
              | inr hrev =>
                  rcases hrev with ⟨hwhileRec, hrdRev⟩
                  exact .inr ⟨ExecStmt.whileTrue hcond hbody hwhileRec, hrdRev⟩

end Benchmarks.Dss.Jug
