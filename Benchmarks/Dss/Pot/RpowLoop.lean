import Benchmarks.Dss.Pot.Arith

/-!
# MakerDAO/Sky DSS Pot `_rpow` loop: Solm-side locals + expression helpers

Ported from the fully-proved sibling `Benchmarks/Dss/Jug`
(`ArithmeticExpr.lean` additions + `ArithmeticLocals.lean` + `ArithmeticRpowLoop.lean`).
The Solm base-of-exponentiation variable is named `"base"` in Pot (vs `"b"` in Jug).
Every declaration here is contract-independent (`LIBRARY CANDIDATE`): it exercises only
`evalExpr?`/`Store` on the ternary/rpow locals frame.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## Word/expression helpers not already present in `ArithExpr` -/

theorem potUInt256One_toNat : (⟨1⟩ : UInt256).toNat = 1 := by
  decide +native

theorem potUInt256Two_toNat : (⟨2⟩ : UInt256).toNat = 2 := by
  decide +native

theorem potUInt256Two_ne_zero : (⟨2⟩ : UInt256) ≠ ⟨0⟩ := by
  decide +native

theorem u256_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (y * x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_op_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 :=
    Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem evalExpr_mod_int_ok {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b r : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hb : b ≠ 0) (hr : r = a % b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .mod lhs rhs) =
      .ok (.int r) := by
  subst r
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hb]

theorem evalExpr_ne_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_ne_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool false) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_ite_true {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? config { contract := contract, locals := locals } evm cond =
      .ok (.bool true))
    (hthen : evalExpr? config { contract := contract, locals := locals } evm thenExpr =
      .ok value) :
    evalExpr? config { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value := by
  simp [evalExpr?, EvalResult.bind, bind, hcond, hthen]

theorem evalExpr_ite_false {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? config { contract := contract, locals := locals } evm cond =
      .ok (.bool false))
    (helse : evalExpr? config { contract := contract, locals := locals } evm elseExpr =
      .ok value) :
    evalExpr? config { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value := by
  simp [evalExpr?, EvalResult.bind, bind, hcond, helse]

/-! ## Ternary/rpow locals frames + `RpowLoopStore` (ported from Jug `ArithmeticLocals`) -/

abbrev uintTernaryLocals (x n b : UInt256) : Store :=
  ((((∅ : Store).insert "base" (.int (Int.ofNat b.toNat))).insert "n"
    (.int (Int.ofNat n.toNat))).insert "x" (.int (Int.ofNat x.toNat)))

abbrev rpowLocalsZ (x n b z : UInt256) : Store :=
  (uintTernaryLocals x n b).insert "z" (.int (Int.ofNat z.toNat))

abbrev rpowLocalsZH (x n b z half : UInt256) : Store :=
  (rpowLocalsZ x n b z).insert "half" (.int (Int.ofNat half.toNat))

abbrev rpowLocalsZHN (x n b z half n' : UInt256) : Store :=
  (rpowLocalsZH x n b z half).insert "n" (.int (Int.ofNat n'.toNat))

theorem uintTernaryLocals_get_x (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintTernaryLocals, store_get_self]

theorem uintTernaryLocals_get_n (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintTernaryLocals_get_b (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem rpowLocalsZ_get_b (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_b]

theorem rpowLocalsZ_get_n (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_n]

theorem rpowLocalsZH_get_b (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_b]

theorem rpowLocalsZH_get_n (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_n]

theorem rpowLocalsZHN_get_n (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "n" = some (.int (Int.ofNat n'.toNat)) := by
  rw [rpowLocalsZHN, store_get_self]

theorem rpowLocalsZHN_get_z (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_self]

theorem rpowLocalsZHN_get_x (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_ne _ _ (by decide),
    uintTernaryLocals_get_x]

theorem rpowLocalsZHN_get_b (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH_get_b]

theorem rpowLocalsZHN_get_half (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "half" =
      some (.int (Int.ofNat half.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH, store_get_self]

structure RpowLoopStore (x n b z half : UInt256) (locals : Store) : Prop where
  get_x : locals.get? "x" = some (.int (Int.ofNat x.toNat))
  get_n : locals.get? "n" = some (.int (Int.ofNat n.toNat))
  get_b : locals.get? "base" = some (.int (Int.ofNat b.toNat))
  get_z : locals.get? "z" = some (.int (Int.ofNat z.toNat))
  get_half : locals.get? "half" = some (.int (Int.ofNat half.toNat))

theorem RpowLoopStore.rpowLocalsZHN (x n b z half n' : UInt256) :
    RpowLoopStore x n' b z half (rpowLocalsZHN x n b z half n') where
  get_x := rpowLocalsZHN_get_x x n b z half n'
  get_n := rpowLocalsZHN_get_n x n b z half n'
  get_b := rpowLocalsZHN_get_b x n b z half n'
  get_z := rpowLocalsZHN_get_z x n b z half n'
  get_half := rpowLocalsZHN_get_half x n b z half n'

theorem RpowLoopStore.insert_ne {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (name : Ident) (value : Value)
    (hx : (name == "x") = false) (hn : (name == "n") = false)
    (hb : (name == "base") = false) (hz : (name == "z") = false)
    (hhalf : (name == "half") = false) :
    RpowLoopStore x n b z half (locals.insert name value) where
  get_x := by rw [store_get_ne locals (k := name) (a := "x") value hx, h.get_x]
  get_n := by rw [store_get_ne locals (k := name) (a := "n") value hn, h.get_n]
  get_b := by rw [store_get_ne locals (k := name) (a := "base") value hb, h.get_b]
  get_z := by rw [store_get_ne locals (k := name) (a := "z") value hz, h.get_z]
  get_half := by rw [store_get_ne locals (k := name) (a := "half") value hhalf, h.get_half]

theorem RpowLoopStore.set_x {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (x' : UInt256) :
    RpowLoopStore x' n b z half (locals.insert "x" (.int (Int.ofNat x'.toNat))) where
  get_x := store_get_self locals "x" (.int (Int.ofNat x'.toNat))
  get_n := by
    rw [store_get_ne locals (k := "x") (a := "n") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "x") (a := "base") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "x") (a := "z") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "x") (a := "half") (.int (Int.ofNat x'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_z {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (z' : UInt256) :
    RpowLoopStore x n b z' half (locals.insert "z" (.int (Int.ofNat z'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "z") (a := "x") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_x]
  get_n := by
    rw [store_get_ne locals (k := "z") (a := "n") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "z") (a := "base") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_b]
  get_z := store_get_self locals "z" (.int (Int.ofNat z'.toNat))
  get_half := by
    rw [store_get_ne locals (k := "z") (a := "half") (.int (Int.ofNat z'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_n {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (n' : UInt256) :
    RpowLoopStore x n' b z half (locals.insert "n" (.int (Int.ofNat n'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "n") (a := "x") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_x]
  get_n := store_get_self locals "n" (.int (Int.ofNat n'.toNat))
  get_b := by
    rw [store_get_ne locals (k := "n") (a := "base") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "n") (a := "z") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "n") (a := "half") (.int (Int.ofNat n'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.eval_x {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x") (value := x) h.get_x

theorem RpowLoopStore.eval_n {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "n") (value := n) h.get_n

theorem RpowLoopStore.eval_b {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "base") =
      .ok (.int (Int.ofNat b.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "base") (value := b) h.get_b

theorem RpowLoopStore.eval_z {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "z") (value := z) h.get_z

theorem RpowLoopStore.eval_half {evm : EVM.State} {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "half") (value := half)
    h.get_half

theorem RpowLoopStore.eval_while_false {evm : EVM.State} {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) := by
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_false h.eval_n hzeroLit rfl

theorem RpowLoopStore.eval_while_true {evm : EVM.State} {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) := by
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  apply evalExpr_ne_int_true h.eval_n hzeroLit
  intro hbad
  exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

/-! ## `_rpow` loop-body single-step lemmas (ported from Jug `ArithmeticRpowLoop`) -/

theorem rpow_div_two_toNat_le_pred {n : UInt256} {v : ℕ}
    (hnz : n ≠ ⟨0⟩) (hle : n.toNat ≤ v + 1) :
    (UInt256.div n ⟨2⟩).toNat ≤ v := by
  have hnNatNe : n.toNat ≠ 0 := by
    intro hzero
    exact hnz (uint256_toNat_eq_zero hzero)
  have hnPos : 0 < n.toNat := Nat.pos_of_ne_zero hnNatNe
  have hlt : (UInt256.div n ⟨2⟩).toNat < n.toNat := by
    rw [udiv_toNat, potUInt256Two_toNat]
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
        (.binary .div (.var "xxRound") (.var "base")) =
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
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hmod :
      evalExpr? config { contract := contract, locals := localsX } evm
        (.binary .mod (.var "n") (.intLit 2)) = .ok (.int 0) := by
    exact evalExpr_mod_int_ok hstoreX.eval_n htwoLitX
      (by simp [potUInt256Two_toNat])
      (by
        rw [potUInt256Two_toNat]
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
    exact evalExpr_div_uint256_ok hstoreX.eval_n htwoLitX potUInt256Two_ne_zero rfl
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
          .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "base")),
          .ite
            (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
            (checkedMulUintInto "zx" (.var "z") (.var "x") ++
              checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
              [ .assign .localVar { base := "z" }
                  (.binary .div (.var "zxRound") (.var "base")) ])
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

end Benchmarks.Dss.Pot
