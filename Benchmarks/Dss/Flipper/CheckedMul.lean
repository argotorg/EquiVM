import Benchmarks.Dss.Flipper.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flipper

/-! ## Shared checked multiplication helpers -/

abbrev flipperONEWord : UInt256 :=
  ⟨1000000000000000000⟩

-- LIBRARY CANDIDATE: generic Solm variable evaluation for uint256-valued locals.
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

theorem evalExpr_flipperONE {evm : EVM.State} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit ONE) =
      .ok (.int (Int.ofNat flipperONEWord.toNat)) := by
  have hone : Int.ofNat flipperONEWord.toNat = ONE := by native_decide
  simpa [evalExpr?, pure, hone]

theorem evalExpr_flipperBeg_of_get {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbeg : locals.get? "beg" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage begRef) =
        .ok (.int (Int.ofNat (flipperSlotWord ⟨4⟩ σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (slot := begRef)
    (er := ({ base := "beg", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨4⟩)
    (hbase := hbeg)
    (her := by simp [begRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨4⟩)

-- LIBRARY CANDIDATE: UInt256 multiplication by zero for the named `UInt256.mul`.
theorem flipper_uint256_mul_zero (x : UInt256) :
    UInt256.mul x (⟨0⟩ : UInt256) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  rfl

-- LIBRARY CANDIDATE: UInt256 checked multiplication no-overflow division check.
theorem flipper_u256_mul_div_right_eq_of_noOverflow (x y : UInt256) (hy : y ≠ ⟨0⟩)
    (h : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt h]
  have hyNat : 0 < y.toNat := by
    have hyne : y.toNat ≠ 0 := by
      intro hz
      apply hy
      exact uint256_toNat_eq_zero hz
    omega
  rw [Nat.mul_comm]
  exact Nat.mul_div_right x.toNat hyNat

-- LIBRARY CANDIDATE: UInt256 checked multiplication overflow fails the solc division guard.
theorem flipper_u256_mul_div_overflow_ne (x y : UInt256)
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
  have hle0 := Nat.mul_div_le (x.toNat * y.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : x.toNat * y.toNat ≤ x.toNat * y.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

-- LIBRARY CANDIDATE: Solm uint256 multiplication range check succeeds when the word product fits.
theorem evalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = UInt256.mul a b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

-- LIBRARY CANDIDATE: Solm uint256 multiplication range check reverts when the product overflows.
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

-- LIBRARY CANDIDATE: Solm uint256 division expression for nonzero uint256 divisors.
theorem evalExpr_div_uint256_ok {evm : EVM.State} {locals : Store}
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

-- LIBRARY CANDIDATE: typed integer equality expression success.
theorem evalExpr_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

-- LIBRARY CANDIDATE: typed integer equality expression failure.
theorem evalExpr_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

-- LIBRARY CANDIDATE: typed uint256 less-or-equal expression success.
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

-- LIBRARY CANDIDATE: typed uint256 less-or-equal expression failure.
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

-- LIBRARY CANDIDATE: typed uint256 greater-or-equal expression success.
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

-- LIBRARY CANDIDATE: typed uint256 greater-or-equal expression failure.
theorem evalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

-- LIBRARY CANDIDATE: short-circuiting `||` when the left operand is true.
theorem evalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

-- LIBRARY CANDIDATE: short-circuiting `||` when the left operand is false.
theorem evalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

-- LIBRARY CANDIDATE: source-side checked multiplication division guard.
theorem evalExpr_checkedMulRequire_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hz : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat prod.toNat)))
    (hprod : prod = UInt256.mul a b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) =
        .ok (.bool true) := by
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  by_cases hb : b = ⟨0⟩
  · have hleft :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_eq_int_true hy hzeroLit
      rw [hb]
    exact evalExpr_or_true_left hleft
  · have hleft :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool false) := by
      apply evalExpr_eq_int_false hy hzeroLit
      intro hbad
      exact hb (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    have hdivWord : UInt256.div prod b = a := by
      rw [hprod]
      exact flipper_u256_mul_div_right_eq_of_noOverflow a b hb hfit
    have hdiv :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .div (.var name) y) = .ok (.int (Int.ofNat a.toNat)) := by
      have h := evalExpr_div_uint256_ok (evm := evm) (locals := locals)
        (x := .var name) (y := y) (a := prod) (b := b)
        (q := UInt256.div prod b) hz hy hb rfl
      simpa [hdivWord] using h
    have hright :
        evalExpr? config { contract := contract, locals := locals } evm
          (.binary .eq (.binary .div (.var name) y) x) =
            .ok (.bool true) :=
      evalExpr_eq_int_true hdiv hx rfl
    exact evalExpr_or_false_right hleft hright

set_option maxHeartbeats 1000000 in
theorem flipperCheckedMulOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret x y : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hret : (D_J flipperBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨6305⟩ (y :: x :: ret :: R)
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ret (UInt256.mul x y :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd6314 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨6332⟩ (by native_decide) (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · rw [hy0] at rd6314
    have rd6332 := rd6314.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rd6299pre := evm_run rd6332 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨6299⟩ (by native_decide) (by evm_ov)]
    have rd6299 := rd6299pre.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rdret := evm_run rd6299 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jump (by native_decide) hret (by evm_ov)]
    exact ⟨_, _, by simpa [hy0, flipper_uint256_mul_zero] using rdret⟩
  · have hyNonzero : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    rw [hyNonzero] at rd6314
    have rd6315 := rd6314.jumpiNT (by native_decide)
      (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
    have rd6327pre := evm_run rd6315 with [
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw mul (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨6329⟩ (by native_decide) (by evm_ov)]
    have rd6329 := rd6327pre.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
    have hdiv : UInt256.div (UInt256.mul x y) y = x :=
      flipper_u256_mul_div_right_eq_of_noOverflow x y hy0 hfit
    have rd6332pre := evm_run rd6329 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov)]
    rw [hdiv, u256_eq_refl] at rd6332pre
    have rd6299pre := evm_run rd6332pre with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨6299⟩ (by native_decide) (by evm_ov)]
    have rd6299 := rd6299pre.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rdret := evm_run rd6299 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jump (by native_decide) hret (by evm_ov)]
    exact ⟨_, _, by simpa using rdret⟩

set_option maxHeartbeats 1000000 in
theorem flipperCheckedMulRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret x y : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hov : R.length + 10 ≤ 1024)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD flipperBytecode I g s0 ⟨6305⟩ (y :: x :: ret :: R)
      mem aw rdata (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have hy0 : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (UInt256.mul x y) y ≠ x :=
    flipper_u256_mul_div_overflow_ne x y hover
  have rd6314 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨6332⟩ (by native_decide) (by evm_ov)]
  have hyNonzero : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
  rw [hyNonzero] at rd6314
  have rd6315 := rd6314.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd6327pre := evm_run rd6315 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨6329⟩ (by native_decide) (by evm_ov)]
  have rd6329 := rd6327pre.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
  have rd6332pre := evm_run rd6329 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (UInt256.div (UInt256.mul x y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  rw [heq] at rd6332pre
  have rd6337 := evm_run rd6332pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨6299⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  exact RD.uniswapPush1Dup1Revert0 rd6337
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

end Benchmarks.Dss.Flipper
