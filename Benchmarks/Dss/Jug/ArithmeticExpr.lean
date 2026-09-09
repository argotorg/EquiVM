import Benchmarks.Dss.Jug.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

/-! ## Solm-side arithmetic helpers for `drip` -/

abbrev jugRay : UInt256 :=
  ⟨1000000000000000000000000000⟩

theorem jugRay_toNat : jugRay.toNat = 1000000000000000000000000000 := by
  change (UInt256.ofNat 1000000000000000000000000000).toNat =
    1000000000000000000000000000
  exact ulit_toNat' _ (by decide +native)

theorem jugUInt256Zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := by
  decide +native

theorem jugUInt256One_toNat : (⟨1⟩ : UInt256).toNat = 1 := by
  decide +native

theorem jugUInt256Two_toNat : (⟨2⟩ : UInt256).toNat = 2 := by
  decide +native

theorem jugUInt256Two_ne_zero : (⟨2⟩ : UInt256) ≠ ⟨0⟩ := by
  decide +native

theorem jugUInt256DivZeroTwo :
    UInt256.div (⟨0⟩ : UInt256) (⟨2⟩ : UInt256) = ⟨0⟩ := by
  decide +native

theorem jugUInt256DivOneTwo :
    UInt256.div (⟨1⟩ : UInt256) (⟨2⟩ : UInt256) = ⟨0⟩ := by
  decide +native

theorem one_eq_jugRay_toNat : one = Int.ofNat jugRay.toNat := by
  simp [one, jugRay_toNat]

theorem jugRay_mul_div_cancel (y : UInt256)
    (hfit : jugRay.toNat * y.toNat < UInt256.size) :
    UInt256.div (y * jugRay) jugRay = y := by
  apply u256_inj
  rw [udiv_toNat]
  have hfit' : y.toNat * jugRay.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hfit
  have hprod : (y * jugRay).toNat = y.toNat * jugRay.toNat := by
    rw [umul_toNat y jugRay hfit']
  have hRayPos : 0 < jugRay.toNat := by
    rw [jugRay_toNat]
    norm_num
  rw [hprod]
  simpa [Nat.mul_comm] using Nat.mul_div_right y.toNat hRayPos

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

theorem jugRay_mul_div_overflow_ne (y : UInt256)
    (hover : UInt256.size ≤ jugRay.toNat * y.toNat) :
    UInt256.div (y * jugRay) y ≠ jugRay :=
  u256_mul_div_overflow_ne jugRay y hover

theorem u256_sub_eq_zero_iff_eq {a b : UInt256} :
    UInt256.sub a b = ⟨0⟩ ↔ a = b := by
  constructor
  · intro h
    by_contra hne
    exact u256_sub_ne_zero_of_ne hne h
  · intro h
    rw [h]
    exact u256_sub_self b

theorem evalExpr_varInt {evm : EVM.State} {locals : Store}
    {name : Ident} {value : Int}
    (h : locals.get? name = some (.int value)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int value) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok (.int value)
  rw [h]
  rfl

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
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm (.binary .le y x) =
        .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
    exact_mod_cast hle
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  have hchecked :
      evalExpr? config { contract := contract, locals := locals } evm (checkedSub256 x y) =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simp [checkedSub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
      uint256Int]
    rw [if_neg]
    · rw [hsubInt, ← hdiffNat]
      rfl
    · intro hbad
      rcases hbad with hbad | hbad
      · exact (not_le.mpr hbad) hle
      · rw [hsubInt] at hbad
        exact hlt hbad
  simp [sub256, evalExpr?, EvalResult.bind, bind, hcond, hchecked]

theorem evalExpr_sub256_underflow_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm (.binary .le y x) =
        .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
    exact_mod_cast hlt
  have hbLe : b.toNat ≤ UInt256.size + a.toNat := by
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hdiffNat : diff.toNat = UInt256.size + a.toNat - b.toNat := by
    rw [hdiff, usub_toNat_underflow hlt]
  have hsubInt :
      ((UInt256.size : Nat) : Int) + (a.toNat : Int) - (b.toNat : Int) =
        ((UInt256.size + a.toNat - b.toNat : Nat) : Int) := by
    rw [← Nat.cast_add, ← Int.ofNat_sub hbLe]
  have hltNat : UInt256.size + a.toNat - b.toNat < UInt256.size := by
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hltRange :
      ¬ ((UInt256.size + a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  have hwrapped :
      evalExpr? config { contract := contract, locals := locals } evm
          (u256 (.binary .sub (.binary .add (.intLit (Int.ofNat UInt256.size)) x) y)) =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
    rw [if_neg]
    · have hval :
          ((UInt256.size : Nat) : Int) + (a.toNat : Int) - (b.toNat : Int) =
            (diff.toNat : Int) := by
        rw [hsubInt, ← hdiffNat]
      change pure (Value.int
          (((UInt256.size : Nat) : Int) + (a.toNat : Int) - (b.toNat : Int))) =
        EvalResult.ok (.int (Int.ofNat diff.toNat))
      rw [hval]
      rfl
    · intro hbad
      rcases hbad with hbad | hbad
      · omega
      · have hbad' :
            ((UInt256.size + a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 := by
          rwa [hsubInt] at hbad
        exact hltRange hbad'
  simpa [sub256, evalExpr?, EvalResult.bind, bind, hcond] using hwrapped

theorem evalExpr_sub256_word_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  by_cases hle : b.toNat ≤ a.toNat
  · exact evalExpr_sub256_ok hx hy hdiff hle
  · exact evalExpr_sub256_underflow_ok hx hy hdiff (Nat.lt_of_not_ge hle)

theorem evalExpr_checkedSub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (checkedSub256 x y) =
      .revert := by
  simp [checkedSub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int]
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
    rw [hprod, umul_toNat a b hfit]
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

theorem evalExpr_mod_int_ok {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b r : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hb : b ≠ 0) (hr : r = a % b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .mod lhs rhs) =
      .ok (.int r) := by
  subst r
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hb]

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

theorem evalExpr_le_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hle

theorem evalExpr_le_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : b < a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hlt

theorem evalExpr_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

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

theorem evalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

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

theorem evalExpr_s256_ok {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? config { contract := contract, locals := locals } evm e = .ok (.int i))
    (hlo : -((2 : Int) ^ 255) ≤ i) (hhi : i < (2 : Int) ^ 255) :
    evalExpr? config { contract := contract, locals := locals } evm (s256 e) =
      .ok (.int i) := by
  have hnlo : ¬ i < -((2 : Int) ^ 255) := not_lt.mpr hlo
  have hnhi : ¬ i ≥ (2 : Int) ^ 255 := not_le.mpr hhi
  simp [s256, int256Int, evalExpr?, EvalResult.bind, bind, he]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact hnlo (by simpa using hbad)
    · exact hnhi (by simpa using hbad)

theorem evalExpr_s256_revert {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? config { contract := contract, locals := locals } evm e = .ok (.int i))
    (hbad : i < -((2 : Int) ^ 255) ∨ i ≥ (2 : Int) ^ 255) :
    evalExpr? config { contract := contract, locals := locals } evm (s256 e) = .revert := by
  simp [s256, int256Int, evalExpr?, EvalResult.bind, bind, he]
  by_cases hlo : i < -((2 : Int) ^ 255)
  · intro hge
    exact False.elim ((not_lt.mpr (by simpa using hge)) hlo)
  · have hhi : i ≥ (2 : Int) ^ 255 := by
      rcases hbad with hbad | hbad
      · exact False.elim (hlo hbad)
      · exact hbad
    intro _
    simpa using hhi

end Benchmarks.Dss.Jug
