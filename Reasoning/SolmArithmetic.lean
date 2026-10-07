import Reasoning.ABI
import Reasoning.SolmBody
import Reasoning.ABIComposite
import Reasoning.WordArithmetic

/-!
# Source arithmetic

Shared local stores and expression proofs for checked and wrapping arithmetic, comparisons,
conditionals, and signed ranges. The evaluation lemmas hold for every configuration and contract.
-/

open Solm ABI Ethereum Ethereum.EVM

set_option autoImplicit false

namespace Reasoning.Theory

abbrev sourceUInt256 : IntType := .uint ⟨256, by decide⟩
abbrev sourceInt256 : IntType := .sint ⟨256, by decide⟩
abbrev sourceCheckedUint256 (e : Expr) : Expr := .inRange sourceUInt256 e
abbrev sourceCheckedInt256 (e : Expr) : Expr := .inRange sourceInt256 e
abbrev sourceAdd256 (x y : Expr) : Expr := sourceCheckedUint256 (.binary .add x y)
abbrev sourceCheckedSub256 (x y : Expr) : Expr := sourceCheckedUint256 (.binary .sub x y)
abbrev sourceWrappingSub256 (x y : Expr) : Expr :=
  .ite (.binary .le y x)
    (sourceCheckedSub256 x y)
    (sourceCheckedUint256
      (.binary .sub (.binary .add (.intLit (Int.ofNat UInt256.size)) x) y))
abbrev sourceMul256 (x y : Expr) : Expr := sourceCheckedUint256 (.binary .mul x y)

abbrev uintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev uintBinaryLocalsZ (x y z : UInt256) : Store :=
  (uintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem uintBinaryLocals_get_x (x y : UInt256) :
    (uintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocals, store_get_self]

theorem uintBinaryLocals_get_y (x y : UInt256) :
    (uintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintBinaryLocalsZ_get_x (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_x]

theorem uintBinaryLocalsZ_get_z (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_self]

abbrev uintBinaryLocalsZAssigned (x y old new : UInt256) : Store :=
  (uintBinaryLocalsZ x y old).insert "z" (.int (Int.ofNat new.toNat))

abbrev uintBinaryLocalsIntZ (x y : UInt256) (z : Int) : Store :=
  (uintBinaryLocals x y).insert "z" (.int z)

theorem uintBinaryLocalsZ_get_y (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_y]

theorem uintBinaryLocalsZAssigned_get_z (x y old new : UInt256) :
    (uintBinaryLocalsZAssigned x y old new).get? "z" =
      some (.int (Int.ofNat new.toNat)) := by
  rw [uintBinaryLocalsZAssigned, store_get_self]

theorem uintBinaryLocalsIntZ_get_x (x y : UInt256) (z : Int) :
    (uintBinaryLocalsIntZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocalsIntZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_x]

theorem uintBinaryLocalsIntZ_get_y (x y : UInt256) (z : Int) :
    (uintBinaryLocalsIntZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocalsIntZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_y]

theorem uintBinaryLocalsIntZ_get_z (x y : UInt256) (z : Int) :
    (uintBinaryLocalsIntZ x y z).get? "z" = some (.int z) := by
  rw [uintBinaryLocalsIntZ, store_get_self]

theorem evalExpr_varInt {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {name : Ident} {value : Int}
    (h : locals.get? name = some (.int value)) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var name) =
      .ok (.int value) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok (.int value)
  rw [h]
  rfl

theorem evalExpr_varUInt256 {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_add256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceAdd256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [sourceAdd256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    sourceUInt256, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_add256_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceAdd256 x y) =
      .revert := by
  simp [sourceAdd256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy,
    evalBinaryOp?, sourceUInt256]
  intro _
  exact_mod_cast hover

theorem evalExpr_wrappingSub256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceWrappingSub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hcond :
      evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le y x) =
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
      evalExpr? cfg { contract := contract, locals := locals } evm (sourceCheckedSub256 x y) =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simp [sourceCheckedSub256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy,
      evalBinaryOp?,
      sourceUInt256]
    rw [if_neg]
    · rw [hsubInt, ← hdiffNat]
      rfl
    · intro hbad
      rcases hbad with hbad | hbad
      · exact (not_le.mpr hbad) hle
      · rw [hsubInt] at hbad
        exact hlt hbad
  simp [sourceWrappingSub256, evalExpr?, EvalResult.bind, bind, hcond, hchecked]

theorem evalExpr_wrappingSub256_underflow_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceWrappingSub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hcond :
      evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le y x) =
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
      evalExpr? cfg { contract := contract, locals := locals } evm
          (sourceCheckedUint256
            (.binary .sub (.binary .add (.intLit (Int.ofNat UInt256.size)) x) y)) =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simp [sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
      sourceUInt256]
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
  simpa [sourceWrappingSub256, evalExpr?, EvalResult.bind, bind, hcond] using hwrapped

theorem evalExpr_wrappingSub256_word_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceWrappingSub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  by_cases hle : b.toNat ≤ a.toNat
  · exact evalExpr_wrappingSub256_ok hx hy hdiff hle
  · exact evalExpr_wrappingSub256_underflow_ok hx hy hdiff (Nat.lt_of_not_ge hle)

theorem evalExpr_checkedSub256_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceCheckedSub256 x y) =
      .revert := by
  simp [sourceCheckedSub256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy,
    evalBinaryOp?,
    sourceUInt256]
  intro hle
  exact False.elim (not_le.mpr hlt hle)

theorem evalExpr_mul256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceMul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [sourceMul256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    sourceUInt256, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_mul256_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceMul256 x y) =
      .revert := by
  simp [sourceMul256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy,
    evalBinaryOp?, sourceUInt256]
  intro _
  exact_mod_cast hover

theorem evalExpr_div_uint256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem evalExpr_mod_int_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b r : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hb : b ≠ 0) (hr : r = a % b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .mod lhs rhs) =
      .ok (.int r) := by
  subst r
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hb]

theorem evalExpr_le_uint256_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

theorem evalExpr_le_uint256_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : b.toNat < a.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

theorem evalExpr_ge_uint256_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_ge_uint256_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

theorem evalExpr_le_int_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hle

theorem evalExpr_le_int_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : b < a) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hlt

theorem evalExpr_eq_int_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_eq_int_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_ne_int_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_ne_int_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool false) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_or_true_left {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_or_false_right {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? cfg { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? cfg { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_ite_true {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? cfg { contract := contract, locals := locals } evm cond =
      .ok (.bool true))
    (hthen : evalExpr? cfg { contract := contract, locals := locals } evm thenExpr =
      .ok value) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value := by
  simp [evalExpr?, EvalResult.bind, bind, hcond, hthen]

theorem evalExpr_ite_false {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? cfg { contract := contract, locals := locals } evm cond =
      .ok (.bool false))
    (helse : evalExpr? cfg { contract := contract, locals := locals } evm elseExpr =
      .ok value) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value := by
  simp [evalExpr?, EvalResult.bind, bind, hcond, helse]

theorem evalExpr_s256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? cfg { contract := contract, locals := locals } evm e = .ok (.int i))
    (hlo : -((2 : Int) ^ 255) ≤ i) (hhi : i < (2 : Int) ^ 255) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceCheckedInt256 e) =
      .ok (.int i) := by
  have hnlo : ¬ i < -((2 : Int) ^ 255) := not_lt.mpr hlo
  have hnhi : ¬ i ≥ (2 : Int) ^ 255 := not_le.mpr hhi
  simp [sourceCheckedInt256, sourceInt256, evalExpr?, EvalResult.bind, bind, he]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact hnlo (by simpa using hbad)
    · exact hnhi (by simpa using hbad)

theorem evalExpr_s256_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? cfg { contract := contract, locals := locals } evm e = .ok (.int i))
    (hbad : i < -((2 : Int) ^ 255) ∨ i ≥ (2 : Int) ^ 255) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceCheckedInt256 e) = .revert
      := by
  simp [sourceCheckedInt256, sourceInt256, evalExpr?, EvalResult.bind, bind, he]
  by_cases hlo : i < -((2 : Int) ^ 255)
  · intro hge
    exact False.elim ((not_lt.mpr (by simpa using hge)) hlo)
  · have hhi : i ≥ (2 : Int) ^ 255 := by
      rcases hbad with hbad | hbad
      · exact False.elim (hlo hbad)
      · exact hbad
    intro _
    simpa using hhi

theorem evalExpr_checkedSub256_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm (sourceCheckedSub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sourceCheckedSub256, sourceCheckedUint256, evalExpr?, EvalResult.bind, bind, hx, hy,
    evalBinaryOp?, sourceUInt256]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_checkedMulRequire_ok {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {a b prod : UInt256}
    (hx : evalExpr? cfg { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hz : evalExpr? cfg { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat prod.toNat)))
    (hprod : prod = UInt256.mul a b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) =
        .ok (.bool true) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  by_cases hb : b = ⟨0⟩
  · have hleft :
        evalExpr? cfg { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_eq_int_true hy hzeroLit
      rw [hb]
    exact evalExpr_or_true_left hleft
  · have hleft :
        evalExpr? cfg { contract := contract, locals := locals } evm
          (.binary .eq y (.intLit 0)) = .ok (.bool false) := by
      apply evalExpr_eq_int_false hy hzeroLit
      intro hbad
      exact hb (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    have hdivWord : UInt256.div prod b = a := by
      rw [hprod]
      exact u256_mul_div_right_eq_of_noOverflow a b hb hfit
    have hdiv :
        evalExpr? cfg { contract := contract, locals := locals } evm
          (.binary .div (.var name) y) = .ok (.int (Int.ofNat a.toNat)) := by
      have h := evalExpr_div_uint256_ok (evm := evm) (locals := locals)
        (x := .var name) (y := y) (a := prod) (b := b)
        (q := UInt256.div prod b) hz hy hb rfl
      simpa [hdivWord] using h
    have hright :
        evalExpr? cfg { contract := contract, locals := locals } evm
          (.binary .eq (.binary .div (.var name) y) x) =
            .ok (.bool true) :=
      evalExpr_eq_int_true hdiv hx rfl
    exact evalExpr_or_false_right hleft hright

theorem assignLocalVarBase_ok {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store}
    {name : Ident} {old value : Value}
    (hget : locals.get? name = some old) :
    assignStorageRef? cfg { contract := contract, locals := locals } evm .localVar
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

theorem evalExpr_mod_intLit {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {x modulus : Int} (he : evalExpr? cfg frame evm e = .ok (.int x))
    (hmodulus : modulus ≠ 0) :
    evalExpr? cfg frame evm (.binary .mod e (.intLit modulus)) =
      .ok (.int (x % modulus)) := by
  rw [evalExpr?]
  · simp only [he, evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hmodulus,
      ↓reduceIte]
  · decide
  · decide


/-- Reading a plain variable from the locals. -/
theorem evalLocalVar {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State}
    {name : Ident}
    {v : Value} (h : L.get? name = some v) :
    evalExpr? cfg { contract := C, locals := L } evm (.var name) = .ok v := by
  simp only [evalExpr?, EvalResult.ofOption, h]


end Reasoning.Theory

namespace Reasoning.Theory.RpowB

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

abbrev uintTernaryLocals (x n b : UInt256) : Store :=
  ((((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert "n"
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
    (uintTernaryLocals x n b).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem rpowLocalsZ_get_b (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_b]

theorem rpowLocalsZ_get_n (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_n]

theorem rpowLocalsZH_get_b (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "b" = some (.int (Int.ofNat b.toNat)) := by
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
    (rpowLocalsZHN x n b z half n').get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH_get_b]

theorem rpowLocalsZHN_get_half (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "half" =
      some (.int (Int.ofNat half.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH, store_get_self]

structure RpowLoopStore (x n b z half : UInt256) (locals : Store) : Prop where
  get_x : locals.get? "x" = some (.int (Int.ofNat x.toNat))
  get_n : locals.get? "n" = some (.int (Int.ofNat n.toNat))
  get_b : locals.get? "b" = some (.int (Int.ofNat b.toNat))
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
    (hb : (name == "b") = false) (hz : (name == "z") = false)
    (hhalf : (name == "half") = false) :
    RpowLoopStore x n b z half (locals.insert name value) where
  get_x := by rw [store_get_ne locals (k := name) (a := "x") value hx, h.get_x]
  get_n := by rw [store_get_ne locals (k := name) (a := "n") value hn, h.get_n]
  get_b := by rw [store_get_ne locals (k := name) (a := "b") value hb, h.get_b]
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
    rw [store_get_ne locals (k := "x") (a := "b") (.int (Int.ofNat x'.toNat)) (by decide),
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
    rw [store_get_ne locals (k := "z") (a := "b") (.int (Int.ofNat z'.toNat)) (by decide),
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
    rw [store_get_ne locals (k := "n") (a := "b") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "n") (a := "z") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "n") (a := "half") (.int (Int.ofNat n'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.eval_x {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x") (value := x) h.get_x

theorem RpowLoopStore.eval_n {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "n") (value := n) h.get_n

theorem RpowLoopStore.eval_b {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "b") =
      .ok (.int (Int.ofNat b.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "b") (value := b) h.get_b

theorem RpowLoopStore.eval_z {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "z") (value := z) h.get_z

theorem RpowLoopStore.eval_half {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "half") (value := half)
    h.get_half

theorem RpowLoopStore.eval_while_false {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_false h.eval_n hzeroLit rfl

theorem RpowLoopStore.eval_while_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  apply evalExpr_ne_int_true h.eval_n hzeroLit
  intro hbad
  exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem RpowLoopStore.eval_odd_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) := by
  have htwoLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, uInt256Two_toNat]
  have hmod :
      evalExpr? cfg { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [uInt256Two_toNat])
      (by
        rw [uInt256Two_toNat]
        norm_num)
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_true hmod hzeroLit (by
    intro hbad
    apply hodd
    exact Nat.cast_injective hbad)

end Reasoning.Theory.RpowB

namespace Reasoning.Theory.RpowBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

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

theorem RpowLoopStore.eval_x {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x") (value := x) h.get_x

theorem RpowLoopStore.eval_n {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "n") (value := n) h.get_n

theorem RpowLoopStore.eval_b {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "base") =
      .ok (.int (Int.ofNat b.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "base") (value := b) h.get_b

theorem RpowLoopStore.eval_z {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "z") (value := z) h.get_z

theorem RpowLoopStore.eval_half {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "half") (value := half)
    h.get_half

theorem RpowLoopStore.eval_while_false {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_false h.eval_n hzeroLit rfl

theorem RpowLoopStore.eval_while_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  apply evalExpr_ne_int_true h.eval_n hzeroLit
  intro hbad
  exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem RpowLoopStore.eval_odd_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) := by
  have htwoLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, uInt256Two_toNat]
  have hmod :
      evalExpr? cfg { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [uInt256Two_toNat])
      (by
        rw [uInt256Two_toNat]
        norm_num)
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_true hmod hzeroLit (by
    intro hbad
    apply hodd
    exact Nat.cast_injective hbad)

end Reasoning.Theory.RpowBase

/-! ## Timestamp conversions, address casts, and exponentiation frames -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem timestamp_add_duration_word_eq_left (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      UInt256.ofNat evm.executionEnv.header.timestamp + EVM.word biddingTime.toNat :=
  constructorCheckedAddIntWordBaseFirst_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

theorem timestamp_add_duration_word_eq (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      EVM.word biddingTime.toNat + UInt256.ofNat evm.executionEnv.header.timestamp :=
  constructorCheckedAddIntWord_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

theorem cast_addressAsUint256 (w : UInt256) :
    castValue? (.address (AccountAddress.ofNat w.toNat)) packedUInt256StorageType =
      some (.int (Int.ofNat (UInt256.land solcAddrMask w).toNat)) := by
  have haddr : (AccountAddress.ofNat w.toNat).toNat =
      (UInt256.land solcAddrMask w).toNat := accountAddress_ofNat_toNat_eq_mask w
  have hlt : (AccountAddress.ofNat w.toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide)
  simp only [castValue?, packedUInt256StorageType, abiUInt256Int]
  rw [if_pos hlt]
  rw [haddr]

end Reasoning.Theory
