import Reasoning.WordArithmetic
import Reasoning.SolmArithmetic
import Reasoning.EVMWord
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
  exact ulit_toNat' _ (by native_decide)


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


theorem jugRay_mul_div_overflow_ne (y : UInt256)
    (hover : UInt256.size ≤ jugRay.toNat * y.toNat) :
    UInt256.div (y * jugRay) y ≠ jugRay :=
  u256_mul_div_overflow_ne jugRay y hover


theorem evalExpr_varInt {evm : EVM.State} {locals : Store}
    {name : Ident} {value : Int}
    (h : locals.get? name = some (.int value)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int value) :=
  Reasoning.Theory.evalExpr_varInt (cfg := config) (contract := contract) h

theorem evalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) :=
  Reasoning.Theory.evalExpr_varUInt256 (cfg := config) (contract := contract) h

theorem evalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) :=
  Reasoning.Theory.evalExpr_add256_ok (cfg := config) (contract := contract) hx hy hsum hfit

theorem evalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert :=
  Reasoning.Theory.evalExpr_add256_revert (cfg := config) (contract := contract) hx hy hover

theorem evalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) :=
  Reasoning.Theory.evalExpr_wrappingSub256_ok (cfg := config) (contract := contract) hx hy hdiff hle

theorem evalExpr_sub256_underflow_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) :=
  Reasoning.Theory.evalExpr_wrappingSub256_underflow_ok (cfg := config) (contract := contract) hx
    hy hdiff hlt

theorem evalExpr_sub256_word_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) :=
  Reasoning.Theory.evalExpr_wrappingSub256_word_ok (cfg := config) (contract := contract) hx hy
    hdiff

theorem evalExpr_checkedSub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (checkedSub256 x y) =
      .revert :=
  Reasoning.Theory.evalExpr_checkedSub256_revert (cfg := config) (contract := contract) hx hy hlt

theorem evalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) :=
  Reasoning.Theory.evalExpr_mul256_ok (cfg := config) (contract := contract) hx hy hprod hfit

theorem evalExpr_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .revert :=
  Reasoning.Theory.evalExpr_mul256_revert (cfg := config) (contract := contract) hx hy hover

theorem evalExpr_div_uint256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) :=
  Reasoning.Theory.evalExpr_div_uint256_ok (cfg := config) (contract := contract) hx hy hb hq

theorem evalExpr_mod_int_ok {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b r : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hb : b ≠ 0) (hr : r = a % b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .mod lhs rhs) =
      .ok (.int r) :=
  Reasoning.Theory.evalExpr_mod_int_ok (cfg := config) (contract := contract) hlhs hrhs hb hr

theorem evalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_le_uint256_true (cfg := config) (contract := contract) hlhs hrhs hle

theorem evalExpr_le_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) :=
  Reasoning.Theory.evalExpr_le_uint256_false (cfg := config) (contract := contract) hlhs hrhs hlt

theorem evalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_ge_uint256_true (cfg := config) (contract := contract) hlhs hrhs hge

theorem evalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) :=
  Reasoning.Theory.evalExpr_ge_uint256_false (cfg := config) (contract := contract) hlhs hrhs hlt

theorem evalExpr_le_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_le_int_true (cfg := config) (contract := contract) hlhs hrhs hle

theorem evalExpr_le_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : b < a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) :=
  Reasoning.Theory.evalExpr_le_int_false (cfg := config) (contract := contract) hlhs hrhs hlt

theorem evalExpr_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_eq_int_true (cfg := config) (contract := contract) hlhs hrhs h

theorem evalExpr_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) :=
  Reasoning.Theory.evalExpr_eq_int_false (cfg := config) (contract := contract) hlhs hrhs h

theorem evalExpr_ne_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_ne_int_true (cfg := config) (contract := contract) hlhs hrhs h

theorem evalExpr_ne_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool false) :=
  Reasoning.Theory.evalExpr_ne_int_false (cfg := config) (contract := contract) hlhs hrhs h

theorem evalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) :=
  Reasoning.Theory.evalExpr_or_true_left (cfg := config) (contract := contract) hlhs

theorem evalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) :=
  Reasoning.Theory.evalExpr_or_false_right (cfg := config) (contract := contract) hlhs hrhs

theorem evalExpr_ite_true {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? config { contract := contract, locals := locals } evm cond =
      .ok (.bool true))
    (hthen : evalExpr? config { contract := contract, locals := locals } evm thenExpr =
      .ok value) :
    evalExpr? config { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value :=
  Reasoning.Theory.evalExpr_ite_true (cfg := config) (contract := contract) hcond hthen

theorem evalExpr_ite_false {evm : EVM.State} {locals : Store}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? config { contract := contract, locals := locals } evm cond =
      .ok (.bool false))
    (helse : evalExpr? config { contract := contract, locals := locals } evm elseExpr =
      .ok value) :
    evalExpr? config { contract := contract, locals := locals } evm (.ite cond thenExpr elseExpr) =
      .ok value :=
  Reasoning.Theory.evalExpr_ite_false (cfg := config) (contract := contract) hcond helse

theorem evalExpr_s256_ok {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? config { contract := contract, locals := locals } evm e = .ok (.int i))
    (hlo : -((2 : Int) ^ 255) ≤ i) (hhi : i < (2 : Int) ^ 255) :
    evalExpr? config { contract := contract, locals := locals } evm (s256 e) =
      .ok (.int i) :=
  Reasoning.Theory.evalExpr_s256_ok (cfg := config) (contract := contract) he hlo hhi

theorem evalExpr_s256_revert {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
    (he : evalExpr? config { contract := contract, locals := locals } evm e = .ok (.int i))
    (hbad : i < -((2 : Int) ^ 255) ∨ i ≥ (2 : Int) ^ 255) :
    evalExpr? config { contract := contract, locals := locals } evm (s256 e) = .revert :=
  Reasoning.Theory.evalExpr_s256_revert (cfg := config) (contract := contract) he hbad

end Benchmarks.Dss.Jug
