import Benchmarks.Dss.LinearDecrease.Tau

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.LinearDecrease

/-! ## `price(uint256,uint256)` -/

abbrev priceTop (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev priceDur (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev priceLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "top" (.int (Int.ofNat (priceTop I).toNat))).insert
    "dur" (.int (Int.ofNat (priceDur I).toNat))

abbrev priceUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev priceUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (priceUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev priceUintBinaryLocalsZAssigned (x y old new : UInt256) : Store :=
  (priceUintBinaryLocalsZ x y old).insert "z" (.int (Int.ofNat new.toNat))

def priceTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  tauWord σ I

abbrev stairstepRay : UInt256 :=
  ⟨1000000000000000000000000000⟩

def priceLeft (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (priceTauWord σ I) (priceDur I)

def priceScaled (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  priceLeft σ I * stairstepRay

def priceRatio (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (priceScaled σ I) (priceTauWord σ I)

def priceOut (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (priceRatio σ I * priceTop I) stairstepRay

abbrev priceLocalsLeft (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (priceLocals I).insert "left" (.int (Int.ofNat (priceLeft σ I).toNat))

abbrev priceLocalsScaled (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (priceLocalsLeft σ I).insert "scaled" (.int (Int.ofNat (priceScaled σ I).toNat))

abbrev priceLocalsRatio (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (priceLocalsScaled σ I).insert "ratio" (.int (Int.ofNat (priceRatio σ I).toNat))

abbrev priceLocalsOut (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (priceLocalsRatio σ I).insert "out" (.int (Int.ofNat (priceOut σ I).toNat))

theorem stairstepRay_toNat : stairstepRay.toNat = 1000000000000000000000000000 := by
  change (UInt256.ofNat 1000000000000000000000000000).toNat =
    1000000000000000000000000000
  exact ulit_toNat' _ (by native_decide)

theorem RAY_eq_stairstepRay_toNat : RAY = Int.ofNat stairstepRay.toNat := by
  simp [RAY, stairstepRay_toNat]

theorem stairstepUInt256Zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := by
  native_decide

-- GENERALIZES Benchmarks.Dss.Jug.u256_mul_div_overflow_ne.
theorem price_u256_mul_div_overflow_ne (x y : UInt256)
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
  have hle0 := Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem stairstepRay_mul_div_cancel (y : UInt256)
    (hfit : stairstepRay.toNat * y.toNat < UInt256.size) :
    UInt256.div (stairstepRay * y) stairstepRay = y := by
  apply u256_inj
  rw [udiv_toNat]
  have hprod : (stairstepRay * y).toNat = stairstepRay.toNat * y.toNat := by
    rw [umul_toNat stairstepRay y hfit]
  have hRayPos : 0 < stairstepRay.toNat := by
    rw [stairstepRay_toNat]
    norm_num
  rw [hprod]
  exact Nat.mul_div_right y.toNat hRayPos

theorem stairstepRay_mul_div_overflow_ne (y : UInt256)
    (hover : UInt256.size ≤ stairstepRay.toNat * y.toNat) :
    UInt256.div (stairstepRay * y) stairstepRay ≠ y :=
  price_u256_mul_div_overflow_ne y stairstepRay (by simpa [Nat.mul_comm] using hover)

theorem uint256_mul_zero (x : UInt256) :
    x * (⟨0⟩ : UInt256) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_op_toNat]
  rfl

theorem uint256_zero_mul (x : UInt256) :
    (⟨0⟩ : UInt256) * x = ⟨0⟩ := by
  rw [show (⟨0⟩ : UInt256) * x = x * (⟨0⟩ : UInt256) by
    exact u256_mul_comm (⟨0⟩ : UInt256) x]
  exact uint256_mul_zero x

theorem uint256_div_zero_num (x : UInt256) :
    UInt256.div (⟨0⟩ : UInt256) x = ⟨0⟩ := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.zero_div x.toNat

theorem priceLocals_get_top (I : ExecutionEnv) :
    (priceLocals I).get? "top" = some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocals, store_get_ne _ _ (by decide), store_get_self]

theorem priceLocals_get_dur (I : ExecutionEnv) :
    (priceLocals I).get? "dur" = some (.int (Int.ofNat (priceDur I).toNat)) := by
  rw [priceLocals, store_get_self]

theorem priceLocals_get_tau_none (I : ExecutionEnv) :
    (priceLocals I).get? "tau" = none := by
  rw [priceLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem priceUintBinaryLocals_get_x (x y : UInt256) :
    (priceUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [priceUintBinaryLocals, store_get_self]

theorem priceUintBinaryLocals_get_y (x y : UInt256) :
    (priceUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [priceUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem priceUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (priceUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [priceUintBinaryLocalsZ, store_get_ne _ _ (by decide),
    priceUintBinaryLocals_get_x]

theorem priceUintBinaryLocalsZ_get_y (x y z : UInt256) :
    (priceUintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [priceUintBinaryLocalsZ, store_get_ne _ _ (by decide),
    priceUintBinaryLocals_get_y]

theorem priceUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (priceUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [priceUintBinaryLocalsZ, store_get_self]

theorem priceUintBinaryLocalsZAssigned_get_z (x y old new : UInt256) :
    (priceUintBinaryLocalsZAssigned x y old new).get? "z" =
      some (.int (Int.ofNat new.toNat)) := by
  rw [priceUintBinaryLocalsZAssigned, store_get_self]

theorem priceLocalsLeft_get_top (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsLeft σ I).get? "top" = some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocalsLeft, store_get_ne _ _ (by decide), priceLocals_get_top]

theorem priceLocalsLeft_get_dur (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsLeft σ I).get? "dur" = some (.int (Int.ofNat (priceDur I).toNat)) := by
  rw [priceLocalsLeft, store_get_ne _ _ (by decide), priceLocals_get_dur]

theorem priceLocalsLeft_get_left (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsLeft σ I).get? "left" =
      some (.int (Int.ofNat (priceLeft σ I).toNat)) := by
  rw [priceLocalsLeft, store_get_self]

theorem priceLocalsLeft_get_tau_none (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsLeft σ I).get? "tau" = none := by
  rw [priceLocalsLeft, store_get_ne _ _ (by decide), priceLocals_get_tau_none]

theorem priceLocalsScaled_get_top (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsScaled σ I).get? "top" =
      some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocalsScaled, store_get_ne _ _ (by decide), priceLocalsLeft_get_top]

theorem priceLocalsScaled_get_scaled (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsScaled σ I).get? "scaled" =
      some (.int (Int.ofNat (priceScaled σ I).toNat)) := by
  rw [priceLocalsScaled, store_get_self]

theorem priceLocalsScaled_get_tau_none (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsScaled σ I).get? "tau" = none := by
  rw [priceLocalsScaled, store_get_ne _ _ (by decide), priceLocalsLeft_get_tau_none]

theorem priceLocalsRatio_get_top (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsRatio σ I).get? "top" =
      some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocalsRatio, store_get_ne _ _ (by decide), priceLocalsScaled_get_top]

theorem priceLocalsRatio_get_ratio (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsRatio σ I).get? "ratio" =
      some (.int (Int.ofNat (priceRatio σ I).toNat)) := by
  rw [priceLocalsRatio, store_get_self]

theorem priceLocalsRatio_get_tau_none (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsRatio σ I).get? "tau" = none := by
  rw [priceLocalsRatio, store_get_ne _ _ (by decide), priceLocalsScaled_get_tau_none]

theorem priceLocalsOut_get_out (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsOut σ I).get? "out" =
      some (.int (Int.ofNat (priceOut σ I).toNat)) := by
  rw [priceLocalsOut, store_get_self]

theorem evalExpr_priceDur {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := priceLocals I } evm (.var "dur") =
      .ok (.int (Int.ofNat (priceDur I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((priceLocals I).get? "dur") =
    .ok (.int (Int.ofNat (priceDur I).toNat))
  rw [priceLocals_get_dur]
  rfl

theorem evalExpr_priceTau_word {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage tauRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := tauRef)
    (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨1⟩)
    (hbase := hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by exact stairstepStorageLocLoad_uint256 evm ⟨1⟩)]

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

theorem evalExpr_price_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_price_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
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
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_price_mul256_ok {evm : EVM.State} {locals : Store}
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

theorem evalExpr_price_mul256_revert {evm : EVM.State} {locals : Store}
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

theorem evalExpr_price_div_uint256_ok {evm : EVM.State} {locals : Store}
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

theorem evalExpr_price_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_price_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_price_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_price_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExprs_priceMulArgs {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} :
    evalExprs? config { contract := contract, locals := priceLocalsLeft σ I } evm
      [.var "left", .intLit RAY] =
        .ok [.int (Int.ofNat (priceLeft σ I).toNat),
          .int (Int.ofNat stairstepRay.toNat)] := by
  have hleft :
      evalExpr? config { contract := contract, locals := priceLocalsLeft σ I } evm
        (.var "left") = .ok (.int (Int.ofNat (priceLeft σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsLeft_get_left σ I)
  have hRay :
      evalExpr? config { contract := contract, locals := priceLocalsLeft σ I } evm
        (.intLit RAY) = .ok (.int (Int.ofNat stairstepRay.toNat)) := by
    simp [evalExpr?, pure, RAY_eq_stairstepRay_toNat]
  simp [evalExprs?, hleft, hRay, EvalResult.bind, bind, pure]

theorem evalExprs_priceRmulArgs {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} :
    evalExprs? config { contract := contract, locals := priceLocalsRatio σ I } evm
      [.var "top", .var "ratio"] =
        .ok [.int (Int.ofNat (priceTop I).toNat),
          .int (Int.ofNat (priceRatio σ I).toNat)] := by
  have htop :
      evalExpr? config { contract := contract, locals := priceLocalsRatio σ I } evm
        (.var "top") = .ok (.int (Int.ofNat (priceTop I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsRatio_get_top σ I)
  have hratio :
      evalExpr? config { contract := contract, locals := priceLocalsRatio σ I } evm
        (.var "ratio") = .ok (.int (Int.ofNat (priceRatio σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsRatio_get_ratio σ I)
  simp [evalExprs?, htop, hratio, EvalResult.bind, bind, pure]

theorem stairstepExecMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := priceUintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := priceUintBinaryLocalsZ x y prod }
        evm (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := priceUintBinaryLocals x y
  let localsZ := priceUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (priceUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (priceUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_price_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (priceUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (priceUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (priceUintBinaryLocalsZ_get_z x y prod)
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
        apply evalExpr_price_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact evalExpr_price_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_price_eq_int_false hyZ hZeroLit
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
        have h := evalExpr_price_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact evalExpr_price_eq_int_true hDivY hxZ rfl
      exact evalExpr_price_or_false_right hyEqZero hRight
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, checkedMulUintInto, locals, localsZ]
    using ExecFuncBody.execBlockRet hblock

theorem stairstepExecMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := priceUintBinaryLocals x y } evm
      mulFunction.body .reverted := by
  let locals := priceUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (priceUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (priceUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .revert :=
    evalExpr_price_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [mulFunction, checkedMulUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem stairstepExecRmulFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size)
    (hq : q = UInt256.div prod stairstepRay) :
    ExecFuncBody config { contract := contract, locals := priceUintBinaryLocals x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := priceUintBinaryLocalsZAssigned x y prod q }
        evm (some [.int (Int.ofNat q.toNat)])) := by
  let locals := priceUintBinaryLocals x y
  let localsZ := priceUintBinaryLocalsZ x y prod
  let localsQ := priceUintBinaryLocalsZAssigned x y prod q
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (priceUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (priceUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_price_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (priceUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (priceUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (priceUintBinaryLocalsZ_get_z x y prod)
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
        apply evalExpr_price_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact evalExpr_price_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_price_eq_int_false hyZ hZeroLit
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
        have h := evalExpr_price_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact evalExpr_price_eq_int_true hDivY hxZ rfl
      exact evalExpr_price_or_false_right hyEqZero hRight
  have hRayLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit RAY) =
        .ok (.int (Int.ofNat stairstepRay.toNat)) := by
    simp [evalExpr?, pure, RAY_eq_stairstepRay_toNat]
  have hDivRay :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "z") (.intLit RAY)) = .ok (.int (Int.ofNat q.toNat)) :=
    evalExpr_price_div_uint256_ok hzZ hRayLit (by native_decide) hq
  have hAssign :
      assignStorageRef? config { contract := contract, locals := localsZ } evm .localVar
          { base := "z" } (.int (Int.ofNat q.toNat)) =
        .ok ({ contract := contract, locals := localsQ }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsQ,
      priceUintBinaryLocalsZAssigned, localsZ, priceUintBinaryLocalsZ]
  have hzQ :
      evalExpr? config { contract := contract, locals := localsQ } evm (.var "z") =
        .ok (.int (Int.ofNat q.toNat)) := by
    simpa [localsQ] using evalExpr_price_varUInt256 (evm := evm)
      (locals := localsQ) (name := "z") (value := q)
      (priceUintBinaryLocalsZAssigned_get_z x y prod q)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit RAY)),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsQ } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivRay hAssign) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzQ))
  simpa [rmulFunction, checkedMulUintInto, locals, localsZ, localsQ]
    using ExecFuncBody.execBlockRet hblock

theorem stairstepExecRmulFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := priceUintBinaryLocals x y } evm
      rmulFunction.body .reverted := by
  let locals := priceUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (priceUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_price_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (priceUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .revert :=
    evalExpr_price_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit RAY)),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [rmulFunction, checkedMulUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem uint256_lt_eq_zero_toNat_ge {a b : UInt256}
    (h : UInt256.lt a b = ⟨0⟩) :
    b.toNat ≤ a.toNat := by
  by_contra hge
  have hlt : a.toNat < b.toNat := by omega
  have hone : UInt256.lt a b = ⟨1⟩ := ult_one hlt
  have hbad : (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa [h] using hone
  exact (by native_decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hbad

-- LIBRARY CANDIDATE: legacy solc05 decoding for `(uint256,uint256)`.
theorem stairstepDecodeABIValues_uint256_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  have hread32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hmod0 :
      (Int.ofNat (ABI.bytesToWord (bytes.take 32)).val % Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord (bytes.take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord (bytes.take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using (ABI.bytesToWord (bytes.take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  have hmod32 :
      (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).val %
          Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord ((bytes.drop 32).take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord ((bytes.drop 32).take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using
          (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  simp [decodeABIValues?, abiUInt256, isDynamicABIType, staticABIEncodedSize?,
    decodeABIValue?, readWord?, readBytes?, decodeABIWord?, hlen0, hread32]
  exact ⟨hmod0, hmod32⟩

-- LIBRARY CANDIDATE: legacy solc05 short-calldata rejection for `(uint256,uint256)`.
theorem stairstepDecodeABIValues_uint256_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiUInt256, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readWord?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      omega
    simp [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, htake0, hnot]

theorem stairstepDecodeCalldata_legacyUInt256_uint256_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [stairstepDecodeABIValues_uint256_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem stairstepDecodeCalldata_legacyUInt256_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [stairstepDecodeABIValues_uint256_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem stairstepDecode_price_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (priceTransition.params.map Param.name)
      (transitionSignature priceTransition).paramTypes I.calldata =
        some (priceLocals I) := by
  simpa [config, priceTransition, uint256, uint256Int, priceLocals, priceTop, priceDur,
    abiUInt256] using
    (stairstepDecodeCalldata_legacyUInt256_uint256_ok (cd := I.calldata) (x := "top")
      (y := "dur") hsz68)

theorem stairstepDecode_price_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (priceTransition.params.map Param.name)
      (transitionSignature priceTransition).paramTypes I.calldata = none := by
  simpa [config, priceTransition, uint256, uint256Int, abiUInt256] using
    (stairstepDecodeCalldata_legacyUInt256_uint256_none_short (cd := I.calldata)
      (x := "top") (y := "dur") hsz4 hshort)

theorem stairstepReachPriceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (stairstepSelBytes 2)) :
    ∃ k C, RD linearDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepPriceEntryPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : stairstepSelWord I = ⟨0x487a2395⟩ :=
    stairstepSelWord_eq_of_beq I hsz 0x48 0x7a 0x23 0x95 ⟨0x487a2395⟩
      (by native_decide) (by simpa [stairstepSelBytes] using hsel)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc 1))
        (stairstepSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact stairstepReachBody 1 (by omega) stairstepPriceEntryPc hcode hwv hsz hsize
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.stairstepPriceDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD linearDecreaseBytecode I g s0 ⟨162⟩
      (de :: ⟨4⟩ :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨552⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd552 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨552⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [priceDur, priceTop, calldataWord] using rd552⟩

theorem stairstepPriceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD linearDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepPriceEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD linearDecreaseBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨552⟩
        [priceDur I, priceTop I, ⟨175⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := linearDecreaseBytecode) (sel := sel)
    (entry := stairstepPriceEntryPc) (ret := ⟨175⟩) (decoded := ⟨162⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  exact RD.stairstepPriceDecodeToRoutine hdecoded

theorem stairstepPriceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD linearDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepPriceEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := linearDecreaseBytecode) (sel := sel)
    (entry := stairstepPriceEntryPc) (ret := ⟨175⟩) (decoded := ⟨162⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem stairstepPriceSourceZeroReturns {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) = ⟨0⟩) :
    let locals := priceLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals priceTransition.body
      (.returned { contract := contract, locals := locals } evm0 (some [.int 0])) := by
  intro locals evm0
  have hdur :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "dur") =
        .ok (.int (Int.ofNat (priceDur I).toNat)) := by
    simpa [locals] using evalExpr_priceDur (evm := evm0) (I := I)
  have htau :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage tauRef) =
        .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [locals, evm0, priceTauWord, tauWord, stairstepSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      (evalExpr_priceTau_word (evm := evm0) (locals := locals)
        (by simpa [locals] using priceLocals_get_tau_none I))
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ge (.var "dur") (.storage tauRef)) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hdur htau (uint256_lt_eq_zero_toNat_ge hlt)
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm0 (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.return [.intLit 0]]
        (.returned { contract := contract, locals := locals } evm0 (some [.int 0])) :=
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzero))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 priceTransition.body
        (.returned { contract := contract, locals := locals } evm0 (some [.int 0])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRet hblock

theorem stairstepPriceSourceReturns {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htauLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceTauWord σ I)
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) ≠ ⟨0⟩)
    (hfitMul : (priceLeft σ I).toNat * stairstepRay.toNat < UInt256.size)
    (hfitRmul : (priceRatio σ I).toNat * (priceTop I).toNat < UInt256.size) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body
      (.returned { contract := contract, locals := priceLocalsOut σ I }
        evm (some [.int (Int.ofNat (priceOut σ I).toNat)])) := by
  have hltNat : (priceDur I).toNat < (priceTauWord σ I).toNat :=
    ult_ne_zero_toNat_lt hlt
  have htauNe : priceTauWord σ I ≠ ⟨0⟩ := by
    intro hzero
    have hzeroNat : (priceTauWord σ I).toNat = 0 := by
      rw [hzero]
      exact stairstepUInt256Zero_toNat
    omega
  have hdur :
      evalExpr? config { contract := contract, locals := priceLocals I } evm (.var "dur") =
        .ok (.int (Int.ofNat (priceDur I).toNat)) :=
    evalExpr_priceDur (evm := evm) (I := I)
  have htau :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.storage tauRef) = .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [htauLoad] using
      (evalExpr_priceTau_word (evm := evm) (locals := priceLocals I)
        (priceLocals_get_tau_none I))
  have hcond :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .ge (.var "dur") (.storage tauRef)) = .ok (.bool false) :=
    evalExpr_ge_uint256_false hdur htau hltNat
  have hleftEval :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (sub256 (.storage tauRef) (.var "dur")) =
          .ok (.int (Int.ofNat (priceLeft σ I).toNat)) :=
    evalExpr_price_sub256_ok htau hdur rfl (le_of_lt hltNat)
  have hleftStmt :
      ExecStmt config { contract := contract, locals := priceLocals I } evm
        (.letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")))
        (.ok { contract := contract, locals := priceLocalsLeft σ I } evm) := by
    simpa [priceLocalsLeft] using ExecStmt.letDecl hleftEval
  have hmulArgs := evalExprs_priceMulArgs (evm := evm) (σ := σ) (I := I)
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat (priceLeft σ I).toNat),
            .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintBinaryLocals (priceLeft σ I) stairstepRay) := by
    simp [mulFunction, priceUintBinaryLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := priceLocalsLeft σ I } evm
        (.internalCall "mul" [.var "left", .intLit RAY] "scaled")
        (.ok { contract := contract, locals := priceLocalsScaled σ I } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsLeft σ I))
      (evm := evm) (name := "mul") (retVar := "scaled")
      (args := [.var "left", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceLeft σ I).toNat),
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := mulFunction)
      (locals := priceUintBinaryLocals (priceLeft σ I) stairstepRay)
      hmulArgs hlookupMul hbindMul
      (stairstepExecMulFunctionReturn evm (x := priceLeft σ I) (y := stairstepRay)
        (prod := priceScaled σ I) rfl hfitMul)
    simpa [resumeAfterInternalCall, priceLocalsScaled] using h
  have hscaled :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.var "scaled") = .ok (.int (Int.ofNat (priceScaled σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsScaled_get_scaled σ I)
  have htauScaled :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.storage tauRef) = .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [htauLoad] using
      (evalExpr_priceTau_word (evm := evm) (locals := priceLocalsScaled σ I)
        (priceLocalsScaled_get_tau_none σ I))
  have hratioEval :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.binary .div (.var "scaled") (.storage tauRef)) =
          .ok (.int (Int.ofNat (priceRatio σ I).toNat)) :=
    evalExpr_price_div_uint256_ok hscaled htauScaled htauNe rfl
  have hratioStmt :
      ExecStmt config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)))
        (.ok { contract := contract, locals := priceLocalsRatio σ I } evm) := by
    simpa [priceLocalsRatio] using ExecStmt.letDecl hratioEval
  have hrmulArgs := evalExprs_priceRmulArgs (evm := evm) (σ := σ) (I := I)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat),
            .int (Int.ofNat (priceRatio σ I).toNat)] =
        some (priceUintBinaryLocals (priceTop I) (priceRatio σ I)) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hfitRmulLocal : (priceTop I).toNat * (priceRatio σ I).toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hfitRmul
  have hq :
      priceOut σ I = UInt256.div (priceTop I * priceRatio σ I) stairstepRay := by
    unfold priceOut
    have hcomm : priceRatio σ I * priceTop I = priceTop I * priceRatio σ I := by
      simpa [HMul.hMul, Mul.mul] using u256_mul_comm (priceRatio σ I) (priceTop I)
    rw [hcomm]
  have hrmulStmt :
      ExecStmt config { contract := contract, locals := priceLocalsRatio σ I } evm
        (.internalCall "rmul" [.var "top", .var "ratio"] "out")
        (.ok { contract := contract, locals := priceLocalsOut σ I } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsRatio σ I))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "ratio"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat),
        .int (Int.ofNat (priceRatio σ I).toNat)])
      (callee := rmulFunction)
      (locals := priceUintBinaryLocals (priceTop I) (priceRatio σ I))
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionReturn evm (x := priceTop I) (y := priceRatio σ I)
        (prod := priceTop I * priceRatio σ I) (q := priceOut σ I)
        rfl hfitRmulLocal hq)
    simpa [resumeAfterInternalCall, priceLocalsOut] using h
  have hout :
      evalExpr? config { contract := contract, locals := priceLocalsOut σ I } evm
        (.var "out") = .ok (.int (Int.ofNat (priceOut σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsOut_get_out σ I)
  have helse :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")),
          .internalCall "mul" [.var "left", .intLit RAY] "scaled",
          .letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)),
          .internalCall "rmul" [.var "top", .var "ratio"] "out",
          .return [.var "out"] ]
        (.returned { contract := contract, locals := priceLocalsOut σ I } evm
          (some [.int (Int.ofNat (priceOut σ I).toNat)])) := by
    refine ExecBlock.consNormal hleftStmt ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal hratioStmt ?_
    refine ExecBlock.consNormal hrmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hout))
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        priceTransition.body
        (.returned { contract := contract, locals := priceLocalsOut σ I } evm
          (some [.int (Int.ofNat (priceOut σ I).toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, priceTransition, nonpayable] using ExecFuncBody.execBlockRet hblock

theorem stairstepPriceSourceMulRayOverflowReverts {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htauLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceTauWord σ I)
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (priceLeft σ I).toNat * stairstepRay.toNat) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hltNat : (priceDur I).toNat < (priceTauWord σ I).toNat :=
    ult_ne_zero_toNat_lt hlt
  have hdur :
      evalExpr? config { contract := contract, locals := priceLocals I } evm (.var "dur") =
        .ok (.int (Int.ofNat (priceDur I).toNat)) :=
    evalExpr_priceDur (evm := evm) (I := I)
  have htau :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.storage tauRef) = .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [htauLoad] using
      (evalExpr_priceTau_word (evm := evm) (locals := priceLocals I)
        (priceLocals_get_tau_none I))
  have hcond :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .ge (.var "dur") (.storage tauRef)) = .ok (.bool false) :=
    evalExpr_ge_uint256_false hdur htau hltNat
  have hleftEval :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (sub256 (.storage tauRef) (.var "dur")) =
          .ok (.int (Int.ofNat (priceLeft σ I).toNat)) :=
    evalExpr_price_sub256_ok htau hdur rfl (le_of_lt hltNat)
  have hleftStmt :
      ExecStmt config { contract := contract, locals := priceLocals I } evm
        (.letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")))
        (.ok { contract := contract, locals := priceLocalsLeft σ I } evm) := by
    simpa [priceLocalsLeft] using ExecStmt.letDecl hleftEval
  have hmulArgs := evalExprs_priceMulArgs (evm := evm) (σ := σ) (I := I)
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat (priceLeft σ I).toNat),
            .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintBinaryLocals (priceLeft σ I) stairstepRay) := by
    simp [mulFunction, priceUintBinaryLocals, bindParams?]
  have hmulRevert :
      ExecStmt config { contract := contract, locals := priceLocalsLeft σ I } evm
        (.internalCall "mul" [.var "left", .intLit RAY] "scaled") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsLeft σ I))
      (evm := evm) (name := "mul") (retVar := "scaled")
      (args := [.var "left", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceLeft σ I).toNat),
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := mulFunction)
      (locals := priceUintBinaryLocals (priceLeft σ I) stairstepRay)
      hmulArgs hlookupMul hbindMul
      (stairstepExecMulFunctionRevert evm (x := priceLeft σ I) (y := stairstepRay) hover)
  have helse :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")),
          .internalCall "mul" [.var "left", .intLit RAY] "scaled",
          .letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)),
          .internalCall "rmul" [.var "top", .var "ratio"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal hleftStmt ?_
    exact ExecBlock.consRevert hmulRevert
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        priceTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, priceTransition, nonpayable] using ExecFuncBody.execBlockRevert hblock

theorem stairstepPriceSourceRmulOverflowReverts {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htauLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceTauWord σ I)
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) ≠ ⟨0⟩)
    (hfitMul : (priceLeft σ I).toNat * stairstepRay.toNat < UInt256.size)
    (hover : UInt256.size ≤ (priceRatio σ I).toNat * (priceTop I).toNat) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hltNat : (priceDur I).toNat < (priceTauWord σ I).toNat :=
    ult_ne_zero_toNat_lt hlt
  have htauNe : priceTauWord σ I ≠ ⟨0⟩ := by
    intro hzero
    have hzeroNat : (priceTauWord σ I).toNat = 0 := by
      rw [hzero]
      exact stairstepUInt256Zero_toNat
    omega
  have hdur :
      evalExpr? config { contract := contract, locals := priceLocals I } evm (.var "dur") =
        .ok (.int (Int.ofNat (priceDur I).toNat)) :=
    evalExpr_priceDur (evm := evm) (I := I)
  have htau :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.storage tauRef) = .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [htauLoad] using
      (evalExpr_priceTau_word (evm := evm) (locals := priceLocals I)
        (priceLocals_get_tau_none I))
  have hcond :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .ge (.var "dur") (.storage tauRef)) = .ok (.bool false) :=
    evalExpr_ge_uint256_false hdur htau hltNat
  have hleftEval :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (sub256 (.storage tauRef) (.var "dur")) =
          .ok (.int (Int.ofNat (priceLeft σ I).toNat)) :=
    evalExpr_price_sub256_ok htau hdur rfl (le_of_lt hltNat)
  have hleftStmt :
      ExecStmt config { contract := contract, locals := priceLocals I } evm
        (.letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")))
        (.ok { contract := contract, locals := priceLocalsLeft σ I } evm) := by
    simpa [priceLocalsLeft] using ExecStmt.letDecl hleftEval
  have hmulArgs := evalExprs_priceMulArgs (evm := evm) (σ := σ) (I := I)
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat (priceLeft σ I).toNat),
            .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintBinaryLocals (priceLeft σ I) stairstepRay) := by
    simp [mulFunction, priceUintBinaryLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := priceLocalsLeft σ I } evm
        (.internalCall "mul" [.var "left", .intLit RAY] "scaled")
        (.ok { contract := contract, locals := priceLocalsScaled σ I } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsLeft σ I))
      (evm := evm) (name := "mul") (retVar := "scaled")
      (args := [.var "left", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceLeft σ I).toNat),
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := mulFunction)
      (locals := priceUintBinaryLocals (priceLeft σ I) stairstepRay)
      hmulArgs hlookupMul hbindMul
      (stairstepExecMulFunctionReturn evm (x := priceLeft σ I) (y := stairstepRay)
        (prod := priceScaled σ I) rfl hfitMul)
    simpa [resumeAfterInternalCall, priceLocalsScaled] using h
  have hscaled :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.var "scaled") = .ok (.int (Int.ofNat (priceScaled σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsScaled_get_scaled σ I)
  have htauScaled :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.storage tauRef) = .ok (.int (Int.ofNat (priceTauWord σ I).toNat)) := by
    simpa [htauLoad] using
      (evalExpr_priceTau_word (evm := evm) (locals := priceLocalsScaled σ I)
        (priceLocalsScaled_get_tau_none σ I))
  have hratioEval :
      evalExpr? config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.binary .div (.var "scaled") (.storage tauRef)) =
          .ok (.int (Int.ofNat (priceRatio σ I).toNat)) :=
    evalExpr_price_div_uint256_ok hscaled htauScaled htauNe rfl
  have hratioStmt :
      ExecStmt config { contract := contract, locals := priceLocalsScaled σ I } evm
        (.letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)))
        (.ok { contract := contract, locals := priceLocalsRatio σ I } evm) := by
    simpa [priceLocalsRatio] using ExecStmt.letDecl hratioEval
  have hrmulArgs := evalExprs_priceRmulArgs (evm := evm) (σ := σ) (I := I)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat),
            .int (Int.ofNat (priceRatio σ I).toNat)] =
        some (priceUintBinaryLocals (priceTop I) (priceRatio σ I)) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hoverLocal : UInt256.size ≤ (priceTop I).toNat * (priceRatio σ I).toNat := by
    simpa [Nat.mul_comm] using hover
  have hrmulRevert :
      ExecStmt config { contract := contract, locals := priceLocalsRatio σ I } evm
        (.internalCall "rmul" [.var "top", .var "ratio"] "out") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsRatio σ I))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "ratio"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat),
        .int (Int.ofNat (priceRatio σ I).toNat)])
      (callee := rmulFunction)
      (locals := priceUintBinaryLocals (priceTop I) (priceRatio σ I))
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionRevertMul evm (x := priceTop I) (y := priceRatio σ I)
        hoverLocal)
  have helse :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")),
          .internalCall "mul" [.var "left", .intLit RAY] "scaled",
          .letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)),
          .internalCall "rmul" [.var "top", .var "ratio"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal hleftStmt ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal hratioStmt ?_
    exact ExecBlock.consRevert hrmulRevert
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        priceTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, priceTransition, nonpayable] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem stairstepPriceZeroReturn {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) = ⟨0⟩)
    (h : RD linearDecreaseBytecode I g s0 ⟨552⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret linearDecreaseBytecode g s0 (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  have rd557 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k558, C558, rd558raw⟩ := rd557.sload (by native_decide) (by evm_ov)
  have rd558 : RD linearDecreaseBytecode I g s0 ⟨558⟩
      (priceTauWord σ I :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k558 C558 := by
    simpa [priceTauWord, tauWord, stairstepSlotWord] using rd558raw
  have rd620 := evm_run rd558 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw push2 ⟨571⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) hlt (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨620⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd175 := evm_run rd620 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hret := RD.solcReturnWordFromMem
    (pc := ⟨175⟩) (val := (⟨0⟩ : UInt256)) (ret := sel) (R := [])
    (memout := solcScratchReturnMem solcFreePtrMem (⟨0⟩ : UInt256))
    (by simpa using rd175)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcScratchReturnMem_mload64 (⟨0⟩ : UInt256) solcFreePtrMem_size solcFreePtrMem_read64)
    (solcScratchReturnMem_read128 (⟨0⟩ : UInt256) solcFreePtrMem_size)
    (by simp)
  simpa using hret

set_option maxHeartbeats 1000000 in
theorem stairstepPriceToMulRay {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ I) ≠ ⟨0⟩)
    (h : RD linearDecreaseBytecode I g s0 ⟨552⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: priceLeft σ I :: ⟨604⟩ :: priceTauWord σ I :: priceTop I ::
        ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd557 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k558, C558, rd558raw⟩ := rd557.sload (by native_decide) (by evm_ov)
  have rd558 : RD linearDecreaseBytecode I g s0 ⟨558⟩
      (priceTauWord σ I :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k558 C558 := by
    simpa [priceTauWord, tauWord, stairstepSlotWord] using rd558raw
  have rd571 := evm_run rd558 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw push2 ⟨571⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) hlt (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨617⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k579, C579, rd579raw⟩ := rd571.sload (by native_decide) (by evm_ov)
  have rd579 : RD linearDecreaseBytecode I g s0 ⟨579⟩
      (priceTauWord σ I :: priceTop I :: ⟨617⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k579 C579 := by
    simpa [priceTauWord, tauWord, stairstepSlotWord] using rd579raw
  have rd585 := evm_run rd579 with [
    raw push2 ⟨604⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k586, C586, rd586raw⟩ := rd585.sload (by native_decide) (by evm_ov)
  have rd586 : RD linearDecreaseBytecode I g s0 ⟨586⟩
      (priceTauWord σ I :: priceDur I :: ⟨604⟩ :: priceTauWord σ I ::
        priceTop I :: ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k586 C586 := by
    simpa [priceTauWord, tauWord, stairstepSlotWord] using rd586raw
  have rd587 := evm_run rd586 with [
    raw sub (by native_decide) (by evm_ov)]
  have rd600 := rd587.pushConst stairstepRay
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd987pre := evm_run rd600 with [
    raw push2 ⟨987⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [priceLeft, stairstepRay] using
      rd987pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceMulRayReturns {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hfit : (priceLeft σ I).toNat * stairstepRay.toNat < UInt256.size)
    (h : RD linearDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: priceLeft σ I :: ⟨604⟩ :: priceTauWord σ I :: priceTop I ::
        ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨604⟩
      (priceScaled σ I :: priceTauWord σ I :: priceTop I :: ⟨617⟩ :: ⟨0⟩ ::
        priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let prod := priceLeft σ I * stairstepRay
  have rd1014pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1014⟩ (by native_decide) (by evm_ov)]
  have hRayNonzero : UInt256.isZero stairstepRay = ⟨0⟩ := by native_decide
  have rd997 := rd1014pre.jumpiNT (by native_decide) hRayNonzero (by evm_ov)
  have rd1011pre := evm_run rd997 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1011⟩ (by native_decide) (by evm_ov)]
  have rd1011 := rd1011pre.jumpiT (by native_decide)
    (by native_decide : stairstepRay ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have hdivRay : UInt256.div (stairstepRay * priceLeft σ I) stairstepRay =
      priceLeft σ I := by
    simpa [Nat.mul_comm] using stairstepRay_mul_div_cancel (priceLeft σ I) (by
      simpa [Nat.mul_comm] using hfit)
  have hdiv' :
      UInt256.div (UInt256.mul (priceLeft σ I) stairstepRay) stairstepRay =
        priceLeft σ I := by
    rw [u256_mul_comm (priceLeft σ I) stairstepRay]
    simpa [HMul.hMul, Mul.mul] using hdivRay
  have rd1014 := evm_run rd1011 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hdiv', u256_eq_refl] at rd1014
  have rd620pre := evm_run rd1014 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨620⟩ (by native_decide) (by evm_ov)]
  have rd620 := rd620pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd604pre := evm_run rd620 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [prod, priceScaled, hdiv', HMul.hMul, Mul.mul] using
      rd604pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceMulRayOverflowReverts {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hover : UInt256.size ≤ (priceLeft σ I).toNat * stairstepRay.toNat)
    (h : RD linearDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: priceLeft σ I :: ⟨604⟩ :: priceTauWord σ I :: priceTop I ::
        ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g s0 := by
  have rd1014pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1014⟩ (by native_decide) (by evm_ov)]
  have hRayNonzero : UInt256.isZero stairstepRay = ⟨0⟩ := by native_decide
  have rd997 := rd1014pre.jumpiNT (by native_decide) hRayNonzero (by evm_ov)
  have rd1011pre := evm_run rd997 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1011⟩ (by native_decide) (by evm_ov)]
  have rd1011 := rd1011pre.jumpiT (by native_decide)
    (by native_decide : stairstepRay ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have hdivNe :
      UInt256.div (UInt256.mul (priceLeft σ I) stairstepRay) stairstepRay ≠
        priceLeft σ I := by
    have h := stairstepRay_mul_div_overflow_ne (priceLeft σ I) (by
      simpa [Nat.mul_comm] using hover)
    intro hbad
    rw [u256_mul_comm (priceLeft σ I) stairstepRay] at hbad
    exact h (by simpa [HMul.hMul, Mul.mul] using hbad)
  have rd1014 := evm_run rd1011 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq :
      UInt256.eq
          (UInt256.div (UInt256.mul (priceLeft σ I) stairstepRay) stairstepRay)
          (priceLeft σ I) = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  rw [heq] at rd1014
  have rd1019pre := evm_run rd1014 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨620⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rd1019pre
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem stairstepPriceAfterMulToRmul {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (htau : priceTauWord σ I ≠ ⟨0⟩)
    (h : RD linearDecreaseBytecode I g s0 ⟨604⟩
      (priceScaled σ I :: priceTauWord σ I :: priceTop I :: ⟨617⟩ :: ⟨0⟩ ::
        priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨1023⟩
      (priceRatio σ I :: priceTop I :: ⟨617⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd611 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨611⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) htau (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push2 ⟨1023⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [priceRatio] using rd611.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulReturns {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel pow : UInt256}
    (hfit : pow.toNat * (priceTop I).toNat < UInt256.size)
    (h : RD linearDecreaseBytecode I g s0 ⟨1023⟩
      (pow :: priceTop I :: ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I ::
        ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨617⟩
      (UInt256.div (pow * priceTop I) stairstepRay :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1047pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1047⟩ (by native_decide) (by evm_ov)]
  by_cases hpow0 : pow = ⟨0⟩
  · have hpowZero : UInt256.isZero pow ≠ ⟨0⟩ := by
      rw [hpow0]
      decide
    have rd1047 := rd1047pre.jumpiT (by native_decide) hpowZero
      (by jump_dest) (by evm_ov)
    have rd1056pre := evm_run rd1047 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨1056⟩ (by native_decide) (by evm_ov)]
    have rd1056 := rd1056pre.jumpiT (by native_decide) hpowZero
      (by jump_dest) (by evm_ov)
    have rd1057 := evm_run rd1056 with [
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd1070 := rd1057.pushConst stairstepRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd1076pre := evm_run rd1070 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨_, _, by simpa [hpow0] using
      rd1076pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  · have hpowNonzero : UInt256.isZero pow = ⟨0⟩ := isZero_eq_zero_of_ne hpow0
    have rd1034 := rd1047pre.jumpiNT (by native_decide) hpowNonzero (by evm_ov)
    have rd1044pre := evm_run rd1034 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨1044⟩ (by native_decide) (by evm_ov)]
    have rd1044 := rd1044pre.jumpiT (by native_decide) hpow0 (by jump_dest) (by evm_ov)
    have hpowNatNe : pow.toNat ≠ 0 := by
      intro hzero
      exact hpow0 (uint256_toNat_eq_zero hzero)
    have hdiv : UInt256.div (pow * priceTop I) pow = priceTop I := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (pow * priceTop I).toNat = pow.toNat * (priceTop I).toNat := by
        rw [umul_toNat pow (priceTop I) hfit]
      rw [hprod]
      exact Nat.mul_div_right (priceTop I).toNat (Nat.pos_of_ne_zero hpowNatNe)
    have hdiv' : UInt256.div (UInt256.mul pow (priceTop I)) pow = priceTop I := by
      simpa [HMul.hMul, Mul.mul] using hdiv
    have rd1047 := evm_run rd1044 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov)]
    rw [hdiv', u256_eq_refl] at rd1047
    have rd1056pre := evm_run rd1047 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨1056⟩ (by native_decide) (by evm_ov)]
    have rd1056 := rd1056pre.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rd1057 := evm_run rd1056 with [
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd1070 := rd1057.pushConst stairstepRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd1076pre := evm_run rd1070 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨_, _, by simpa [hdiv, hdiv'] using
      rd1076pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulOverflowReverts {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel pow : UInt256}
    (hover : UInt256.size ≤ pow.toNat * (priceTop I).toNat)
    (h : RD linearDecreaseBytecode I g s0 ⟨1023⟩
      (pow :: priceTop I :: ⟨617⟩ :: ⟨0⟩ :: priceDur I :: priceTop I ::
        ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g s0 := by
  have hpowNe : pow ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : pow.toNat * (priceTop I).toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (pow * priceTop I) pow ≠ priceTop I :=
    price_u256_mul_div_overflow_ne (priceTop I) pow (by simpa [Nat.mul_comm] using hover)
  have hdivNe' : UInt256.div (UInt256.mul pow (priceTop I)) pow ≠ priceTop I := by
    simpa [HMul.hMul, Mul.mul] using hdivNe
  have rd1047pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1047⟩ (by native_decide) (by evm_ov)]
  have hpowNonzero : UInt256.isZero pow = ⟨0⟩ := isZero_eq_zero_of_ne hpowNe
  have rd1034 := rd1047pre.jumpiNT (by native_decide) hpowNonzero (by evm_ov)
  have rd1044pre := evm_run rd1034 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1044⟩ (by native_decide) (by evm_ov)]
  have rd1044 := rd1044pre.jumpiT (by native_decide) hpowNe (by jump_dest) (by evm_ov)
  have rd1047 := evm_run rd1044 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq :
      UInt256.eq (UInt256.div (UInt256.mul pow (priceTop I)) pow) (priceTop I) = ⟨0⟩ :=
    u256_eq_of_ne hdivNe'
  rw [heq] at rd1047
  have rd1052pre := evm_run rd1047 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨1056⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rd1052pre
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem stairstepPriceFinishReturn {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel out : UInt256}
    (h : RD linearDecreaseBytecode I g s0 ⟨617⟩
      (out :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret linearDecreaseBytecode g s0 (cA, σ) (UInt256.toByteArray out) := by
  have rd175 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact RD.solcReturnWordFromMem
    (code := linearDecreaseBytecode) (g := g) (s0 := s0)
    (ee := I) (pc := ⟨175⟩) (val := out) (ret := sel) (R := [])
    (memout := solcReturnMem out)
    rd175
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 out)
    (solcReturnMem_read128 out)
    (by simp)

theorem stairstepPriceBodyCoreZero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some priceTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (priceTransition.params.map Param.name)
        (transitionSignature priceTransition).paramTypes I.calldata = some (priceLocals I))
    (hreach : ∃ k C, RD linearDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨552⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlt : UInt256.lt (priceDur I) (priceTauWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd552⟩ := hreach
  have htauEq : priceTauWord σ_evm I = priceTauWord σ_solm I := by
    unfold priceTauWord tauWord stairstepSlotWord
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hltSolm : UInt256.lt (priceDur I) (priceTauWord σ_solm I) = ⟨0⟩ := by
    rw [← htauEq]
    exact hlt
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (priceLocals I) priceTransition.body
        (.returned { contract := contract, locals := priceLocals I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int 0])) := by
    simpa using
      stairstepPriceSourceZeroReturns (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hltSolm
  have hret := stairstepPriceZeroReturn (σ := σ_evm) hlt rd552
  have hval :
      some [Value.int 0] =
        some [Value.int (Int.ofNat ((⟨0⟩ : UInt256).toNat))] := by
    native_decide
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256))
        (some [(.int (Int.ofNat ((⟨0⟩ : UInt256).toNat)))])
        priceTransition.returnType := by
    rw [show priceTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem stairstepPriceBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = linearDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some priceTransition)
    (hreach : ∃ k C, RD linearDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) stairstepPriceEntryPc
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (stairstepPriceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (stairstepDecode_price_none_short hsz4 hshort)

set_option maxHeartbeats 2000000 in
theorem stairstepPriceBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = linearDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (stairstepSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (stairstepSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some priceTransition :=
    stairstepDispatchPrice hsel
  have hreach := stairstepReachPriceBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hdecode := stairstepDecode_price_ok (I := I) hsz68
    have hloadSolm :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩ =
          priceTauWord σ_solm I := by
      simp [evmSolm, priceTauWord, tauWord, stairstepSlotWord, initState,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord]
    have htauEq : priceTauWord σ_evm I = priceTauWord σ_solm I := by
      unfold priceTauWord tauWord stairstepSlotWord
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hleftEq : priceLeft σ_evm I = priceLeft σ_solm I := by
      unfold priceLeft
      rw [htauEq]
    have hscaledEq : priceScaled σ_evm I = priceScaled σ_solm I := by
      unfold priceScaled
      rw [hleftEq]
    have hratioEq : priceRatio σ_evm I = priceRatio σ_solm I := by
      unfold priceRatio
      rw [hscaledEq, htauEq]
    have houtEq : priceOut σ_evm I = priceOut σ_solm I := by
      unfold priceOut
      rw [hratioEq]
    obtain ⟨_, _, rd552⟩ :=
      stairstepPriceX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    by_cases hltZero : UInt256.lt (priceDur I) (priceTauWord σ_evm I) = ⟨0⟩
    · exact stairstepPriceBodyCoreZero hcode hwv hdispatch hdecode ⟨_, _, rd552⟩
        hAccounts hltZero
    · have hltSolm : UInt256.lt (priceDur I) (priceTauWord σ_solm I) ≠ ⟨0⟩ := by
        intro hbad
        exact hltZero (by
          rw [← htauEq] at hbad
          exact hbad)
      have hltNat : (priceDur I).toNat < (priceTauWord σ_evm I).toNat :=
        ult_ne_zero_toNat_lt hltZero
      have htauEvmNe : priceTauWord σ_evm I ≠ ⟨0⟩ := by
        intro hzero
        have hzeroNat : (priceTauWord σ_evm I).toNat = 0 := by
          rw [hzero]
          exact stairstepUInt256Zero_toNat
        omega
      obtain ⟨_, _, rd987⟩ := stairstepPriceToMulRay (σ := σ_evm) hltZero rd552
      by_cases hfitMul : (priceLeft σ_evm I).toNat * stairstepRay.toNat < UInt256.size
      · obtain ⟨_, _, rd604⟩ := stairstepPriceMulRayReturns (σ := σ_evm) hfitMul rd987
        obtain ⟨_, _, rd1023⟩ :=
          stairstepPriceAfterMulToRmul (σ := σ_evm) htauEvmNe rd604
        have hfitMulSolm :
            (priceLeft σ_solm I).toNat * stairstepRay.toNat < UInt256.size := by
          simpa [← hleftEq] using hfitMul
        by_cases hfitRmul :
            (priceRatio σ_evm I).toNat * (priceTop I).toNat < UInt256.size
        · have hfitRmulSolm :
              (priceRatio σ_solm I).toNat * (priceTop I).toNat < UInt256.size := by
            simpa [← hratioEq] using hfitRmul
          have hbody :
              ExecTransitionBody config contract evmSolm (priceLocals I)
                priceTransition.body
                (.returned { contract := contract, locals := priceLocalsOut σ_solm I }
                  evmSolm (some [.int (Int.ofNat (priceOut σ_solm I).toNat)])) :=
            stairstepPriceSourceReturns (evm := evmSolm) (σ := σ_solm) (I := I)
              (by simp only [evmSolm, initState]; exact hwv)
              hloadSolm hltSolm hfitMulSolm hfitRmulSolm
          obtain ⟨_, _, rd617⟩ :=
            stairstepPriceRmulReturns (σ := σ_evm) (pow := priceRatio σ_evm I)
              hfitRmul rd1023
          have hret :
              RDret linearDecreaseBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
                (UInt256.toByteArray (priceOut σ_evm I)) := by
            exact stairstepPriceFinishReturn (out := priceOut σ_evm I)
              (by simpa [priceOut] using rd617)
          have hval :
              some [Value.int (Int.ofNat (priceOut σ_solm I).toNat)] =
                some [Value.int (Int.ofNat (priceOut σ_evm I).toNat)] := by
            rw [← houtEq]
          have henc :
              returnEquiv (UInt256.toByteArray (priceOut σ_evm I))
                (some [.int (Int.ofNat (priceOut σ_evm I).toNat)])
                priceTransition.returnType := by
            rw [show priceTransition.returnType = [uint256] by rfl]
            exact returnEquiv_of_encode
              (by simpa [uint256] using uint256ReturnEncoding (priceOut σ_evm I))
          exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts
            henc
        · have hover : UInt256.size ≤
              (priceRatio σ_evm I).toNat * (priceTop I).toNat := by
            omega
          have hoverSolm : UInt256.size ≤
              (priceRatio σ_solm I).toNat * (priceTop I).toNat := by
            simpa [← hratioEq] using hover
          have hbody :
              ExecTransitionBody config contract evmSolm (priceLocals I)
                priceTransition.body .reverted :=
            stairstepPriceSourceRmulOverflowReverts (evm := evmSolm) (σ := σ_solm)
              (I := I) (by simp only [evmSolm, initState]; exact hwv)
              hloadSolm hltSolm hfitMulSolm hoverSolm
          have hrev :=
            stairstepPriceRmulOverflowReverts (σ := σ_evm) (pow := priceRatio σ_evm I)
              hover rd1023
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hover :
            UInt256.size ≤ (priceLeft σ_evm I).toNat * stairstepRay.toNat := by
          omega
        have hoverSolm :
            UInt256.size ≤ (priceLeft σ_solm I).toNat * stairstepRay.toNat := by
          simpa [← hleftEq] using hover
        have hbody :
            ExecTransitionBody config contract evmSolm (priceLocals I)
              priceTransition.body .reverted :=
          stairstepPriceSourceMulRayOverflowReverts (evm := evmSolm) (σ := σ_solm)
            (I := I) (by simp only [evmSolm, initState]; exact hwv)
            hloadSolm hltSolm hoverSolm
        have hrev := stairstepPriceMulRayOverflowReverts (σ := σ_evm) hover rd987
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact stairstepPriceBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch
      hreach

end Benchmarks.Dss.LinearDecrease
