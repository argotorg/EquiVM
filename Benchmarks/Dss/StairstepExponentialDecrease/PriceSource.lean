import Benchmarks.Dss.StairstepExponentialDecrease.RpowEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.StairstepExponentialDecrease

/-! ## `price(uint256,uint256)` front end -/

abbrev priceTop (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev priceDur (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev priceLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "top" (.int (Int.ofNat (priceTop I).toNat))).insert
    "dur" (.int (Int.ofNat (priceDur I).toNat))

def priceStepWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  stairstepSlotWord ⟨1⟩ σ I

def priceCutWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  stairstepSlotWord ⟨2⟩ σ I

abbrev stairstepRay : UInt256 :=
  ⟨1000000000000000000000000000⟩

def priceN (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (priceDur I) (priceStepWord σ I)

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

abbrev priceUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev priceUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (priceUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev priceUintBinaryLocalsZAssigned (x y old new : UInt256) : Store :=
  (priceUintBinaryLocalsZ x y old).insert "z" (.int (Int.ofNat new.toNat))

abbrev priceUintTernaryLocals (x n b : UInt256) : Store :=
  ((((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert "n"
    (.int (Int.ofNat n.toNat))).insert "x" (.int (Int.ofNat x.toNat)))

abbrev priceLocalsN (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (priceLocals I).insert "n" (.int (Int.ofNat (priceN σ I).toNat))

abbrev priceLocalsPow (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : Store :=
  (priceLocalsN σ I).insert "pow" (.int (Int.ofNat pow.toNat))

abbrev priceLocalsOut (σ : AccountMap) (I : ExecutionEnv) (pow out : UInt256) : Store :=
  (priceLocalsPow σ I pow).insert "out" (.int (Int.ofNat out.toNat))

theorem priceLocals_get_dur (I : ExecutionEnv) :
    (priceLocals I).get? "dur" = some (.int (Int.ofNat (priceDur I).toNat)) := by
  rw [priceLocals, store_get_self]

theorem priceLocals_get_top (I : ExecutionEnv) :
    (priceLocals I).get? "top" = some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocals, store_get_ne _ _ (by decide), store_get_self]

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

theorem priceUintTernaryLocals_get_x (x n b : UInt256) :
    (priceUintTernaryLocals x n b).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [priceUintTernaryLocals, store_get_self]

theorem priceUintTernaryLocals_get_n (x n b : UInt256) :
    (priceUintTernaryLocals x n b).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [priceUintTernaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem priceUintTernaryLocals_get_b (x n b : UInt256) :
    (priceUintTernaryLocals x n b).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [priceUintTernaryLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem priceLocals_get_step_none (I : ExecutionEnv) :
    (priceLocals I).get? "step" = none := by
  rw [priceLocals]
  rw [store_get_ne, store_get_ne]
  · simp
  all_goals native_decide

theorem priceLocalsN_get_top (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsN σ I).get? "top" = some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocalsN, store_get_ne _ _ (by decide), priceLocals_get_top]

theorem priceLocalsN_get_n (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsN σ I).get? "n" = some (.int (Int.ofNat (priceN σ I).toNat)) := by
  rw [priceLocalsN, store_get_self]

theorem priceLocalsN_get_cut_none (σ : AccountMap) (I : ExecutionEnv) :
    (priceLocalsN σ I).get? "cut" = none := by
  rw [priceLocalsN, store_get_ne _ _ (by decide), priceLocals]
  rw [store_get_ne, store_get_ne]
  · simp
  all_goals native_decide

theorem priceLocalsPow_get_top (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) :
    (priceLocalsPow σ I pow).get? "top" =
      some (.int (Int.ofNat (priceTop I).toNat)) := by
  rw [priceLocalsPow, store_get_ne _ _ (by decide), priceLocalsN_get_top]

theorem priceLocalsPow_get_pow (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) :
    (priceLocalsPow σ I pow).get? "pow" = some (.int (Int.ofNat pow.toNat)) := by
  rw [priceLocalsPow, store_get_self]

theorem priceLocalsOut_get_out (σ : AccountMap) (I : ExecutionEnv) (pow out : UInt256) :
    (priceLocalsOut σ I pow out).get? "out" = some (.int (Int.ofNat out.toNat)) := by
  rw [priceLocalsOut, store_get_self]

theorem evalExpr_priceDur {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := priceLocals I } evm (.var "dur") =
      .ok (.int (Int.ofNat (priceDur I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((priceLocals I).get? "dur") =
    .ok (.int (Int.ofNat (priceDur I).toNat))
  rw [priceLocals_get_dur]
  rfl

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

theorem evalExpr_priceStep_zero {evm : EVM.State} {I : ExecutionEnv}
    (hstep : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := priceLocals I } evm (.storage stepRef) =
      .ok (.int 0) := by
  have hload : storageLocLoad evm (wordLoc ⟨1⟩) = .int 0 := by
    rw [stairstepStorageLocLoad_uint256, hstep]
    native_decide
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := priceLocals I }) (evm := evm)
    (slot := stepRef) (er := ({ base := "step", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨1⟩) (value := .int 0)
    (hbase := priceLocals_get_step_none I)
    (her := by simp [evalStorageRef, evalStorageRefSteps, stepRef, EvalResult.bind, pure, bind])
    (hty := by simp [contract, storageDecls, storageTypeAt?, uint256St])
    (hloc := by rfl)
    (hload := hload)

theorem evalExpr_priceStep_word {evm : EVM.State} {I : ExecutionEnv} {step : UInt256}
    (hstep : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = step) :
    evalExpr? config { contract := contract, locals := priceLocals I } evm (.storage stepRef) =
      .ok (.int (Int.ofNat step.toNat)) := by
  have hload : storageLocLoad evm (wordLoc ⟨1⟩) = .int (Int.ofNat step.toNat) := by
    rw [stairstepStorageLocLoad_uint256, hstep]
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := priceLocals I }) (evm := evm)
    (slot := stepRef) (er := ({ base := "step", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨1⟩) (value := .int (Int.ofNat step.toNat))
    (hbase := priceLocals_get_step_none I)
    (her := by simp [evalStorageRef, evalStorageRefSteps, stepRef, EvalResult.bind, pure, bind])
    (hty := by simp [contract, storageDecls, storageTypeAt?, uint256St])
    (hloc := by rfl)
    (hload := hload)

theorem evalExpr_priceCut_word {evm : EVM.State} {locals : Store} {cut : UInt256}
    (hbase : locals.get? "cut" = none)
    (hcut : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = cut) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage cutRef) =
      .ok (.int (Int.ofNat cut.toNat)) := by
  have hload : storageLocLoad evm (wordLoc ⟨2⟩) = .int (Int.ofNat cut.toNat) := by
    rw [stairstepStorageLocLoad_uint256, hcut]
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := cutRef) (er := ({ base := "cut", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨2⟩) (value := .int (Int.ofNat cut.toNat))
    (hbase := hbase)
    (her := by simp [evalStorageRef, evalStorageRefSteps, cutRef, EvalResult.bind, pure, bind])
    (hty := by simp [contract, storageDecls, storageTypeAt?, uint256St])
    (hloc := by rfl)
    (hload := hload)

theorem evalExpr_priceDiv_step_zero {evm : EVM.State} {I : ExecutionEnv}
    (hstep : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := priceLocals I } evm
      (.binary .div (.var "dur") (.storage stepRef)) = .revert := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_priceDur, evalExpr_priceStep_zero hstep,
    evalBinaryOp?]

theorem evalExpr_priceDiv_ok {evm : EVM.State} {I : ExecutionEnv} {step : UInt256}
    (hstepLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = step)
    (hstep : step ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := priceLocals I } evm
      (.binary .div (.var "dur") (.storage stepRef)) =
        .ok (.int (Int.ofNat (UInt256.div (priceDur I) step).toNat)) := by
  have hneNat : step.toNat ≠ 0 := by
    intro hbad
    exact hstep (uint256_toNat_eq_zero hbad)
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_priceDur, evalExpr_priceStep_word hstepLoad,
    evalBinaryOp?, hneNat]
  rw [udiv_toNat]
  norm_num

theorem stairstepPriceSourceStepZeroReverts {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstep : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hlet := evalExpr_priceDiv_step_zero (evm := evm) (I := I) hstep
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hlet)
  simpa [ExecTransitionBody, priceTransition, nonpayable] using ExecFuncBody.execBlockRevert hblock

theorem stairstepExecRpowFunctionReturnNZero (evm : EVM.State) {x b : UInt256} :
    ExecFuncBody config { contract := contract, locals := priceUintTernaryLocals x ⟨0⟩ b }
      evm rpowFunction.body
      (.returned { contract := contract, locals := priceUintTernaryLocals x ⟨0⟩ b } evm
        (some [.int (Int.ofNat b.toNat)])) := by
  let locals := priceUintTernaryLocals x ⟨0⟩ b
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "n") =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))
    rw [show locals.get? "n" = some (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simpa [locals] using priceUintTernaryLocals_get_n x ⟨0⟩ b]
    rfl
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
        .ok (.int (Int.ofNat b.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "b") =
      .ok (.int (Int.ofNat b.toNat))
    rw [show locals.get? "b" = some (.int (Int.ofNat b.toNat)) by
      simpa [locals] using priceUintTernaryLocals_get_b x ⟨0⟩ b]
    rfl
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hnZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hn, hzeroLit, evalBinaryOp?]
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .return [.var "b"] ]
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat b.toNat)])) :=
    ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hb))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat b.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hnZero hthen)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

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

theorem evalExprs_priceRpowArgsNZero {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hcut : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hn : priceN σ I = ⟨0⟩) :
    evalExprs? config { contract := contract, locals := priceLocalsN σ I } evm
      [.storage cutRef, .var "n", .intLit RAY] =
        .ok [.int (Int.ofNat (priceCutWord σ I).toNat), .int 0,
          .int (Int.ofNat stairstepRay.toNat)] := by
  have hcutEval :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.storage cutRef) = .ok (.int (Int.ofNat (priceCutWord σ I).toNat)) :=
    evalExpr_priceCut_word (priceLocalsN_get_cut_none σ I) hcut
  have hnEval :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.var "n") = .ok (.int (Int.ofNat (priceN σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsN_get_n σ I)
  have hRay :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.intLit RAY) = .ok (.int (Int.ofNat stairstepRay.toNat)) := by
    simp [evalExpr?, pure, RAY_eq_stairstepRay_toNat]
  simp [evalExprs?, hcutEval, hnEval, hRay, EvalResult.bind, bind, pure, hn]

theorem evalExprs_priceRmulRayArgs {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} :
    evalExprs? config { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm
      [.var "top", .var "pow"] =
        .ok [.int (Int.ofNat (priceTop I).toNat),
          .int (Int.ofNat stairstepRay.toNat)] := by
  have htop :
      evalExpr? config { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm
        (.var "top") = .ok (.int (Int.ofNat (priceTop I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsPow_get_top σ I stairstepRay)
  have hpow :
      evalExpr? config { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm
        (.var "pow") = .ok (.int (Int.ofNat stairstepRay.toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsPow_get_pow σ I stairstepRay)
  simp [evalExprs?, htop, hpow, EvalResult.bind, bind, pure]

theorem evalExprs_priceRpowArgs {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hcut : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I) :
    evalExprs? config { contract := contract, locals := priceLocalsN σ I } evm
      [.storage cutRef, .var "n", .intLit RAY] =
        .ok [.int (Int.ofNat (priceCutWord σ I).toNat),
          .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)] := by
  have hcutEval :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.storage cutRef) = .ok (.int (Int.ofNat (priceCutWord σ I).toNat)) :=
    evalExpr_priceCut_word (priceLocalsN_get_cut_none σ I) hcut
  have hnEval :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.var "n") = .ok (.int (Int.ofNat (priceN σ I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsN_get_n σ I)
  have hRay :
      evalExpr? config { contract := contract, locals := priceLocalsN σ I } evm
        (.intLit RAY) = .ok (.int (Int.ofNat stairstepRay.toNat)) := by
    simp [evalExpr?, pure, RAY_eq_stairstepRay_toNat]
  simp [evalExprs?, hcutEval, hnEval, hRay, EvalResult.bind, bind, pure]

theorem evalExprs_priceRmulArgs {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {pow : UInt256} :
    evalExprs? config { contract := contract, locals := priceLocalsPow σ I pow } evm
      [.var "top", .var "pow"] =
        .ok [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat pow.toNat)] := by
  have htop :
      evalExpr? config { contract := contract, locals := priceLocalsPow σ I pow } evm
        (.var "top") = .ok (.int (Int.ofNat (priceTop I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsPow_get_top σ I pow)
  have hpow :
      evalExpr? config { contract := contract, locals := priceLocalsPow σ I pow } evm
        (.var "pow") = .ok (.int (Int.ofNat pow.toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsPow_get_pow σ I pow)
  simp [evalExprs?, htop, hpow, EvalResult.bind, bind, pure]

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

theorem stairstepPriceSourceXZeroNNonzeroReturns {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hn : priceN σ I ≠ ⟨0⟩)
    (hcut : priceCutWord σ I = ⟨0⟩) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body
      (.returned { contract := contract, locals := priceLocalsOut σ I ⟨0⟩ ⟨0⟩ }
        evm (some [.int 0])) := by
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgs (evm := evm) (σ := σ) (I := I) hcutLoad
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat),
            .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (uintTernaryLocals ⟨0⟩ (priceN σ I) stairstepRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?, hcut, stairstepUInt256Zero_toNat]
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        (.ok { contract := contract, locals := priceLocalsPow σ I ⟨0⟩ } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat),
        .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := uintTernaryLocals ⟨0⟩ (priceN σ I) stairstepRay)
      hrpowArgs hlookupRpow hbindRpow
      (execRpowFunctionReturnXZeroNNonzero (evm := evm) (n := priceN σ I)
        (b := stairstepRay) hn)
    simpa [resumeAfterInternalCall, priceLocalsPow] using h
  have hrmulArgs := evalExprs_priceRmulArgs (evm := evm) (σ := σ) (I := I)
    (pow := (⟨0⟩ : UInt256))
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat), .int 0] =
        some (priceUintBinaryLocals (priceTop I) ⟨0⟩) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?, stairstepUInt256Zero_toNat]
  have hprodZero : priceTop I * (⟨0⟩ : UInt256) = ⟨0⟩ :=
    uint256_mul_zero (priceTop I)
  have hq : (⟨0⟩ : UInt256) = UInt256.div (priceTop I * ⟨0⟩) stairstepRay := by
    rw [hprodZero, uint256_div_zero_num]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := priceLocalsPow σ I ⟨0⟩ } evm
        (.internalCall "rmul" [.var "top", .var "pow"] "out")
        (.ok { contract := contract, locals := priceLocalsOut σ I ⟨0⟩ ⟨0⟩ } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsPow σ I ⟨0⟩))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "pow"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat), .int 0])
      (callee := rmulFunction) (locals := priceUintBinaryLocals (priceTop I) ⟨0⟩)
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionReturn evm (x := priceTop I) (y := ⟨0⟩)
        (prod := priceTop I * ⟨0⟩) (q := ⟨0⟩) rfl
        (by norm_num [UInt256.size]) hq)
    simpa [resumeAfterInternalCall, priceLocalsOut] using h
  have hout :
      evalExpr? config { contract := contract, locals := priceLocalsOut σ I ⟨0⟩ ⟨0⟩ }
        evm (.var "out") = .ok (.int 0) := by
    have h := evalExpr_price_varUInt256
      (evm := evm) (locals := priceLocalsOut σ I ⟨0⟩ ⟨0⟩)
      (name := "out") (value := (⟨0⟩ : UInt256))
      (priceLocalsOut_get_out σ I ⟨0⟩ ⟨0⟩)
    simpa [stairstepUInt256Zero_toNat] using h
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        (.returned { contract := contract, locals := priceLocalsOut σ I ⟨0⟩ ⟨0⟩ }
          evm (some [.int 0])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal hrpowReturn ?_
    refine ExecBlock.consNormal hrmulReturn ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hout))
  simpa [ExecTransitionBody, priceTransition, nonpayable]
    using ExecFuncBody.execBlockRet hblock

theorem stairstepPriceSourceNZeroReturns {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hn : priceN σ I = ⟨0⟩)
    (hfit : stairstepRay.toNat * (priceTop I).toNat < UInt256.size) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body
      (.returned { contract := contract, locals := priceLocalsOut σ I stairstepRay (priceTop I) }
        evm (some [.int (Int.ofNat (priceTop I).toNat)])) := by
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgsNZero (evm := evm) (σ := σ) (I := I)
    hcutLoad hn
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat), .int 0,
            .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintTernaryLocals (priceCutWord σ I) ⟨0⟩ stairstepRay) := by
    simp [rpowFunction, priceUintTernaryLocals, bindParams?]
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        (.ok { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat), .int 0,
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := priceUintTernaryLocals (priceCutWord σ I) ⟨0⟩ stairstepRay)
      hrpowArgs hlookupRpow hbindRpow
      (stairstepExecRpowFunctionReturnNZero (evm := evm) (x := priceCutWord σ I)
        (b := stairstepRay))
    simpa [resumeAfterInternalCall, priceLocalsPow] using h
  have hrmulArgs := evalExprs_priceRmulRayArgs (evm := evm) (σ := σ) (I := I)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintBinaryLocals (priceTop I) stairstepRay) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hfitLocal : (priceTop I).toNat * stairstepRay.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hfit
  have hprodComm : priceTop I * stairstepRay = stairstepRay * priceTop I := by
    simpa using u256_mul_comm (priceTop I) stairstepRay
  have hq : priceTop I = UInt256.div (priceTop I * stairstepRay) stairstepRay := by
    rw [hprodComm]
    exact (stairstepRay_mul_div_cancel (priceTop I) hfit).symm
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm
        (.internalCall "rmul" [.var "top", .var "pow"] "out")
        (.ok (Frame.mk contract (priceLocalsOut σ I stairstepRay (priceTop I))) evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsPow σ I stairstepRay))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "pow"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat),
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := rmulFunction) (locals := priceUintBinaryLocals (priceTop I) stairstepRay)
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionReturn evm (x := priceTop I) (y := stairstepRay)
        (prod := priceTop I * stairstepRay) (q := priceTop I) rfl hfitLocal hq)
    simpa [resumeAfterInternalCall, priceLocalsOut] using h
  have hout :
      evalExpr? config
          { contract := contract, locals := priceLocalsOut σ I stairstepRay (priceTop I) }
          evm (.var "out") = .ok (.int (Int.ofNat (priceTop I).toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsOut_get_out σ I stairstepRay (priceTop I))
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        (.returned (Frame.mk contract (priceLocalsOut σ I stairstepRay (priceTop I)))
          evm (some [.int (Int.ofNat (priceTop I).toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal hrpowReturn ?_
    refine ExecBlock.consNormal hrmulReturn ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hout))
  simpa [ExecTransitionBody, priceTransition, nonpayable]
    using ExecFuncBody.execBlockRet hblock

theorem stairstepPriceSourceNZeroRmulOverflowReverts {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hn : priceN σ I = ⟨0⟩)
    (hover : UInt256.size ≤ stairstepRay.toNat * (priceTop I).toNat) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgsNZero (evm := evm) (σ := σ) (I := I)
    hcutLoad hn
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat), .int 0,
            .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintTernaryLocals (priceCutWord σ I) ⟨0⟩ stairstepRay) := by
    simp [rpowFunction, priceUintTernaryLocals, bindParams?]
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        (.ok { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat), .int 0,
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := priceUintTernaryLocals (priceCutWord σ I) ⟨0⟩ stairstepRay)
      hrpowArgs hlookupRpow hbindRpow
      (stairstepExecRpowFunctionReturnNZero (evm := evm) (x := priceCutWord σ I)
        (b := stairstepRay))
    simpa [resumeAfterInternalCall, priceLocalsPow] using h
  have hrmulArgs := evalExprs_priceRmulRayArgs (evm := evm) (σ := σ) (I := I)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (priceUintBinaryLocals (priceTop I) stairstepRay) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hoverLocal : UInt256.size ≤ (priceTop I).toNat * stairstepRay.toNat := by
    simpa [Nat.mul_comm] using hover
  have hrmulRevert :
      ExecStmt config { contract := contract, locals := priceLocalsPow σ I stairstepRay } evm
        (.internalCall "rmul" [.var "top", .var "pow"] "out") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsPow σ I stairstepRay))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "pow"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat),
        .int (Int.ofNat stairstepRay.toNat)])
      (callee := rmulFunction) (locals := priceUintBinaryLocals (priceTop I) stairstepRay)
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionRevertMul evm (x := priceTop I) (y := stairstepRay)
        hoverLocal)
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal hrpowReturn ?_
    exact ExecBlock.consRevert hrmulRevert
  simpa [ExecTransitionBody, priceTransition, nonpayable]
    using ExecFuncBody.execBlockRevert hblock

theorem stairstepPriceSourceRpowReverts {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay }
        evm rpowFunction.body .reverted) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgs (evm := evm) (σ := σ) (I := I) hcutLoad
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat),
            .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowRevert :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat),
        .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay)
      hrpowArgs hlookupRpow hbindRpow hrpowBody
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    exact ExecBlock.consRevert hrpowRevert
  simpa [ExecTransitionBody, priceTransition, nonpayable]
    using ExecFuncBody.execBlockRevert hblock

theorem stairstepPriceSourceRpowReturns {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv} {pow : UInt256} {rpowLocals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay }
        evm rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evm
          (some [.int (Int.ofNat pow.toNat)])))
    (hfit : pow.toNat * (priceTop I).toNat < UInt256.size) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body
      (.returned
        { contract := contract,
          locals :=
            priceLocalsOut σ I pow (UInt256.div (pow * priceTop I) stairstepRay) }
        evm
        (some [.int (Int.ofNat (UInt256.div (pow * priceTop I) stairstepRay).toNat)])) := by
  let out := UInt256.div (pow * priceTop I) stairstepRay
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgs (evm := evm) (σ := σ) (I := I) hcutLoad
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat),
            .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        (.ok { contract := contract, locals := priceLocalsPow σ I pow } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat),
        .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay)
      (calleeSolm := { contract := contract, locals := rpowLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, priceLocalsPow] using h
  have hrmulArgs := evalExprs_priceRmulArgs (evm := evm) (σ := σ) (I := I)
    (pow := pow)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat pow.toNat)] =
        some (priceUintBinaryLocals (priceTop I) pow) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hfitLocal : (priceTop I).toNat * pow.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hfit
  have hq : out = UInt256.div (priceTop I * pow) stairstepRay := by
    dsimp [out]
    rw [show pow * priceTop I = priceTop I * pow by
      simpa using u256_mul_comm pow (priceTop I)]
  have hrmulReturn :
      ExecStmt config { contract := contract, locals := priceLocalsPow σ I pow } evm
        (.internalCall "rmul" [.var "top", .var "pow"] "out")
        (.ok { contract := contract, locals := priceLocalsOut σ I pow out } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsPow σ I pow))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "pow"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat pow.toNat)])
      (callee := rmulFunction) (locals := priceUintBinaryLocals (priceTop I) pow)
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionReturn evm (x := priceTop I) (y := pow)
        (prod := priceTop I * pow) (q := out) rfl hfitLocal hq)
    simpa [resumeAfterInternalCall, priceLocalsOut, out] using h
  have hout :
      evalExpr? config { contract := contract, locals := priceLocalsOut σ I pow out }
        evm (.var "out") = .ok (.int (Int.ofNat out.toNat)) :=
    evalExpr_price_varUInt256 (priceLocalsOut_get_out σ I pow out)
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        (.returned { contract := contract, locals := priceLocalsOut σ I pow out } evm
          (some [.int (Int.ofNat out.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal hrpowReturn ?_
    refine ExecBlock.consNormal hrmulReturn ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hout))
  simpa [ExecTransitionBody, priceTransition, nonpayable, out]
    using ExecFuncBody.execBlockRet hblock

theorem stairstepPriceSourceRpowReturnsRmulOverflowReverts
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {pow : UInt256} {rpowLocals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hstepLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = priceStepWord σ I)
    (hcutLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = priceCutWord σ I)
    (hstep : priceStepWord σ I ≠ ⟨0⟩)
    (hrpowBody :
      ExecFuncBody config
        { contract := contract,
          locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay }
        evm rpowFunction.body
        (.returned { contract := contract, locals := rpowLocals } evm
          (some [.int (Int.ofNat pow.toNat)])))
    (hover : UInt256.size ≤ pow.toNat * (priceTop I).toNat) :
    ExecTransitionBody config contract evm (priceLocals I) priceTransition.body .reverted := by
  have hlet :
      evalExpr? config { contract := contract, locals := priceLocals I } evm
        (.binary .div (.var "dur") (.storage stepRef)) =
          .ok (.int (Int.ofNat (priceN σ I).toNat)) := by
    simpa [priceN] using
      evalExpr_priceDiv_ok (evm := evm) (I := I) (step := priceStepWord σ I)
        hstepLoad hstep
  have hrpowArgs := evalExprs_priceRpowArgs (evm := evm) (σ := σ) (I := I) hcutLoad
  have hlookupRpow : lookupCallable? contract "rpow" = some rpowFunction.toCallable := by
    rfl
  have hbindRpow :
      bindParams? rpowFunction.params
          [.int (Int.ofNat (priceCutWord σ I).toNat),
            .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)] =
        some (uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay) := by
    simp [rpowFunction, uintTernaryLocals, bindParams?]
  have hrpowReturn :
      ExecStmt config { contract := contract, locals := priceLocalsN σ I } evm
        (.internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow")
        (.ok { contract := contract, locals := priceLocalsPow σ I pow } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := priceLocalsN σ I })
      (evm := evm) (name := "rpow") (retVar := "pow")
      (args := [.storage cutRef, .var "n", .intLit RAY])
      (argVals := [.int (Int.ofNat (priceCutWord σ I).toNat),
        .int (Int.ofNat (priceN σ I).toNat), .int (Int.ofNat stairstepRay.toNat)])
      (callee := rpowFunction)
      (locals := uintTernaryLocals (priceCutWord σ I) (priceN σ I) stairstepRay)
      (calleeSolm := { contract := contract, locals := rpowLocals })
      hrpowArgs hlookupRpow hbindRpow hrpowBody
    simpa [resumeAfterInternalCall, priceLocalsPow] using h
  have hrmulArgs := evalExprs_priceRmulArgs (evm := evm) (σ := σ) (I := I)
    (pow := pow)
  have hlookupRmul : lookupCallable? contract "rmul" = some rmulFunction.toCallable := by
    rfl
  have hbindRmul :
      bindParams? rmulFunction.params
          [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat pow.toNat)] =
        some (priceUintBinaryLocals (priceTop I) pow) := by
    simp [rmulFunction, priceUintBinaryLocals, bindParams?]
  have hoverLocal : UInt256.size ≤ (priceTop I).toNat * pow.toNat := by
    simpa [Nat.mul_comm] using hover
  have hrmulRevert :
      ExecStmt config { contract := contract, locals := priceLocalsPow σ I pow } evm
        (.internalCall "rmul" [.var "top", .var "pow"] "out") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (priceLocalsPow σ I pow))
      (evm := evm) (name := "rmul") (retVar := "out")
      (args := [.var "top", .var "pow"])
      (argVals := [.int (Int.ofNat (priceTop I).toNat), .int (Int.ofNat pow.toNat)])
      (callee := rmulFunction) (locals := priceUintBinaryLocals (priceTop I) pow)
      hrmulArgs hlookupRmul hbindRmul
      (stairstepExecRmulFunctionRevertMul evm (x := priceTop I) (y := pow) hoverLocal)
  have hblock :
      ExecBlock config { contract := contract, locals := priceLocals I } evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
          .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
          .internalCall "rmul" [.var "top", .var "pow"] "out",
          .return [.var "out"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    refine ExecBlock.consNormal hrpowReturn ?_
    exact ExecBlock.consRevert hrmulRevert
  simpa [ExecTransitionBody, priceTransition, nonpayable]
    using ExecFuncBody.execBlockRevert hblock


end Benchmarks.Dss.StairstepExponentialDecrease
