import Reasoning.SolmArithmetic
import Reasoning.EVMWord
import Benchmarks.Dss.Flipper.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## Shared checked multiplication helpers -/

abbrev flipperONEWord : UInt256 :=
  ⟨1000000000000000000⟩

theorem evalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) :=
  Reasoning.Theory.evalExpr_varUInt256 (cfg := config) (contract := contract) h

theorem evalExpr_flipperONE {evm : EVM.State} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit ONE) =
      .ok (.int (Int.ofNat flipperONEWord.toNat)) := by
  have hone : Int.ofNat flipperONEWord.toNat = ONE := by native_decide
  simpa [evalExpr?, pure, hone]

theorem evalExpr_flipperBeg_of_get {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbeg : locals.get? "beg" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I) (.storage begRef) =
        .ok (.int (Int.ofNat (solcSlotWordAt ⟨4⟩ σ I).toNat)) := by
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
    (storageLocLoad_uint256 (initState σ σ₀ g A I) ⟨4⟩)


theorem evalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = UInt256.mul a b)
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
        .ok (.bool true) :=
  Reasoning.Theory.evalExpr_checkedMulRequire_ok (cfg := config) (contract := contract) hx hy hz
    hprod hfit

set_option maxHeartbeats 1000000 in
theorem flipperCheckedMulOk {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret x y : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hret : (D_J flipperBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (h : RD flipperBytecode I g s0 ⟨6305⟩ (y :: x :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD flipperBytecode I g s0 ret (UInt256.mul x y :: R)
      mem aw rdata σ k' C' := by
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
    exact ⟨_, _, by simpa [hy0, u256_mul_zero] using rdret⟩
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
      u256_mul_div_right_eq_of_noOverflow x y hy0 hfit
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
theorem flipperCheckedMulRevert {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret x y : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hov : R.length + 10 ≤ 1024)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (h : RD flipperBytecode I g s0 ⟨6305⟩ (y :: x :: ret :: R)
      mem aw rdata σ k C) :
    RDrev flipperBytecode g s0 := by
  have hy0 : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (UInt256.mul x y) y ≠ x :=
    u256_mul_div_right_overflow_ne x y hover
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
  exact RD.solcPush1Dup1Revert0 rd6337
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

end Benchmarks.Dss.Flipper
