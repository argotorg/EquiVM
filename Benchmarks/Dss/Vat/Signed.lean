import Reasoning.WordArithmetic
import Benchmarks.Dss.Vat.Slip

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach


theorem evalExpr_fold_wordWrapAdd_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {old addend sum : UInt256} {addendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (haddend : addendInt % (Int.ofNat EVM.wordModulus) = Int.ofNat addend.toNat)
    (hsum : sum = addend + old) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wordWrap256 (.binary .add x y)) =
        .ok (.int (Int.ofNat sum.toNat)) := by
  have hwrap :
      (Int.ofNat old.toNat + addendInt) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat sum.toNat := by
    simpa [hsum] using signedAddWrap old addend addendInt haddend
  have hmodNe : ¬ EVM.wordModulus = 0 := by decide
  simp [wordWrap256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hmodNe]
  simpa using hwrap

theorem evalExpr_fold_wordWrapSub_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {old diff : UInt256} {subtrahendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hwrap :
      (Int.ofNat old.toNat - subtrahendInt) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat diff.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wordWrap256 (.binary .sub x y)) =
        .ok (.int (Int.ofNat diff.toNat)) := by
  have hmodNe : ¬ EVM.wordModulus = 0 := by decide
  simp [wordWrap256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hmodNe]
  simpa using hwrap


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

theorem evalExpr_fold_mul_int_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (.int a))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y = .ok (.int b))
    (hprod : prod = a * b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .mul x y) =
      .ok (.int prod) := by
  subst prod
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]

theorem evalExpr_fold_s256_ok {evm : EVM.State} {locals : Store} {e : Expr} {i : Int}
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

theorem evalSignedAddGuardNeg_true {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {addendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 ≤ addendInt ∨ new.toNat ≤ old.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool true) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonneg =>
      exact vatEvalExpr_or_true_left (vatEvalExpr_ge_int_true hy hzero hnonneg)
  | inr hle =>
      by_cases hnonneg : 0 ≤ addendInt
      · exact vatEvalExpr_or_true_left (vatEvalExpr_ge_int_true hy hzero hnonneg)
      · have hleft := vatEvalExpr_ge_int_false hy hzero (not_le.mp hnonneg)
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_le_uint256_true hnew hx hle)

theorem evalSignedAddGuardPos_true {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {addendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : addendInt ≤ 0 ∨ old.toNat ≤ new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) =
      .ok (.bool true) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonpos =>
      exact vatEvalExpr_or_true_left (vatEvalExpr_le_int_true hy hzero hnonpos)
  | inr hle =>
      by_cases hnonpos : addendInt ≤ 0
      · exact vatEvalExpr_or_true_left (vatEvalExpr_le_int_true hy hzero hnonpos)
      · have hleft := vatEvalExpr_le_int_false hy hzero (not_le.mp hnonpos)
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_ge_uint256_true hnew hx hle)

theorem evalSignedAddGuardNeg_false {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {addendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : addendInt < 0 ∧ old.toNat < new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool false) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_ge_int_false hy hzero hcond.1
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_le_uint256_false hnew hx hcond.2)

theorem evalSignedAddGuardPos_false {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {addendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int addendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 < addendInt ∧ new.toNat < old.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) =
      .ok (.bool false) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_le_int_false hy hzero hcond.1
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_ge_uint256_false hnew hx hcond.2)

theorem evalSignedSubGuardNeg_true {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : subtrahendInt ≤ 0 ∨ new.toNat ≤ old.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool true) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonpos =>
      exact vatEvalExpr_or_true_left (vatEvalExpr_le_int_true hy hzero hnonpos)
  | inr hle =>
      by_cases hnonpos : subtrahendInt ≤ 0
      · exact vatEvalExpr_or_true_left (vatEvalExpr_le_int_true hy hzero hnonpos)
      · have hleft := vatEvalExpr_le_int_false hy hzero (not_le.mp hnonpos)
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_le_uint256_true hnew hx hle)

theorem evalSignedSubGuardPos_true {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 ≤ subtrahendInt ∨ old.toNat ≤ new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) =
      .ok (.bool true) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  cases hcond with
  | inl hnonneg =>
      exact vatEvalExpr_or_true_left (vatEvalExpr_ge_int_true hy hzero hnonneg)
  | inr hle =>
      by_cases hnonneg : 0 ≤ subtrahendInt
      · exact vatEvalExpr_or_true_left (vatEvalExpr_ge_int_true hy hzero hnonneg)
      · have hleft := vatEvalExpr_ge_int_false hy hzero (not_le.mp hnonneg)
        exact vatEvalExpr_or_false_right hleft
          (vatEvalExpr_ge_uint256_true hnew hx hle)

theorem evalSignedSubGuardNeg_false {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 < subtrahendInt ∧ old.toNat < new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool false) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_le_int_false hy hzero hcond.1
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_le_uint256_false hnew hx hcond.2)

theorem evalSignedSubGuardPos_false {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hnew : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat new.toNat)))
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : subtrahendInt < 0 ∧ new.toNat < old.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) =
      .ok (.bool false) := by
  have hzero :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hleft := vatEvalExpr_ge_int_false hy hzero hcond.1
  exact vatEvalExpr_or_false_right hleft
    (vatEvalExpr_ge_uint256_false hnew hx hcond.2)

end Benchmarks.Dss.Vat
