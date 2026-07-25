import Benchmarks.Dss.Vat.Slip

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

theorem uintWordLeMaxInt256_of_slt_zero {w : UInt256}
    (hmax : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    Int.ofNat w.toNat ≤ maxInt256 := by
  have hnonneg := slt_zero_eq_zero_to_nonneg w hmax
  unfold maxInt256
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hlt : (w.toNat : Int) < (2 : Int) ^ 255 := by
      exact_mod_cast (by simpa [EVM.twoPow] using hlow)
    change (w.toNat : Int) ≤ (2 : Int) ^ 255 - 1
    omega
  · have hltInt : (w.toNat : Int) < (EVM.wordModulus : Int) := by
      exact_mod_cast w.val.isLt
    have hbad : ¬ 0 ≤
        (if w.toNat < EVM.twoPow 255 then Int.ofNat w.toNat
         else Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
      simp [hlow]; omega
    exact False.elim (hbad hnonneg)

theorem uintWordGtMaxInt256_of_slt_ne_zero {w : UInt256}
    (hmax : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) :
    maxInt256 < Int.ofNat w.toNat := by
  by_cases hlow : w.toNat < EVM.twoPow 255
  · have hslt0 : UInt256.slt w (UInt256.ofNat 0) = ⟨0⟩ :=
      slt_lit_zero (a := w) (m := 0) (by norm_num) (Nat.zero_le _) hlow
    exact False.elim (hmax (by simpa using hslt0))
  · unfold maxInt256
    have hge : EVM.twoPow 255 ≤ w.toNat := by omega
    have hgeInt : (2 : Int) ^ 255 ≤ Int.ofNat w.toNat := by
      exact_mod_cast (by simpa [EVM.twoPow] using hge)
    omega

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
    simpa [hsum] using slipSignedAddWrap old addend addendInt haddend
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

theorem signedSubWrap (old sub : UInt256) (subInt : Int)
    (hsub : subInt % (Int.ofNat EVM.wordModulus) = Int.ofNat sub.toNat) :
    (Int.ofNat old.toNat - subInt) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (UInt256.sub old sub).toNat := by
  have holdLt : old.toNat < EVM.wordModulus := by
    change old.val.val < EVM.twoPow 256
    exact old.val.isLt
  have hold :
      (Int.ofNat old.toNat) % (Int.ofNat EVM.wordModulus) = Int.ofNat old.toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr holdLt)
  rw [Int.sub_emod, hold, hsub]
  by_cases hle : sub.toNat ≤ old.toNat
  · have hdiff : (UInt256.sub old sub).toNat = old.toNat - sub.toNat :=
      usub_toNat hle
    have hsubInt :
        (Int.ofNat old.toNat - Int.ofNat sub.toNat) =
          Int.ofNat (old.toNat - sub.toNat) := by
      exact (Int.ofNat_sub hle).symm
    have hlt : (old.toNat - sub.toNat) < EVM.wordModulus := by
      omega
    rw [hsubInt]
    calc
      Int.ofNat (old.toNat - sub.toNat) % Int.ofNat EVM.wordModulus =
          Int.ofNat (old.toNat - sub.toNat) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt)
      _ = Int.ofNat (UInt256.sub old sub).toNat := by rw [hdiff]
  · have hlt : old.toNat < sub.toNat := Nat.lt_of_not_ge hle
    have hdiff : (UInt256.sub old sub).toNat = UInt256.size + old.toNat - sub.toNat :=
      usub_toNat_underflow hlt
    have hwordMod : EVM.wordModulus = UInt256.size := by rfl
    have hpos : 0 < sub.toNat - old.toNat := by omega
    have hdiffLt : sub.toNat - old.toNat < EVM.wordModulus := by
      have hsubLt : sub.toNat < EVM.wordModulus := by
        change sub.val.val < EVM.twoPow 256
        exact sub.val.isLt
      omega
    have hneg :
        (Int.ofNat old.toNat - Int.ofNat sub.toNat) =
          -Int.ofNat (sub.toNat - old.toNat) := by
      have hsubOld :
          Int.ofNat sub.toNat - Int.ofNat old.toNat =
            Int.ofNat (sub.toNat - old.toNat) := by
        exact (Int.ofNat_sub (Nat.le_of_lt hlt)).symm
      calc
        Int.ofNat old.toNat - Int.ofNat sub.toNat =
            -(Int.ofNat sub.toNat - Int.ofNat old.toNat) := by omega
        _ = -Int.ofNat (sub.toNat - old.toNat) := by rw [hsubOld]
    rw [hneg]
    have hshift :
        (-Int.ofNat (sub.toNat - old.toNat)) % Int.ofNat EVM.wordModulus =
          Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) := by
      have hMpos : 0 < (Int.ofNat EVM.wordModulus) := by
        change (0 : Int) < (2 : Int) ^ 256
        norm_num
      have hdpos : 0 < (Int.ofNat (sub.toNat - old.toNat)) :=
        Int.natCast_pos.mpr hpos
      have hdlt : (Int.ofNat (sub.toNat - old.toNat)) < Int.ofNat EVM.wordModulus :=
        Int.ofNat_lt.mpr hdiffLt
      rw [Int.emod_eq_add_self_emod]
      rw [show -Int.ofNat (sub.toNat - old.toNat) + Int.ofNat EVM.wordModulus =
          Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) by omega]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hshift, hdiff]
    have hdle : sub.toNat - old.toNat ≤ EVM.wordModulus := by omega
    have hnat :
        EVM.wordModulus - (sub.toNat - old.toNat) =
          UInt256.size + old.toNat - sub.toNat := by
      rw [hwordMod]
      omega
    calc
      Int.ofNat EVM.wordModulus - Int.ofNat (sub.toNat - old.toNat) =
          Int.ofNat (EVM.wordModulus - (sub.toNat - old.toNat)) := by
        exact (Int.ofNat_sub hdle).symm
      _ = Int.ofNat (UInt256.size + old.toNat - sub.toNat) := by rw [hnat]

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
