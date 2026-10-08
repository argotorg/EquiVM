import Benchmarks.EAS.Attester.MultiAttestSourceRow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def AttestRowView (schemas rows expected : List Value) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i : Nat) : Prop :=
  ∃ schema inputs, schemas[i]? = some schema ∧ rows[i]? = some (.array inputs) ∧
    expected[i]? = some (.tuple [schema, .array (attestArrayValues (values i) 0 inputs.length)]) ∧
    inputs.length = counts i ∧ inputs.length < UInt256.size ∧
    normalizeRawBoolWord? schema = .ok schema ∧
    ∀ k < inputs.length, inputs[k]? = some (.int (Int.ofNat (values i k).toNat))

def attestAllocationEnd (allocation : Nat) (counts : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => allocation
  | n + 1 => attestAllocationEnd (allocation + 480 * counts i) counts (i + 1) n

def attestOuterUntouched (name : Ident) : Prop := attestRowUntouched name ∧ name ≠ "i"

theorem attestOuterRun {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests expected : List Value} {i remaining n allocation : Nat}
    {counts : Nat → Nat} {values : Nat → Nat → UInt256}
    (hn : n < UInt256.size) (hi : i + remaining = n)
    (hindex : locals.get? "i" = some (.int (Int.ofNat i)))
    (hcount : locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaInputs" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (ha : locals.get? "allocationEnd" = some (.int (Int.ofNat allocation)))
    (hlen : requests.length = n) (hexpected : expected.length = n)
    (hfilled : ∀ k < i, requests[k]? = expected[k]?)
    (hviews : ∀ k < n, AttestRowView schemas rows expected counts values k) :
    ((∃ k, i ≤ k ∧ k < n ∧ rows[k]? = some (.array [])) ∧
      ExecForLoop config ⟨C, locals, imms⟩ evm attestOuterCond attestOuterPost attestOuterBody
          .reverted) ∨
    ((∀ k, i ≤ k → k < n → rows[k]? ≠ some (.array [])) ∧
      ∃ result, ExecForLoop config ⟨C, locals, imms⟩ evm attestOuterCond attestOuterPost
          attestOuterBody
        (.ok ⟨C, result, imms⟩ evm) ∧ result.get? "multiRequests" = some (.array expected) ∧
        result.get? "allocationEnd" =
          some (.int (Int.ofNat (attestAllocationEnd allocation counts i remaining))) ∧
        ∀ name, attestOuterUntouched name → result.get? name = locals.get? name) := by
  induction remaining generalizing locals requests i allocation with
  | zero =>
      have hin : i = n := by omega
      have hrequests : requests = expected := by
        apply List.ext_getElem (hlen.trans hexpected.symm)
        intro k hk hk'
        have he := hfilled k (by omega)
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.some.injEq] at he
        exact he
      refine .inr ⟨by intro k hk hk'; omega, locals, ExecForLoop.falseDone ?_,
        by simpa only [hrequests] using hq, ha, by intro name _; rfl⟩
      simpa only [attestOuterCond, hin, Nat.lt_irrefl, decide_false] using
        (evalLocalNatLt (cfg := config) (solm := ⟨C, locals, imms⟩) (evm := evm) hindex hcount)
  | succ remaining ih =>
      have hin : i < n := by omega
      have hcond : evalExpr? config ⟨C, locals, imms⟩ evm attestOuterCond = .ok (.bool true) := by
        simpa only [attestOuterCond, hin, decide_true] using
          (evalLocalNatLt (cfg := config) (solm := ⟨C, locals, imms⟩) (evm := evm) hindex hcount)
      obtain ⟨schema, inputs, hsch, hrow, hexp, hlenRow, hfit, hsnormal, hinputs⟩ := hviews i hin
      by_cases hempty : inputs = []
      · subst inputs
        exact .inl ⟨⟨i, le_refl _, hin, hrow⟩,
          ExecForLoop.bodyRevert hcond (attestSourceRowEmpty hindex hr hrow)⟩
      · have hpos : 0 < inputs.length := List.length_pos_iff.mpr hempty
        obtain ⟨l1, hbody, hrequests, ha1, hsame⟩ := attestSourceRow
          (C := C) (imms := imms) (evm := evm)
          hindex hs hr hq hrow hsch (by omega) hpos hfit ha hsnormal hinputs
        have hi1 : l1.get? "i" = some (.int (Int.ofNat i)) :=
          (hsame "i" (by simp [attestRowUntouched])).trans hindex
        let l2 := l1.insert "i" (.int (Int.ofNat (i + 1)))
        have hpost : ExecBlock config ⟨C, l1, imms⟩ evm attestOuterPost
            (.ok ⟨C, l2, imms⟩ evm) := execLocalIncrement hi1 (by omega)
        have hpreserved (name : Ident) (hname : attestOuterUntouched name) :
            l2.get? name = locals.get? name := by
          have hh := hsame name hname.1
          simpa only [l2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr (Ne.symm hname.2), Bool.false_eq_true, if_false] using hh
        have hfilled' : ∀ k < i + 1,
            (requests.set i (.tuple [schema, .array (attestArrayValues (values i) 0
                inputs.length)]))[k]? = expected[k]? := by
          intro k hk
          by_cases hki : k = i
          · subst k
            rw [List.getElem?_set_self (by omega), hexp]
          · rw [List.getElem?_set_ne (Ne.symm hki)]
            exact hfilled k (by omega)
        have hrun := ih (locals := l2)
          (requests := requests.set i (.tuple [schema,
              .array (attestArrayValues (values i) 0 inputs.length)]))
          (i := i + 1) (by omega) (by simp [l2])
          ((hpreserved "schemaLength" (by simp [attestOuterUntouched,
              attestRowUntouched])).trans hcount)
          ((hpreserved "schemas" (by simp [attestOuterUntouched, attestRowUntouched])).trans hs)
          ((hpreserved "schemaInputs" (by simp [attestOuterUntouched,
              attestRowUntouched])).trans hr)
          (by simpa [l2, Std.HashMap.getElem?_insert] using hrequests)
          (by simpa [l2, Std.HashMap.getElem?_insert] using ha1)
          (by simpa using hlen) hfilled'
        rcases hrun with ⟨hbad, hrun⟩ | ⟨hgood, result, hrun, hfinal, haFinal, hsameFinal⟩
        · obtain ⟨k, hk, hk', hrowk⟩ := hbad
          exact .inl ⟨⟨k, by omega, hk', hrowk⟩, ExecForLoop.iterate hcond hbody hpost hrun⟩
        · refine .inr ⟨?_, result, ExecForLoop.iterate hcond hbody hpost hrun, hfinal, ?_, ?_⟩
          · intro k hk hk'
            by_cases hki : k = i
            · subst k
              rw [hrow]
              simpa only [ne_eq, Option.some.injEq, Value.array.injEq] using hempty
            · exact hgood k (by omega) hk'
          · simpa only [attestAllocationEnd, hlenRow] using haFinal
          · intro name hname
            exact (hsameFinal name hname).trans (hpreserved name hname)

theorem attestOuterFor {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests expected : List Value} {n allocation : Nat} {counts :
        Nat → Nat} {values : Nat → Nat → UInt256}
    (hn : n < UInt256.size)
    (hcount : locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaInputs" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (ha : locals.get? "allocationEnd" = some (.int (Int.ofNat allocation)))
    (hlen : requests.length = n) (hexpected : expected.length = n)
    (hviews : ∀ k < n, AttestRowView schemas rows expected counts values k) :
    ((∃ k < n, rows[k]? = some (.array [])) ∧
      ExecStmt config ⟨C, locals, imms⟩ evm
        (.for [.letDecl "i" (some uint256) (.intLit 0)] attestOuterCond attestOuterPost
            attestOuterBody)
        .reverted) ∨
    ((∀ k < n, rows[k]? ≠ some (.array [])) ∧
      ∃ result, ExecStmt config ⟨C, locals, imms⟩ evm
        (.for [.letDecl "i" (some uint256) (.intLit 0)] attestOuterCond attestOuterPost
            attestOuterBody)
        (.ok ⟨C, result, imms⟩ evm) ∧ result.get? "multiRequests" = some (.array expected) ∧
        result.get? "allocationEnd" =
          some (.int (Int.ofNat (attestAllocationEnd allocation counts 0 n))) ∧
        ∀ name, attestOuterUntouched name → result.get? name = locals.get? name) := by
  have hinit : ExecBlock config ⟨C, locals, imms⟩ evm [.letDecl "i" (some uint256) (.intLit 0)]
      (.ok ⟨C, locals.insert "i" (.int 0), imms⟩ evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil
  have hrun := attestOuterRun (C := C) (imms := imms) (evm := evm)
    (locals := locals.insert "i" (.int 0)) (schemas := schemas) (rows := rows)
    (requests := requests) (expected := expected) (i := 0) (remaining := n)
    hn (by omega) (by simp)
    (by simpa [Std.HashMap.getElem?_insert] using hcount)
    (by simpa [Std.HashMap.getElem?_insert] using hs)
    (by simpa [Std.HashMap.getElem?_insert] using hr)
    (by simpa [Std.HashMap.getElem?_insert] using hq)
    (by simpa [Std.HashMap.getElem?_insert] using ha) hlen hexpected (by intro k hk; omega) hviews
  rcases hrun with ⟨⟨k, _, hk, hempty⟩, hrun⟩ | ⟨hgood, result, hrun, hrequests, haFinal, hsame⟩
  · exact .inl ⟨⟨k, hk, hempty⟩, ExecStmt.for hinit hrun⟩
  · refine .inr ⟨by intro k hk; exact hgood k (Nat.zero_le _) hk,
      result, ExecStmt.for hinit hrun, hrequests, haFinal, ?_⟩
    intro name hname
    rw [hsame name hname]
    simp [Std.HashMap.getElem?_insert, Ne.symm hname.2]

end Benchmarks.EAS.Attester
