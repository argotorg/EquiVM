import Benchmarks.EAS.Attester.MultiRevokeSourceRow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def RevokeRowView (schemas rows expected : List Value) (i : Nat) : Prop :=
  ∃ schema uids, schemas[i]? = some schema ∧ rows[i]? = some (.array uids) ∧
    expected[i]? = some (.tuple [schema, .array (revokePairValues uids)]) ∧
    uids.length < UInt256.size ∧ normalizeRawBoolWord? schema = .ok schema ∧
    ∀ v ∈ uids, normalizeRawBoolWord? v = .ok v

def revokeOuterUntouched (name : Ident) : Prop := revokeRowUntouched name ∧ name ≠ "i"

theorem revokeOuterRun {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests expected : List Value} {i remaining n : Nat}
    (hn : n < UInt256.size) (hi : i + remaining = n)
    (hindex : locals.get? "i" = some (.int (Int.ofNat i)))
    (hcount : locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaUids" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (hlen : requests.length = n) (hexpected : expected.length = n)
    (hfilled : ∀ k < i, requests[k]? = expected[k]?)
    (hviews : ∀ k < n, RevokeRowView schemas rows expected k) :
    ((∃ k, i ≤ k ∧ k < n ∧ rows[k]? = some (.array [])) ∧
      ExecForLoop cfg ⟨C, locals, imms⟩ evm revokeOuterCond revokeOuterPost revokeOuterBody
          .reverted) ∨
    ((∀ k, i ≤ k → k < n → rows[k]? ≠ some (.array [])) ∧
      ∃ result, ExecForLoop cfg ⟨C, locals, imms⟩ evm revokeOuterCond revokeOuterPost
          revokeOuterBody
        (.ok ⟨C, result, imms⟩ evm) ∧ result.get? "multiRequests" = some (.array expected) ∧
        ∀ name, revokeOuterUntouched name → result.get? name = locals.get? name) := by
  induction remaining generalizing locals requests i with
  | zero =>
      have hin : i = n := by omega
      have hrequests : requests = expected := by
        apply List.ext_getElem (hlen.trans hexpected.symm)
        intro k hk hk'
        have he := hfilled k (by omega)
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.some.injEq] at he
        exact he
      refine .inr ⟨by intro k hk hk'; omega, locals, ExecForLoop.falseDone ?_,
        by simpa only [hrequests] using hq, by intro name _; rfl⟩
      simpa only [revokeOuterCond, hin, Nat.lt_irrefl, decide_false] using
        (evalLocalNatLt (cfg := cfg) (solm := ⟨C, locals, imms⟩) (evm := evm) hindex hcount)
  | succ remaining ih =>
      have hin : i < n := by omega
      have hcond : evalExpr? cfg ⟨C, locals, imms⟩ evm revokeOuterCond = .ok (.bool true) := by
        simpa only [revokeOuterCond, hin, decide_true] using
          (evalLocalNatLt (cfg := cfg) (solm := ⟨C, locals, imms⟩) (evm := evm) hindex hcount)
      obtain ⟨schema, uids, hsch, hrow, hexp, hfit, hsnormal, hunormal⟩ := hviews i hin
      by_cases hempty : uids = []
      · subst uids
        exact .inl ⟨⟨i, le_refl _, hin, hrow⟩,
          ExecForLoop.bodyRevert hcond (revokeSourceRowEmpty hindex hr hrow)⟩
      · have hpos : 0 < uids.length := List.length_pos_iff.mpr hempty
        obtain ⟨l1, hbody, hrequests, hsame⟩ := revokeSourceRow
          (cfg := cfg) (C := C) (imms := imms) (evm := evm)
          hindex hs hr hq hrow hsch (by omega) hpos hfit hsnormal hunormal
        have hi1 : l1.get? "i" = some (.int (Int.ofNat i)) :=
          (hsame "i" (by simp [revokeRowUntouched])).trans hindex
        let l2 := l1.insert "i" (.int (Int.ofNat (i + 1)))
        have hpost : ExecBlock cfg ⟨C, l1, imms⟩ evm revokeOuterPost
            (.ok ⟨C, l2, imms⟩ evm) := execLocalIncrement hi1 (by omega)
        have hpreserved (name : Ident) (hname : revokeOuterUntouched name) :
            l2.get? name = locals.get? name := by
          have hh := hsame name hname.1
          simpa only [l2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr (Ne.symm hname.2), Bool.false_eq_true, if_false] using hh
        have hfilled' : ∀ k < i + 1,
            (requests.set i (.tuple [schema, .array (revokePairValues uids)]))[k]? = expected[k]? :=
                by
          intro k hk
          by_cases hki : k = i
          · subst k
            rw [List.getElem?_set_self (by omega), hexp]
          · rw [List.getElem?_set_ne (Ne.symm hki)]
            exact hfilled k (by omega)
        have hrun := ih (locals := l2)
          (requests := requests.set i (.tuple [schema, .array (revokePairValues uids)]))
          (i := i + 1) (by omega) (by simp [l2])
          ((hpreserved "schemaLength" (by simp [revokeOuterUntouched,
              revokeRowUntouched])).trans hcount)
          ((hpreserved "schemas" (by simp [revokeOuterUntouched, revokeRowUntouched])).trans hs)
          ((hpreserved "schemaUids" (by simp [revokeOuterUntouched, revokeRowUntouched])).trans hr)
          (by simpa [l2, Std.HashMap.getElem?_insert] using hrequests)
          (by simpa using hlen) hfilled'
        rcases hrun with ⟨hbad, hrun⟩ | ⟨hgood, result, hrun, hfinal, hsameFinal⟩
        · obtain ⟨k, hk, hk', hrowk⟩ := hbad
          exact .inl ⟨⟨k, by omega, hk', hrowk⟩, ExecForLoop.iterate hcond hbody hpost hrun⟩
        · refine .inr ⟨?_, result, ExecForLoop.iterate hcond hbody hpost hrun, hfinal, ?_⟩
          · intro k hk hk'
            by_cases hki : k = i
            · subst k
              rw [hrow]
              simpa only [ne_eq, Option.some.injEq, Value.array.injEq] using hempty
            · exact hgood k (by omega) hk'
          · intro name hname
            exact (hsameFinal name hname).trans (hpreserved name hname)

theorem revokeOuterFor {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests expected : List Value} {n : Nat}
    (hn : n < UInt256.size)
    (hcount : locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaUids" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (hlen : requests.length = n) (hexpected : expected.length = n)
    (hviews : ∀ k < n, RevokeRowView schemas rows expected k) :
    ((∃ k < n, rows[k]? = some (.array [])) ∧
      ExecStmt cfg ⟨C, locals, imms⟩ evm
        (.for [.letDecl "i" (some uint256) (.intLit 0)] revokeOuterCond revokeOuterPost
            revokeOuterBody)
        .reverted) ∨
    ((∀ k < n, rows[k]? ≠ some (.array [])) ∧
      ∃ result, ExecStmt cfg ⟨C, locals, imms⟩ evm
        (.for [.letDecl "i" (some uint256) (.intLit 0)] revokeOuterCond revokeOuterPost
            revokeOuterBody)
        (.ok ⟨C, result, imms⟩ evm) ∧ result.get? "multiRequests" = some (.array expected) ∧
        ∀ name, revokeOuterUntouched name → result.get? name = locals.get? name) := by
  have hinit : ExecBlock cfg ⟨C, locals, imms⟩ evm [.letDecl "i" (some uint256) (.intLit 0)]
      (.ok ⟨C, locals.insert "i" (.int 0), imms⟩ evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil
  have hrun := revokeOuterRun (cfg := cfg) (C := C) (imms := imms) (evm := evm)
    (locals := locals.insert "i" (.int 0)) (schemas := schemas) (rows := rows)
    (requests := requests) (expected := expected) (i := 0) (remaining := n)
    hn (by omega) (by simp)
    (by simpa [Std.HashMap.getElem?_insert] using hcount)
    (by simpa [Std.HashMap.getElem?_insert] using hs)
    (by simpa [Std.HashMap.getElem?_insert] using hr)
    (by simpa [Std.HashMap.getElem?_insert] using hq) hlen hexpected (by intro k hk; omega) hviews
  rcases hrun with ⟨⟨k, _, hk, hempty⟩, hrun⟩ | ⟨hgood, result, hrun, hrequests, hsame⟩
  · exact .inl ⟨⟨k, hk, hempty⟩, ExecStmt.for hinit hrun⟩
  · refine .inr ⟨by intro k hk; exact hgood k (Nat.zero_le _) hk,
      result, ExecStmt.for hinit hrun, hrequests, ?_⟩
    intro name hname
    rw [hsame name hname]
    simp [Std.HashMap.getElem?_insert, Ne.symm hname.2]

end Benchmarks.EAS.Attester
