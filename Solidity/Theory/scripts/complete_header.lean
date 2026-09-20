import Solidity.Theory.InterpLemmas

/-!
# Completeness of the interpreter

Every derivation of the relational semantics is reproduced by the fuel-indexed interpreter for
all sufficiently large fuel.
-/

set_option maxErrors 500
set_option maxHeartbeats 2000000

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

/-! ## Conversions from relational results to interpreter results -/

def toRes {α} : Res α → Except ByteArray (α × Frame × Machine)
  | .ok a fr m => .ok (a, fr, m)
  | .reverted d => .error d

def toUnit : Res Unit → Except ByteArray (Frame × Machine)
  | .ok () fr m => .ok (fr, m)
  | .reverted d => .error d

def toExec : ExecResult → Except ByteArray ExecResult
  | .reverted d => .error d
  | r => .ok r

def toFn : FnResult → Except ByteArray (List Value × Machine)
  | .ok rets m => .ok (rets, m)
  | .reverted d => .error d

@[simp] theorem toRes_ok {α} (a : α) (fr : Frame) (m : Machine) : toRes (.ok a fr m) = .ok (a, fr, m) := rfl
@[simp] theorem toRes_reverted {α} (d : ByteArray) : (toRes (.reverted d) : Except ByteArray (α × Frame × Machine)) = .error d := rfl
@[simp] theorem toUnit_ok (fr : Frame) (m : Machine) : toUnit (.ok () fr m) = .ok (fr, m) := rfl
@[simp] theorem toUnit_reverted (d : ByteArray) : toUnit (.reverted d) = .error d := rfl
@[simp] theorem toExec_normal (fr : Frame) (m : Machine) : toExec (.normal fr m) = .ok (.normal fr m) := rfl
@[simp] theorem toExec_returned (fr : Frame) (m : Machine) : toExec (.returned fr m) = .ok (.returned fr m) := rfl
@[simp] theorem toExec_break (fr : Frame) (m : Machine) : toExec (.break fr m) = .ok (.break fr m) := rfl
@[simp] theorem toExec_continue (fr : Frame) (m : Machine) : toExec (.continue fr m) = .ok (.continue fr m) := rfl
@[simp] theorem toExec_reverted (d : ByteArray) : toExec (.reverted d) = .error d := rfl
@[simp] theorem toFn_ok (rets : List Value) (m : Machine) : toFn (.ok rets m) = .ok (rets, m) := rfl
@[simp] theorem toFn_reverted (d : ByteArray) : toFn (.reverted d) = .error d := rfl

/-! ## Determinism of the EVM bridges -/

theorem callViaEVM_det {o m t v cd perm gas res} (h : callViaEVM o m t v cd perm gas res) :
    Interp.callViaEVM o m t v cd perm gas = res := by
  cases h with
  | callMade hw hle hdepth hΘ =>
    subst hw
    dsimp only [Interp.callViaEVM]
    rw [if_pos ⟨hle, hdepth⟩, ← hΘ]
  | callNotMade hw hor =>
    subst hw
    dsimp only [Interp.callViaEVM]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases hor with h | h
    · exact absurd (show (EVM.Word.ofNat v).val ≤ ((m.evm.accountMap.find? m.this).getD default).balance.val from h1)
        (not_le.mpr h)
    · exact h2 h

theorem delegateCallViaEVM_det {o m t cd gas res} (h : delegateCallViaEVM o m t cd gas res) :
    Interp.delegateCallViaEVM o m t cd gas = res := by
  cases h with
  | callMade hdepth hΘ =>
    dsimp only [Interp.delegateCallViaEVM]
    rw [if_pos hdepth, ← hΘ]
  | callNotMade hdepth =>
    dsimp only [Interp.delegateCallViaEVM]
    rw [if_neg (by simpa using hdepth)]

theorem newViaEVM_det {cfg o m c v args salt res} (h : newViaEVM cfg o m c v args salt res) :
    Interp.newViaEVM cfg o m c v args salt = some res := by
  cases h with
  | created hcc hw hcr hle hdepth hnonce hsize hσ hΛ =>
    subst hw hcr hσ
    dsimp only [Interp.newViaEVM]
    rw [hcc]
    dsimp only
    rw [if_pos ⟨hle, hdepth, hnonce, hsize⟩, ← hΛ]
  | notCreated hcc hw hcr hor =>
    subst hw hcr
    dsimp only [Interp.newViaEVM]
    rw [hcc]
    dsimp only
    rw [if_neg]
    rintro ⟨h1, h2, h3, h4⟩
    rcases hor with h | h | h | h
    · exact absurd (show (EVM.Word.ofNat v).val ≤ ((m.evm.accountMap.find? m.this).getD default).balance.val from h1)
        (not_le.mpr h)
    · exact h2 h
    · exact absurd h3 (not_lt.mpr h)
    · exact absurd h4 (not_le.mpr h)

/-! ## The simp set that evaluates the interpreter -/

syntax "interp_simp" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| interp_simp) => `(tactic| interp_simp [])
  | `(tactic| interp_simp [$ls,*]) => `(tactic|
      simp +decide only [evalExpr, evalMember, evalCall, evalBuiltin, evalNamedCall, evalAbi, evalMemberCall,
        evalValueOpt, evalSaltOpt, evalGasOpt, evalExprs, evalLValue, assignTuple, declareTuple, execStmt, execLoop, execLoopBody, execBlock,
        execChain, evalMods, callFn, toRes, toUnit, toExec, toFn,
        IM.run_bind, IM.run_pure, IM.run_throw, IM.run_failure, liftOp_run, liftOpt_run, guard'_run,
        ite_true, ite_false, dite_true, dite_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
        Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
        beq_self_eq_true, bne_self_eq_false, beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false,
        decide_eq_true_eq, decide_eq_false_iff_not, Option.isNone_none, Option.isNone_some, Option.isSome_none,
        Option.isSome_some, List.isEmpty_nil, List.isEmpty_cons, eq_self_iff_true, ne_eq, not_false_eq_true,
        not_true_eq_false, Fin.toNat_eq_val, $ls,*])

theorem memberCallDirect_false {recv : Expr} (h : memberCallDirect fc fr recv = false) :
    isSuperExpr recv = false ∧ isEnvObj (headIdent recv) = false ∧ libraryRecv fc fr recv = false ∧
      baseRecv fc fr recv = false := by
  unfold memberCallDirect at h
  simp only [Bool.or_eq_false_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem envMember_not_data {m : Machine} {obj f : Ident} {v : Value} (h : envMember m obj f = some v) :
    (obj == "msg" && f == "data") = false := by
  by_cases h1 : obj = "msg" <;> by_cases h2 : f = "data" <;> simp [h1, h2]
  subst h1 h2
  simp [envMember] at h

theorem noCode_false {d : FnDecl} {evm : EVM.State} {a : EVM.Address} (h : d.returns = [] → codeSize evm a ≠ 0) :
    (d.returns.isEmpty && decide (codeSize evm a = 0)) = false := by
  cases hr : d.returns with
  | nil => simp [h hr]
  | cons x xs => simp

/-- `k = k' + c` for `k ≥ c`. -/
theorem exists_add {k c : Nat} (h : c ≤ k) : ∃ k', k = k' + c := ⟨k - c, by omega⟩

