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
        execChain, callFn, exitBlock, toRes, toUnit, toExec, toFn,
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


mutual

theorem evalExpr_complete {fr m e r} (h : EvalExpr cfg o fc fr m e r) :
    ∃ n, ∀ k, n ≤ k → (evalExpr cfg o fc k fr m e).run = some (toRes r) :=
  match h with
  | .lit p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]
  | .thisRef => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«local» p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]
  | .constVar p1 p2 p3 p4 p5 => by
    obtain ⟨n5, ih5⟩ := evalExpr_complete p5
    refine ⟨n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p3, p4, ih5 k' (by omega)]
  | .immutableVar p1 p2 p3 p4 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1, p2, p3, p4]
  | .stateVar p1 p2 p3 p4 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1, p2, p3, p4]
  | .envMember p1 p2 => by
    have hnd := envMember_not_data p2
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [directMember, hnd, p1, p2]
  | .msgData p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [directMember, isEnvObj, p1]
  | .enumMember p1 p2 p3 p4 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [directMember, p1, p2, p3, p4]
  | .typeMember p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [directMember, p1]
  | .memberField p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p2, p4, p5, ih3 k' (by omega)]
  | .memberStorageLength p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .memberStorageLengthPanic p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .memberMemField p1 p2 p3 p4 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p2, p4, ih3 k' (by omega)]
  | .memberMemLength p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .memberBalance (v := v) p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    cases v <;> simp [addrNat] at p3 <;> subst p3 <;> interp_simp [p1, addrNat, ih2 k' (by omega)]
  | .memberBytesLength p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .memberRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .indexStorage p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, p4, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexStoragePanic p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMem p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, p4, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMemRaw p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isRaw, p3, p4, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMemRawRevert p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isRaw, p3, p4, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMemPanic p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexBaseRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .indexRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .convert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .convertPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .convertRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .convertUser (c := c) p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n7, ih7⟩ := evalExpr_complete p7
    refine ⟨n7 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    have e7 := ih7 (k' + 1) (by omega)
    simp only [evalExpr] at e7
    have hconv : ((fc.var? c).isNone && ((fc.types.contractKind? c).isSome || (fc.types.enum? none c).isSome)) = true := by
      rcases p6 with h6 | h6 <;> simp [p3, h6]
    interp_simp [p1, p2, p4, p5, hconv, e7]
  | .structLit p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, p5, p7, ih6 k' (by omega)]
  | .structLitRevert p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, p5, ih6 k' (by omega)]
  | .structLitPanic p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, p5, p7, ih6 k' (by omega)]
  | .requireTrue p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .requireFalse p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .requireMsg p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p1, p4, ih2 k' (by omega), ih3 k' (by omega)]
  | .requireMsgRevert p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .requireCustom p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n4, ih4⟩ := evalExprs_complete p4
    refine ⟨n1 + n4 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isCustomError, isBuiltinFn, p2, p3, p5, p6, ih1 k' (by omega), ih4 k' (by omega)]
  | .requireCustomArgsRevert p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n4, ih4⟩ := evalExprs_complete p4
    refine ⟨n1 + n4 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isCustomError, isBuiltinFn, p2, p3, ih1 k' (by omega), ih4 k' (by omega)]
  | .requireCustomPanic p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n4, ih4⟩ := evalExprs_complete p4
    refine ⟨n1 + n4 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isCustomError, isBuiltinFn, p2, p3, p5, ih1 k' (by omega), ih4 k' (by omega)]
  | .requireCondRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .assertTrue p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .assertFalse p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .assertRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .revertEmpty => by
    refine ⟨3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [isBuiltinFn]
  | .revertMsg p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, ih1 k' (by omega)]
  | .revertMsgRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .keccak p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, ih1 k' (by omega)]
  | .keccakRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .ecrecover p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    have hb4 := callViaEVM_det p4
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, p3, hb4, ih1 k' (by omega)]
  | .ecrecoverFailed p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    have hb4 := callViaEVM_det p4
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, p3, hb4, ih1 k' (by omega)]
  | .ecrecoverAbiPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, ih1 k' (by omega)]
  | .ecrecoverArgsRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, ih1 k' (by omega)]
  | .gasleft => by
    refine ⟨3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [isBuiltinFn]
  | .addmod p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, p3, p4, p5, ih1 k' (by omega)]
  | .mulmod p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isBuiltinFn, p2, p3, p4, p5, ih1 k' (by omega)]
  | .modZero p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    rcases p5 with rfl | rfl <;> interp_simp [isBuiltinFn, p2, p3, p4, ih1 k' (by omega)]
  | .modArgsRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    rcases p1 with rfl | rfl <;> interp_simp [isBuiltinFn, ih2 k' (by omega)]
  | .abiEncode p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, ih1 k' (by omega)]
  | .abiEncodePacked p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, ih1 k' (by omega)]
  | .abiEncodeWithSelector p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, p6, ih1 k' (by omega)]
  | .abiEncodeWithSignature p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, p6, ih1 k' (by omega)]
  | .abiDecode p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, p6, ih1 k' (by omega)]
  | .abiDecodeFail p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, p2, p3, p4, p5, ih1 k' (by omega)]
  | .abiEncodeRevert (es := es) p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    rcases p1 with rfl | rfl | rfl | rfl <;> rcases es with _ | ⟨e, es⟩ <;>
      first | (cases p2; done) | interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, ih2 k' (by omega)]
  | .abiDecodeRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [isSuperExpr, headIdent, isEnvObj, isAbiFn, ih1 k' (by omega)]
  | .newArray p1 p2 p3 p4 p5 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p3, p4, p5, ih2 k' (by omega)]
  | .newArrayRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .newContract p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    refine ⟨n2 + n3 + n5 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p4, p6, hb7, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .newContractFailed p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    refine ⟨n2 + n3 + n5 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p4, p6, hb7, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .newContractAbiPanic p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n2 + n3 + n5 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p4, p6, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .newContractArgsRevert p1 p2 p3 p4 p5 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n2 + n3 + n5 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, p4, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .newContractSaltRevert p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    refine ⟨n2 + n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .newContractValueRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .internalCall p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    obtain ⟨n7, ih7⟩ := callFn_complete p7
    refine ⟨n5 + n7 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, p6, ih5 k' (by omega), ih7 k' (by omega)]
  | .internalCallRevert p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    obtain ⟨n7, ih7⟩ := callFn_complete p7
    refine ⟨n5 + n7 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, p6, ih5 k' (by omega), ih7 k' (by omega)]
  | .internalArgsRevert p1 p2 p3 p4 p5 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n5 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [p1, p2, p3, p4, ih5 k' (by omega)]
  | .superCall p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    obtain ⟨n4, ih4⟩ := callFn_complete p4
    refine ⟨n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, p1, p3, ih2 k' (by omega), ih4 k' (by omega)]
  | .superCallRevert p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    obtain ⟨n4, ih4⟩ := callFn_complete p4
    refine ⟨n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, p1, p3, ih2 k' (by omega), ih4 k' (by omega)]
  | .superArgsRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, p1, ih2 k' (by omega)]
  | .libraryCall p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    obtain ⟨n7, ih7⟩ := callFn_complete p7
    refine ⟨n5 + n7 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, p1, p2, p3, p4, p6, ih5 k' (by omega), ih7 k' (by omega)]
  | .libraryCallRevert p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    obtain ⟨n7, ih7⟩ := callFn_complete p7
    refine ⟨n5 + n7 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, p1, p2, p3, p4, p6, ih5 k' (by omega), ih7 k' (by omega)]
  | .libraryArgsRevert p1 p2 p3 p4 p5 => by
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n5 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, p1, p2, p3, p4, ih5 k' (by omega)]
  | .baseCall p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    obtain ⟨n8, ih8⟩ := callFn_complete p8
    refine ⟨n6 + n8 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, baseRecv, p1, p2, p3, p4, p5, p7, ih6 k' (by omega), ih8 k' (by omega)]
  | .baseCallRevert p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    obtain ⟨n8, ih8⟩ := callFn_complete p8
    refine ⟨n6 + n8 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, baseRecv, p1, p2, p3, p4, p5, p7, ih6 k' (by omega), ih8 k' (by omega)]
  | .baseArgsRevert p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n6 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [isSuperExpr, headIdent, libraryRecv, baseRecv, p1, p2, p3, p4, p5, ih6 k' (by omega)]
  | .usingForCall p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    obtain ⟨n8, ih8⟩ := callFn_complete p8
    refine ⟨n2 + n6 + n8 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, p3, p4, p5, p7, ih2 k' (by omega), ih6 k' (by omega), ih8 k' (by omega)]
  | .usingForArgsRevert p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, p3, p4, p5, ih2 k' (by omega), ih6 k' (by omega)]
  | .usingForCallRevert p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    obtain ⟨n8, ih8⟩ := callFn_complete p8
    refine ⟨n2 + n6 + n8 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, p3, p4, p5, p7, ih2 k' (by omega), ih6 k' (by omega), ih8 k' (by omega)]
  | .push1 p1 p2 p3 p4 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p4, ih2 k' (by omega), ih3 k' (by omega)]
  | .push1Revert p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .push1Panic p1 p2 p3 p4 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p4, ih2 k' (by omega), ih3 k' (by omega)]
  | .push0 p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p3, ih2 k' (by omega)]
  | .push0Panic p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p3, ih2 k' (by omega)]
  | .pop p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p3, ih2 k' (by omega)]
  | .popPanic p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p3, ih2 k' (by omega)]
  | .externalCall p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .externalCallNoCode p1 p2 p3 p4 p5 p6 p7 p8 p9 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p5, p7, p8, p9, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .externalCallFailed p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .externalCallDecodeFail p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .externalValueRevert p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    refine ⟨n2 + n3 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .externalGasRevert p1 p2 p3 p4 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    refine ⟨n2 + n3 + n4 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .externalArgsRevert p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, p1, p5, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .externalAbiPanic p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p10
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [specialMemberCall, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .lowLevelCall (rv := rv) p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n6, ih6⟩ := evalValueOpt_complete p6
    obtain ⟨n7, ih7⟩ := evalGasOpt_complete p7
    obtain ⟨n8, ih8⟩ := evalExpr_complete p8
    have hb10 := callViaEVM_det p10
    refine ⟨n3 + n6 + n7 + n8 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p4 p5
    subst p5
    have hsc : ("staticcall" == "call") = false := by decide
    rcases p1 with rfl | rfl <;> simp only [beq_self_eq_true, hsc, Bool.true_and, Bool.false_and] at hb10 <;>
      interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p2, p9, hb10, p11, hsc, ih3 k' (by omega),
        ih6 k' (by omega), ih7 k' (by omega), ih8 k' (by omega)]
  | .lowLevelValueRevert (rv := rv) p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n6, ih6⟩ := evalValueOpt_complete p6
    refine ⟨n3 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p4 p5
    subst p5
    have hsc : ("staticcall" == "call") = false := by decide
    rcases p1 with rfl | rfl <;>
      interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p2, hsc, ih3 k' (by omega), ih6 k' (by omega)]
  | .lowLevelGasRevert (rv := rv) p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n6, ih6⟩ := evalValueOpt_complete p6
    obtain ⟨n7, ih7⟩ := evalGasOpt_complete p7
    refine ⟨n3 + n6 + n7 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p4 p5
    subst p5
    have hsc : ("staticcall" == "call") = false := by decide
    rcases p1 with rfl | rfl <;>
      interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p2, hsc, ih3 k' (by omega), ih6 k' (by omega),
        ih7 k' (by omega)]
  | .lowLevelDataRevert (rv := rv) p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n6, ih6⟩ := evalValueOpt_complete p6
    obtain ⟨n7, ih7⟩ := evalGasOpt_complete p7
    obtain ⟨n8, ih8⟩ := evalExpr_complete p8
    refine ⟨n3 + n6 + n7 + n8 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p4 p5
    subst p5
    have hsc : ("staticcall" == "call") = false := by decide
    rcases p1 with rfl | rfl <;>
      interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p2, hsc, ih3 k' (by omega), ih6 k' (by omega),
        ih7 k' (by omega), ih8 k' (by omega)]
  | .delegateCall (rv := rv) p1 p2 p3 p4 p5 p6 p7 p8 p9 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalGasOpt_complete p5
    obtain ⟨n6, ih6⟩ := evalExpr_complete p6
    have hb8 := delegateCallViaEVM_det p8
    refine ⟨n2 + n5 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, p7, hb8, p9, ih2 k' (by omega), ih5 k' (by omega),
      ih6 k' (by omega)]
  | .delegateCallGasRevert (rv := rv) p1 p2 p3 p4 p5 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalGasOpt_complete p5
    refine ⟨n2 + n5 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, ih2 k' (by omega), ih5 k' (by omega)]
  | .delegateCallDataRevert (rv := rv) p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalGasOpt_complete p5
    obtain ⟨n6, ih6⟩ := evalExpr_complete p6
    refine ⟨n2 + n5 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, ih2 k' (by omega), ih5 k' (by omega),
      ih6 k' (by omega)]
  | .transfer (rv := rv) p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalExpr_complete p5
    have hb7 := callViaEVM_det p7
    refine ⟨n2 + n5 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, p6, hb7, ih2 k' (by omega), ih5 k' (by omega)]
  | .transferFailed (rv := rv) p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalExpr_complete p5
    have hb7 := callViaEVM_det p7
    refine ⟨n2 + n5 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, p6, hb7, ih2 k' (by omega), ih5 k' (by omega)]
  | .send (rv := rv) p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n5, ih5⟩ := evalExpr_complete p5
    have hb7 := callViaEVM_det p7
    refine ⟨n2 + n5 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p3 p4
    subst p4
    interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p1, p6, hb7, ih2 k' (by omega), ih5 k' (by omega)]
  | .transferAmtRevert (rv := rv) p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3⟩ := memberCallDirect_false p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n6, ih6⟩ := evalExpr_complete p6
    refine ⟨n3 + n6 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    cases rv <;> simp [addrNat, isContractValue] at p4 p5
    subst p5
    rcases p1 with rfl | rfl <;>
      interp_simp [specialMemberCall, addrNat, hmd1, hmd2, hmd3, p2, ih3 k' (by omega), ih6 k' (by omega)]
  | .callRecvRevert p1 p2 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 3, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 3) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega)]
  | .unary p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, p3, p4, ih1 k' (by omega)]
  | .unaryPanic p1 p2 p3 p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, p3, p4, ih1 k' (by omega)]
  | .unaryRevert p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, p3, ih1 k' (by omega)]
  | .incDec p1 p2 p3 p4 p5 => by
    obtain ⟨n2, ih2⟩ := evalLValue_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, p4, p5, ih2 k' (by omega)]
  | .incDecPanic p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalLValue_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, p4, ih2 k' (by omega)]
  | .incDecReadPanic p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalLValue_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .incDecAssignPanic p1 p2 p3 p4 p5 => by
    obtain ⟨n2, ih2⟩ := evalLValue_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, p4, p5, ih2 k' (by omega)]
  | .incDecRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalLValue_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .deleteLocal p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isIncDec, p2, p3, ih1 k' (by omega)]
  | .deleteStorage p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isIncDec, p2, ih1 k' (by omega)]
  | .deleteStoragePanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isIncDec, p2, ih1 k' (by omega)]
  | .deleteRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isIncDec, ih1 k' (by omega)]
  | .andShort p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .andFull p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .orShort p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .orFull p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .andLeftRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .andRightRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .orLeftRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .orRightRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .binary p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalExpr_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, ih3 k' (by omega), ih4 k' (by omega)]
  | .binaryPanic p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalExpr_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, ih3 k' (by omega), ih4 k' (by omega)]
  | .binaryRightRevert p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .binaryLeftRevert p1 p2 p3 p4 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalExpr_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega), ih4 k' (by omega)]
  | .condT p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .condF p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .condRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .assignPlain p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalLValue_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, ih2 k' (by omega), ih3 k' (by omega)]
  | .assignTuple p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := assignTuple_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isTupleExpr, ih1 k' (by omega), ih2 k' (by omega)]
  | .assignTupleRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := assignTuple_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [isTupleExpr, ih1 k' (by omega), ih2 k' (by omega)]
  | .assignPanic p1 p2 p3 p4 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalLValue_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, ih2 k' (by omega), ih3 k' (by omega)]
  | .assignCompound p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalLValue_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, p6, p7, ih3 k' (by omega), ih4 k' (by omega)]
  | .assignCompoundPanic p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalLValue_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, p6, ih3 k' (by omega), ih4 k' (by omega)]
  | .assignCompoundReadPanic p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalLValue_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, ih3 k' (by omega), ih4 k' (by omega)]
  | .assignCompoundAssignPanic p1 p2 p3 p4 p5 p6 p7 => by
    obtain ⟨n3, ih3⟩ := evalExpr_complete p3
    obtain ⟨n4, ih4⟩ := evalLValue_complete p4
    refine ⟨n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p5, p6, p7, ih3 k' (by omega), ih4 k' (by omega)]
  | .assignRhsRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .assignLhsRevert p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalLValue_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .tuple p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .tupleRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega)]
  | .arrayLit p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .arrayLitPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .arrayLitRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExprs_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]

theorem evalValueOpt_complete {fr m e r} (h : EvalValueOpt cfg o fc fr m e r) :
    ∃ n, ∀ k, n ≤ k → (evalValueOpt cfg o fc k fr m e).run = some (toRes r) :=
  match h with
  | .«none» => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«some» p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .revert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]

theorem evalGasOpt_complete {fr m e r} (h : EvalGasOpt cfg o fc fr m e r) :
    ∃ n, ∀ k, n ≤ k → (evalGasOpt cfg o fc k fr m e).run = some (toRes r) :=
  match h with
  | .«none» => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«some» p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .revert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]

theorem evalSaltOpt_complete {fr m e r} (h : EvalSaltOpt cfg o fc fr m e r) :
    ∃ n, ∀ k, n ≤ k → (evalSaltOpt cfg o fc k fr m e).run = some (toRes r) :=
  match h with
  | .«none» => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«some» p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .revert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]

theorem evalExprs_complete {fr m es r} (h : EvalExprs cfg o fc fr m es r) :
    ∃ n, ∀ k, n ≤ k → (evalExprs cfg o fc k fr m es).run = some (toRes r) :=
  match h with
  | .nil => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .cons p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .headRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .tailRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExprs_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]

theorem evalLValue_complete {fr m e r} (h : EvalLValue cfg o fc fr m e r) :
    ∃ n, ∀ k, n ≤ k → (evalLValue cfg o fc k fr m e).run = some (toRes r) :=
  match h with
  | .«local» p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]
  | .stateVar p1 p2 p3 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1, p2, p3]
  | .immutableVar p1 p2 p3 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1, p2, p3]
  | .memberStorage p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .memberMem p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .memberRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .indexStorage p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexStoragePanic p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMem p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, p4, p5, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexMemPanic (n := n) (len := len) p1 p2 p3 p4 p5 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    have hnl : ¬ n < len := not_lt.mpr p5
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p3, p4, hnl, ih1 k' (by omega), ih2 k' (by omega)]
  | .indexBaseRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .indexRevert p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]

theorem assignTuple_complete {fr m ls vs r} (h : AssignTuple cfg o fc fr m ls vs r) :
    ∃ n, ∀ k, n ≤ k → (assignTuple cfg o fc k fr m ls vs).run = some (toUnit r) :=
  match h with
  | .nil => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«skip» p1 => by
    obtain ⟨n1, ih1⟩ := assignTuple_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .cons p1 p2 p3 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    obtain ⟨n3, ih3⟩ := assignTuple_complete p3
    refine ⟨n1 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega), ih3 k' (by omega)]
  | .revert p1 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .assignPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalLValue_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]

theorem execStmt_complete {fr m s r} (h : ExecStmt cfg o fc fr m s r) :
    ∃ n, ∀ k, n ≤ k → (execStmt cfg o fc k fr m s).run = some (toExec r) :=
  match h with
  | .block (r := rr) p1 => by
    obtain ⟨n1, ih1⟩ := execBlock_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, ih1 k' (by omega)]
  | .varDeclNone p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]
  | .varDecl p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .varDeclRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .varDeclNonePanic p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]
  | .varDeclPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p2, ih1 k' (by omega)]
  | .tupleDecl p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := declareTuple_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .tupleDeclRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .tupleDeclPanic p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := declareTuple_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .exprStmt p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .exprStmtRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .iteT p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .iteF p1 p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .iteFNone p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .iteRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .«while» p1 => by
    obtain ⟨n1, ih1⟩ := execLoop_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .doWhile p1 p2 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    obtain ⟨n2, ih2⟩ := execLoop_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .doWhileContinue p1 p2 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    obtain ⟨n2, ih2⟩ := execLoop_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .doWhileBreak p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .doWhileReturn p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .doWhileRevert p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .forNoInit p1 => by
    obtain ⟨n1, ih1⟩ := execLoop_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .forInit (r := rr) p1 p2 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    obtain ⟨n2, ih2⟩ := execLoop_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, ih1 k' (by omega), ih2 k' (by omega)]
  | .forInitRevert p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .«break» => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«continue» => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .returnNone => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .returnSingle p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .returnMulti p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := assignTuple_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    rcases hrv : fr.retVars with _ | ⟨r1, _ | ⟨r2, rs⟩⟩
    · simp [hrv] at p1
    · simp [hrv] at p1
    · rw [hrv] at ih3
      have hlen : (r1 :: r2 :: rs).length ≥ 2 := by simp
      interp_simp [hrv, hlen, ih2 k' (by omega), ih3 k' (by omega)]
  | .returnRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .returnSinglePanic p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p3, ih2 k' (by omega)]
  | .returnMultiRevert p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := assignTuple_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    rcases hrv : fr.retVars with _ | ⟨r1, _ | ⟨r2, rs⟩⟩
    · simp [hrv] at p1
    · simp [hrv] at p1
    · rw [hrv] at ih3
      have hlen : (r1 :: r2 :: rs).length ≥ 2 := by simp
      interp_simp [hrv, hlen, ih2 k' (by omega), ih3 k' (by omega)]
  | .emit p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p4, p5, ih3 k' (by omega)]
  | .emitRevert p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .emitPanic p1 p2 p3 p4 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p4, ih3 k' (by omega)]
  | .revertError p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p4, p5, ih3 k' (by omega)]
  | .revertErrorArgsRevert p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .revertErrorPanic p1 p2 p3 p4 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p4, ih3 k' (by omega)]
  | .unchecked (r := rr) p1 => by
    obtain ⟨n1, ih1⟩ := execBlock_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, restoreUnchecked, ih1 k' (by omega)]
  | .placeholder (r := rr) (r' := r') p1 p2 => by
    obtain ⟨n1, ih1⟩ := execChain_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> simp [settlePlaceholder] at p2 <;> (try subst p2) <;> interp_simp [settlePlaceholder, ih1 k' (by omega)]
  | .tryCallOk (r := rr) p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    obtain ⟨n15, ih15⟩ := execBlock_complete p15
    refine ⟨n2 + n3 + n4 + n6 + n15 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, p14, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega), ih15 k' (by omega)]
  | .tryCallBindPanic p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, p14, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallDecodeFail p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallCaught (r := rr) p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    obtain ⟨n15, ih15⟩ := execBlock_complete p15
    refine ⟨n2 + n3 + n4 + n6 + n15 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, p14, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega), ih15 k' (by omega)]
  | .tryCallCaughtBindPanic p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, p14, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallUncaught p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p11
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    have hb12 := callViaEVM_det p12
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, p11, hb12, p13, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallNoCode p1 p2 p3 p4 p5 p6 p7 p8 p9 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, p5, p7, p8, p9, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallAbiPanic p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    have hnc := noCode_false p10
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, hnc, p1, p5, p7, p8, p9, p10, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallArgsRevert p1 p2 p3 p4 p5 p6 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    obtain ⟨n6, ih6⟩ := evalExprs_complete p6
    refine ⟨n2 + n3 + n4 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, p5, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega), ih6 k' (by omega)]
  | .tryCallGasRevert p1 p2 p3 p4 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    obtain ⟨n4, ih4⟩ := evalGasOpt_complete p4
    refine ⟨n2 + n3 + n4 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .tryCallValueRevert p1 p2 p3 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    obtain ⟨n3, ih3⟩ := evalValueOpt_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .tryCallRecvRevert p1 p2 => by
    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p1
    obtain ⟨n2, ih2⟩ := evalExpr_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [hmd1, hmd2, hmd3, hmd4, p1, ih2 k' (by omega)]
  | .tryNewOk (r := rr) p1 p2 p3 p4 p5 p6 p7 p8 p9 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    obtain ⟨n9, ih9⟩ := execBlock_complete p9
    refine ⟨n2 + n3 + n5 + n9 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, p1, p4, p6, hb7, p8, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega), ih9 k' (by omega)]
  | .tryNewBindPanic p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    refine ⟨n2 + n3 + n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, p6, hb7, p8, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .tryNewCaught (r := rr) p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    obtain ⟨n10, ih10⟩ := execBlock_complete p10
    refine ⟨n2 + n3 + n5 + n10 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [exitBlock, p1, p4, p6, hb7, p8, p9, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega), ih10 k' (by omega)]
  | .tryNewCaughtBindPanic p1 p2 p3 p4 p5 p6 p7 p8 p9 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    refine ⟨n2 + n3 + n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, p6, hb7, p8, p9, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .tryNewUncaught p1 p2 p3 p4 p5 p6 p7 p8 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    have hb7 := newViaEVM_det p7
    refine ⟨n2 + n3 + n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, p6, hb7, p8, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .tryNewAbiPanic p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n2 + n3 + n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, p6, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .tryNewArgsRevert p1 p2 p3 p4 p5 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    obtain ⟨n5, ih5⟩ := evalExprs_complete p5
    refine ⟨n2 + n3 + n5 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p4, ih2 k' (by omega), ih3 k' (by omega), ih5 k' (by omega)]
  | .tryNewSaltRevert p1 p2 p3 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    obtain ⟨n3, ih3⟩ := evalSaltOpt_complete p3
    refine ⟨n2 + n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega), ih3 k' (by omega)]
  | .tryNewValueRevert p1 p2 => by
    obtain ⟨n2, ih2⟩ := evalValueOpt_complete p2
    refine ⟨n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, ih2 k' (by omega)]

theorem declareTuple_complete {fr m bs vs r} (h : DeclareTuple cfg o fc fr m bs vs r) :
    ∃ n, ∀ k, n ≤ k → (declareTuple cfg o fc k fr m bs vs).run = some (toUnit r) :=
  match h with
  | .nil => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .«skip» p1 => by
    obtain ⟨n1, ih1⟩ := declareTuple_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .cons p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := declareTuple_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .panic p1 p2 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1, p2]

theorem execLoop_complete {fr m c post body r} (h : ExecLoop cfg o fc fr m c post body r) :
    ∃ n, ∀ k, n ≤ k → (execLoop cfg o fc k fr m c post body).run = some (toExec r) :=
  match h with
  | .condFalse p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .condRevert p1 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .iterate .none p2 .none p4 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih4 k' (by omega)]
  | .iterate .none p2 (.some hp3) p4 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n2 + n3 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .iterate (.some hp1) p2 .none p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n1 + n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih4 k' (by omega)]
  | .iterate (.some hp1) p2 (.some hp3) p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n1 + n2 + n3 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .iterateContinue .none p2 .none p4 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih4 k' (by omega)]
  | .iterateContinue .none p2 (.some hp3) p4 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n2 + n3 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .iterateContinue (.some hp1) p2 .none p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n1 + n2 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih4 k' (by omega)]
  | .iterateContinue (.some hp1) p2 (.some hp3) p4 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    obtain ⟨n4, ih4⟩ := execLoop_complete p4
    refine ⟨n1 + n2 + n3 + n4 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih3 k' (by omega), ih4 k' (by omega)]
  | .postRevert .none p2 (.revert hp3) => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    refine ⟨n2 + n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih3 k' (by omega)]
  | .postRevert (.some hp1) p2 (.revert hp3) => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    refine ⟨n1 + n2 + n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih3 k' (by omega)]
  | .postRevertContinue .none p2 (.revert hp3) => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    refine ⟨n2 + n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega), ih3 k' (by omega)]
  | .postRevertContinue (.some hp1) p2 (.revert hp3) => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    obtain ⟨n3, ih3⟩ := evalExpr_complete hp3
    refine ⟨n1 + n2 + n3 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega), ih3 k' (by omega)]
  | .breakOut .none p2 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega)]
  | .breakOut (.some hp1) p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n1 + n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega)]
  | .returnOut .none p2 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega)]
  | .returnOut (.some hp1) p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n1 + n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega)]
  | .bodyRevert .none p2 => by
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    interp_simp [ih2 k' (by omega)]
  | .bodyRevert (.some hp1) p2 => by
    obtain ⟨n1, ih1⟩ := evalExpr_complete hp1
    obtain ⟨n2, ih2⟩ := execStmt_complete p2
    refine ⟨n1 + n2 + 2, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 2) (by omega)
    simp only [execLoop, IM.run_bind, toRes, ih1 (k' + 1) (by omega)]
    interp_simp [ih2 k' (by omega)]

theorem execBlock_complete {fr m ss r} (h : ExecBlock cfg o fc fr m ss r) :
    ∃ n, ∀ k, n ≤ k → (execBlock cfg o fc k fr m ss).run = some (toExec r) :=
  match h with
  | .nil => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp
  | .cons p1 p2 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    obtain ⟨n2, ih2⟩ := execBlock_complete p2
    refine ⟨n1 + n2 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega), ih2 k' (by omega)]
  | .consReturn p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .consBreak p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .consContinue p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .consRevert p1 => by
    obtain ⟨n1, ih1⟩ := execStmt_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]

theorem execChain_complete {fr m mods body r} (h : ExecChain cfg o fc fr m mods body r) :
    ∃ n, ∀ k, n ≤ k → (execChain cfg o fc k fr m mods body).run = some (toExec r) :=
  match h with
  | .body p1 => by
    obtain ⟨n1, ih1⟩ := execBlock_complete p1
    refine ⟨n1 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [ih1 k' (by omega)]
  | .modifier (r := rr) p1 p2 p3 p4 p5 p6 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    obtain ⟨n6, ih6⟩ := execBlock_complete p6
    refine ⟨n3 + n6 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr <;> interp_simp [popScope, p1, p2, p4, p5, ih3 k' (by omega), ih6 k' (by omega)]
  | .modifierArgsRevert p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .modifierPanic p1 p2 p3 p4 => by
    obtain ⟨n3, ih3⟩ := evalExprs_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, p4, ih3 k' (by omega)]
  | .skipBase p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := execChain_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]

theorem callFn_complete {fr m fn args r} (h : CallFn cfg o fc fr m fn args r) :
    ∃ n, ∀ k, n ≤ k → (callFn cfg o fc k fr m fn args).run = some (toFn r) :=
  match h with
  | .ok (r := rr) p1 p2 p3 p4 p5 => by
    obtain ⟨n3, ih3⟩ := execChain_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    cases rr with
    | normal fr' m' => interp_simp [p1, p2, p4, p5, ih3 k' (by omega)]
    | returned fr' m' => interp_simp [p1, p2, p4, p5, ih3 k' (by omega)]
    | «break» fr' m' => simp [finished] at p4
    | «continue» fr' m' => simp [finished] at p4
    | reverted d => simp [finished] at p4
  | .reverted p1 p2 p3 => by
    obtain ⟨n3, ih3⟩ := execChain_complete p3
    refine ⟨n3 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := 1) (by omega)
    interp_simp [p1, p2, ih3 k' (by omega)]
  | .enterPanic p1 => by
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_add hk
    interp_simp [p1]

end

end Solidity
