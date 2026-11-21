import Stele.Interp.Sound

/-!
# Completeness of the executable semantics

Every derivation of the relational semantics of `Stele/Semantics/Exec.lean` is reached by the
interpreter of `Stele/Interp.lean` with enough fuel and the oracle that replays the derivation's own
witnesses (`scriptOracle`), unless the interpreter stops short at an allocation beyond
`allocationCap` (`Reaches`).  Static mode is exact: the ordinary rules require write permission
precisely where the interpreter halts with `staticViolation`, and the `*Static` rules are the
derivation's own result.  The relational semantics is the specification; nothing here changes it.
-/

namespace Stele.Interp

open ABI Ethereum Ethereum.EVM

/-! ## The script oracle -/

/-- A witness for one existential of the relation: a call's `Θ` result, a creation's `Lambda`
    result, or the word of `letGas`. -/
inductive Witness where
  | call : CallResult → Witness
  | create : CreateResult → Witness
  | gas : EVM.Word → Witness

/-- The oracle that answers from a script of witnesses, one per consultation.  A missing or
    mismatched witness is an error (the interpreter reports `stuck`), or zero for `gasleft()`. -/
def scriptOracle : Oracle (List Witness) where
  call := fun ω _ _ =>
    match ω with
    | .call res :: ω' => .ok (res, ω')
    | _ => .error "script: no call witness"
  create := fun ω _ _ =>
    match ω with
    | .create res :: ω' => .ok (res, ω')
    | _ => .error "script: no creation witness"
  gasLeft := fun ω _ =>
    match ω with
    | .gas w :: ω' => (w, ω')
    | _ => (⟨0⟩, ω)

/-! ## Reaching a result -/

/-- The run `p` reached `r` with its script consumed down to `rest`, or stopped short at an
    allocation beyond `allocationCap` (no result). -/
inductive Reaches : Outcome × List Witness → ExecResult → List Witness → Prop
  | hit : Reaches (.result r, rest) r rest
  | unsupported (why : String) (ω : List Witness) : Reaches (.unsupported why, ω) r rest

theorem Reaches.hit_or_short {p : Outcome × List Witness} {r : ExecResult} {rest : List Witness}
    (h : Reaches p r rest) :
    p = (.result r, rest) ∨ ∃ why ω, p = (.unsupported why, ω) := by
  cases h with
  | hit => exact .inl rfl
  | unsupported why ω => exact .inr ⟨why, ω, rfl⟩

theorem succ_of_le {n fuel : Nat} (h : n + 1 ≤ fuel) : ∃ k, fuel = k + 1 ∧ n ≤ k :=
  ⟨fuel - 1, by omega, by omega⟩

/-- A judgment is complete once one more unit of fuel than the bound `n` runs its step. -/
theorem complete_of_succ {run : Nat → List Witness → Outcome × List Witness} {r : ExecResult}
    (ω : List Witness) (n : Nat)
    (h : ∀ fuel, n ≤ fuel → ∀ rest, Reaches (run (fuel + 1) (ω ++ rest)) r rest) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest, Reaches (run fuel (ω ++ rest)) r rest := by
  refine ⟨ω, n + 1, fun fuel hf rest => ?_⟩
  obtain ⟨fuel, rfl, hn⟩ := succ_of_le hf
  exact h fuel hn rest

/-- A statement step past the allocation guard: an oversized allocation stops short. -/
theorem execStmt_guard {cfg : Config} {stele : Frame} {evm : EVM.State} {stmt : Stmt}
    {r : ExecResult} {fuel : Nat} {ω rest : List Witness}
    (h : oversizedAllocation cfg stele evm stmt = none →
      Reaches (execStmt (fuel + 1) scriptOracle ω cfg stele evm stmt) r rest) :
    Reaches (execStmt (fuel + 1) scriptOracle ω cfg stele evm stmt) r rest := by
  rcases hover : oversizedAllocation cfg stele evm stmt with _ | why
  · exact h hover
  · rw [execStmt]; simp only [hover]; exact .unsupported why ω

theorem stmt_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {stmt : Stmt}
    {r : ExecResult} (ω : List Witness) (n : Nat)
    (h : ∀ fuel, n ≤ fuel → ∀ rest, oversizedAllocation cfg stele evm stmt = none →
      Reaches (execStmt (fuel + 1) scriptOracle (ω ++ rest) cfg stele evm stmt) r rest) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execStmt fuel scriptOracle (ω ++ rest) cfg stele evm stmt) r rest :=
  complete_of_succ (run := fun fuel ω => execStmt fuel scriptOracle ω cfg stele evm stmt) ω n
    fun fuel hn rest => execStmt_guard (h fuel hn rest)

theorem loop_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {cond : Expr}
    {post body : List Stmt} {r : ExecResult} (ω : List Witness) (n : Nat)
    (h : ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execForLoop (fuel + 1) scriptOracle (ω ++ rest) cfg stele evm cond post body)
        r rest) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execForLoop fuel scriptOracle (ω ++ rest) cfg stele evm cond post body) r rest :=
  complete_of_succ
    (run := fun fuel ω => execForLoop fuel scriptOracle ω cfg stele evm cond post body) ω n h

theorem block_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {stmts : List Stmt}
    {r : ExecResult} (ω : List Witness) (n : Nat)
    (h : ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execBlock (fuel + 1) scriptOracle (ω ++ rest) cfg stele evm stmts) r rest) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execBlock fuel scriptOracle (ω ++ rest) cfg stele evm stmts) r rest :=
  complete_of_succ (run := fun fuel ω => execBlock fuel scriptOracle ω cfg stele evm stmts) ω n h

theorem body_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {body : List Stmt}
    {r : ExecResult} (ω : List Witness) (n : Nat)
    (h : ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execFuncBody (fuel + 1) scriptOracle (ω ++ rest) cfg stele evm body) r rest) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execFuncBody fuel scriptOracle (ω ++ rest) cfg stele evm body) r rest :=
  complete_of_succ (run := fun fuel ω => execFuncBody fuel scriptOracle ω cfg stele evm body)
    ω n h

/-- Unfold one step of the interpreter `f` and reduce it with the derivation's hypotheses.
    Scoped: `step` and `follow` must not become keywords in files importing this module. -/
scoped macro "step" f:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (rw [$f:ident]
             try simp only [List.append_assoc, List.cons_append, List.nil_append, $hs,*]))

/-- Follow the sub-run `h`: the interpreter's arm returns a short stop as it is, and the arm for
    the result reached is what remains (closed when it is the derivation's own result). -/
scoped macro "follow" h:term : tactic =>
  `(tactic| (rcases Reaches.hit_or_short $h with hb | ⟨_, _, hb⟩ <;>
      simp only [hb] <;>
      try first
        | exact Reaches.hit
        | exact Reaches.unsupported _ _))

/-! ## Call bridges -/

theorem callViaEVMRun_complete {evm : EVM.State} {target : EVM.Address} {value : Int}
    {calldata : ByteArray} {z : Bool} {evm' : EVM.State} {out : ByteArray} {perm : Bool}
    (h : callViaEVM evm target value calldata (z, evm', out) perm) :
    ∃ ω₀ : List Witness, ∀ ω,
      callViaEVMRun scriptOracle (ω₀ ++ ω) evm target value calldata perm =
        .ok ((z, evm', out), ω) := by
  rcases h with ⟨hvw, -, hevm', hle, hd⟩ | ⟨hA, hevm', hng⟩
  · rename_i valueWord σ' g' A'
    refine ⟨[.call ⟨z, σ', A', out⟩], fun ω => ?_⟩
    have hg : callMadeGuard evm value = true := by
      subst hvw
      simp only [callMadeGuard, decide_eq_true_eq]
      exact ⟨hle, hd⟩
    subst hevm'
    simp [callViaEVMRun, hg, scriptOracle]
  · refine ⟨[], fun ω => ?_⟩
    have hg : callMadeGuard evm value = false := by
      simp only [callMadeGuard, decide_eq_false_iff_not]
      exact hng
    subst hA hevm'
    simp [callViaEVMRun, hg, scriptOracle]

theorem delegateCallViaEVMRun_complete {evm : EVM.State} {target : EVM.Address}
    {calldata : ByteArray} {z : Bool} {evm' : EVM.State} {out : ByteArray}
    (h : delegateCallViaEVM evm target calldata (z, evm', out)) :
    ∃ ω₀ : List Witness, ∀ ω,
      delegateCallViaEVMRun scriptOracle (ω₀ ++ ω) evm target calldata =
        .ok ((z, evm', out), ω) := by
  rcases h with ⟨-, hevm', hd⟩ | ⟨hA, hevm', hd⟩
  · rename_i σ' g' A'
    refine ⟨[.call ⟨z, σ', A', out⟩], fun ω => ?_⟩
    subst hevm'
    simp [delegateCallViaEVMRun, hd, scriptOracle]
  · refine ⟨[], fun ω => ?_⟩
    subst hA hevm'
    simp [delegateCallViaEVMRun, hd, scriptOracle]

theorem typedCallViaEVMRun_complete {cfg : Config} {evm : EVM.State} {target : EVM.Address}
    {name : Ident} {value : Int} {args : List Value} {z : Bool} {evm' : EVM.State}
    {out : ByteArray} {perm : Bool}
    (h : typedCallViaEVM cfg evm target name value args (z, evm', out) perm) :
    ∃ ω₀ : List Witness, ∀ ω,
      typedCallViaEVMRun scriptOracle (ω₀ ++ ω) cfg evm target name value args perm =
        .ok ((z, evm', out), ω) := by
  obtain ⟨calldata, henc, hcall⟩ := h
  obtain ⟨ω₀, hrun⟩ := callViaEVMRun_complete hcall
  exact ⟨ω₀, fun ω => by simp [typedCallViaEVMRun, henc, hrun ω]⟩

theorem newViaEVMRun_complete {cfg : Config} {evm : EVM.State} {name : Ident} {value : Int}
    {args : List Value} {salt : Option ByteArray} {addr : EVM.Address} {evm' : EVM.State}
    {z : Bool} (h : newViaEVM cfg evm name value args salt (addr, evm', z)) :
    ∃ ω₀ : List Witness, ∀ ω,
      newViaEVMRun scriptOracle (ω₀ ++ ω) cfg evm name value args salt =
        .ok ((addr, evm', z), ω) := by
  rcases h with ⟨hcode, hcan, -, -, hevm'⟩ | ⟨hcode, hcan⟩
  · rename_i initCode valueWord σ' A'
    refine ⟨[.create ⟨addr, σ', A', z⟩], fun ω => ?_⟩
    subst hevm'
    simp [newViaEVMRun, hcode, (newCanCreateB_iff _ _ _).2 hcan, scriptOracle]
  · rename_i initCode
    refine ⟨[], fun ω => ?_⟩
    have hg : ¬ newCanCreateB evm value initCode = true :=
      fun hb => hcan ((newCanCreateB_iff _ _ _).1 hb)
    simp [newViaEVMRun, hcode, hg, scriptOracle]

/-! ## Permission guards

The ordinary rule's permission hypothesis is the negation of the interpreter's static test. -/

theorem not_assignStatic {origin : VarOrigin} {perm : Bool}
    (h : origin = .localVar ∨ perm = true) :
    ¬ ((origin = .storage ∨ origin = .transient) ∧ perm = false) := by
  rcases h with rfl | rfl <;> simp

theorem not_static {perm : Bool} (h : perm = true) : ¬ perm = false := by simp [h]

theorem not_callStatic {w : EVM.Word} {perm : Bool} (h : w = ⟨0⟩ ∨ perm = true) :
    ¬ (w ≠ ⟨0⟩ ∧ perm = false) := by
  rcases h with rfl | rfl <;> simp

/-! ## Statements -/

mutual

theorem execStmt_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {stmt : Stmt}
    {r : ExecResult} (h : ExecStmt cfg stele evm stmt r) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execStmt fuel scriptOracle (ω ++ rest) cfg stele evm stmt) r rest := by
  match h with
  | .letDecl hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .letDeclRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .letStorage hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .letStorageRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .letGas w =>
    exact stmt_complete [.gas w] 0 fun _ _ _ hover => by
      step execStmt [hover, scriptOracle]; constructor
  | .assign hperm hv hst =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hst]; rw [if_neg (not_assignStatic hperm)]; constructor
  | .assignExprRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .assignStoreRevert hv hst =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv, hst]; constructor
  | .assignStatic hv hst hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hst]; rw [if_pos ⟨.inl trivial, hp⟩]; constructor
  | .assignTransientStatic hv hst hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hst]; rw [if_pos ⟨.inr trivial, hp⟩]; constructor
  | .pushVal hperm hv hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hp]; rw [if_neg (not_static hperm)]; constructor
  | .pushValExprRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .pushValStoreRevert hv hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv, hp]; constructor
  | .pushValStatic hv hp hperm =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hp]; rw [if_pos hperm]; constructor
  | .pushGrow hperm hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_neg (not_static hperm)]; constructor
  | .pushGrowRevert hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hp]; constructor
  | .pushGrowStatic hp hperm =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_pos hperm]; constructor
  | .pop hperm hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_neg (not_static hperm)]; constructor
  | .popRevert hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hp]; constructor
  | .popStatic hp hperm =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_pos hperm]; constructor
  | .delete hperm hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_neg (not_static hperm)]; constructor
  | .deleteRevert hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hp]; constructor
  | .deleteStatic hp hperm =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hp]; rw [if_pos hperm]; constructor
  | .requireTrue hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .requireFalse hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .requireRevert hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .whileFalse hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .whileCondRevert hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .whileTrue hc hb hk =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execStmt_complete hk
    refine stmt_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    exact h₂ fuel (by omega) rest
  | .whileReturn hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel hf rest)
  | .whileRevert hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel hf rest)
  | .whileBreak hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel hf rest)
  | .whileContinue hc hb hk =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execStmt_complete hk
    refine stmt_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    exact h₂ fuel (by omega) rest
  | .whileStatic hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    follow (h₁ fuel hf rest)
  | .«for» hinit hloop =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hinit
    obtain ⟨ω₂, n₂, h₂⟩ := execForLoop_complete hloop
    refine stmt_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest hover => ?_
    step execStmt [hover]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    exact h₂ fuel (by omega) rest
  | .forInitReturn hinit =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hinit
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover]
    follow (h₁ fuel hf rest)
  | .forInitRevert hinit =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hinit
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover]
    follow (h₁ fuel hf rest)
  | .forInitStatic hinit =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hinit
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover]
    follow (h₁ fuel hf rest)
  | .iteTrue hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    exact h₁ fuel hf rest
  | .iteFalse hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hc]
    exact h₁ fuel hf rest
  | .iteCondRevert hc =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hc]; constructor
  | .internalCallReturn hargs hcallee hbind hbody =>
    obtain ⟨ω₁, n₁, h₁⟩ := execFuncBody_complete hbody
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hargs, hcallee, hbind]
    follow (h₁ fuel hf rest)
  | .internalCallRevert hargs hcallee hbind hbody =>
    obtain ⟨ω₁, n₁, h₁⟩ := execFuncBody_complete hbody
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hargs, hcallee, hbind]
    follow (h₁ fuel hf rest)
  | .internalCallArgsRevert hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hargs]; constructor
  | .internalCallStatic hargs hcallee hbind hbody =>
    obtain ⟨ω₁, n₁, h₁⟩ := execFuncBody_complete hbody
    refine stmt_complete ω₁ n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hargs, hcallee, hbind]
    follow (h₁ fuel hf rest)
  | .externalCallSuccess hperm hrecv hval hargs hcall hdec =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hargs, hrun rest, hdec]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .externalCallFailure hperm hrecv hval hargs hcall =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hargs, hrun rest]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .externalCallReturnDecodeRevert hperm hrecv hval hargs hcall hdec =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hargs, hrun rest, hdec]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .externalCallReceiverRevert hrecv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv]; constructor
  | .externalCallSendRevert hrecv hval =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv, hval]; constructor
  | .externalCallArgsRevert hrecv hval hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hargs]; constructor
  | .externalCallStatic hrecv hval hargs hnz hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hargs]; rw [if_pos ⟨hnz, hp⟩]; constructor
  | .lowLevelCallSuccess hperm hrecv hval hcd hcall =>
    obtain ⟨ω₀, hrun⟩ := callViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hcd, hrun rest]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .lowLevelCallFailure hperm hrecv hval hcd hcall =>
    obtain ⟨ω₀, hrun⟩ := callViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hcd, hrun rest]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .lowLevelCallReceiverRevert hrecv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv]; constructor
  | .lowLevelCallSendRevert hrecv hval =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv, hval]; constructor
  | .lowLevelCallDataRevert hrecv hval hcd =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hcd]; constructor
  | .lowLevelCallStatic hrecv hval hcd hnz hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hcd]; rw [if_pos ⟨hnz, hp⟩]; constructor
  | .delegateCallSuccess hrecv hcd hcall =>
    obtain ⟨ω₀, hrun⟩ := delegateCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hcd, hrun rest]; constructor
  | .delegateCallFailure hrecv hcd hcall =>
    obtain ⟨ω₀, hrun⟩ := delegateCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hcd, hrun rest]; constructor
  | .delegateCallReceiverRevert hrecv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv]; constructor
  | .delegateCallDataRevert hrecv hcd =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv, hcd]; constructor
  | .checkedCallSuccess hperm hrecv hval hargs hcall hdec hblock =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hblock
    refine stmt_complete (ω₀ ++ ω₁) n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hrecv, hval, hargs, hrun (ω₁ ++ rest), hdec]
    rw [if_neg (not_callStatic hperm)]
    exact h₁ fuel hf rest
  | .checkedCallFail hperm hrecv hval hargs hcall hblock =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hblock
    refine stmt_complete (ω₀ ++ ω₁) n₁ fun fuel hf rest hover => ?_
    step execStmt [hover, hrecv, hval, hargs, hrun (ω₁ ++ rest)]
    rw [if_neg (not_callStatic hperm)]
    exact h₁ fuel hf rest
  | .checkedCallReturnDecodeRevert hperm hrecv hval hargs hcall hdec =>
    obtain ⟨ω₀, hrun⟩ := typedCallViaEVMRun_complete hcall
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hrecv, hval, hargs, hrun rest, hdec]
      rw [if_neg (not_callStatic hperm)]; constructor
  | .checkedCallReceiverRevert hrecv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv]; constructor
  | .checkedCallSendRevert hrecv hval =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hrecv, hval]; constructor
  | .checkedCallArgsRevert hrecv hval hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hargs]; constructor
  | .checkedCallStatic hrecv hval hargs hnz hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hrecv, hval, hargs]; rw [if_pos ⟨hnz, hp⟩]; constructor
  | .newSuccess hperm hv hargs hsalt hnew =>
    obtain ⟨ω₀, hrun⟩ := newViaEVMRun_complete hnew
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hv, hargs, hsalt, hrun rest]
      rw [if_neg (not_static hperm)]; constructor
  | .newRevert hperm hv hargs hsalt hnew =>
    obtain ⟨ω₀, hrun⟩ := newViaEVMRun_complete hnew
    exact stmt_complete ω₀ 0 fun _ _ rest hover => by
      step execStmt [hover, hv, hargs, hsalt, hrun rest]
      rw [if_neg (not_static hperm)]; constructor
  | .newValueRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .newArgsRevert hv hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv, hargs]; constructor
  | .newStatic hv hargs hsalt hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hargs, hsalt]; rw [if_pos hp]; constructor
  | .«return» hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .returnRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .setImmutable hv hty hfit =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hv, hty]; rw [if_pos hfit]; constructor
  | .setImmutableRevert hv =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hv]; constructor
  | .«break» =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover]; constructor
  | .«continue» =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover]; constructor
  | .emit hperm hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hargs]; rw [if_neg (not_static hperm)]; constructor
  | .emitArgsRevert hargs =>
    exact stmt_complete [] 0 fun _ _ _ hover => by step execStmt [hover, hargs]; constructor
  | .emitStatic hargs hp =>
    exact stmt_complete [] 0 fun _ _ _ hover => by
      step execStmt [hover, hargs]; rw [if_pos hp]; constructor

theorem execForLoop_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {cond : Expr}
    {post body : List Stmt} {r : ExecResult} (h : ExecForLoop cfg stele evm cond post body r) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execForLoop fuel scriptOracle (ω ++ rest) cfg stele evm cond post body) r rest := by
  match h with
  | .falseDone hc =>
    exact loop_complete [] 0 fun _ _ _ => by step execForLoop [hc]; constructor
  | .condRevert hc =>
    exact loop_complete [] 0 fun _ _ _ => by step execForLoop [hc]; constructor
  | .bodyReturn hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine loop_complete ω₁ n₁ fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel hf rest)
  | .bodyRevert hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine loop_complete ω₁ n₁ fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel hf rest)
  | .bodyBreak hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine loop_complete ω₁ n₁ fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel hf rest)
  | .iterate hc hb hp hl =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    obtain ⟨ω₃, n₃, h₃⟩ := execForLoop_complete hl
    refine loop_complete (ω₁ ++ ω₂ ++ ω₃) (n₁ + n₂ + n₃) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ (ω₃ ++ rest)))
    follow (h₂ fuel (by omega) (ω₃ ++ rest))
    exact h₃ fuel (by omega) rest
  | .iteratePostRevert hc hb hp =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    refine loop_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    follow (h₂ fuel (by omega) rest)
  | .continueIter hc hb hp hl =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    obtain ⟨ω₃, n₃, h₃⟩ := execForLoop_complete hl
    refine loop_complete (ω₁ ++ ω₂ ++ ω₃) (n₁ + n₂ + n₃) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ (ω₃ ++ rest)))
    follow (h₂ fuel (by omega) (ω₃ ++ rest))
    exact h₃ fuel (by omega) rest
  | .continuePostRevert hc hb hp =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    refine loop_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    follow (h₂ fuel (by omega) rest)
  | .bodyStatic hc hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine loop_complete ω₁ n₁ fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel hf rest)
  | .iteratePostStatic hc hb hp =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    refine loop_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    follow (h₂ fuel (by omega) rest)
  | .continuePostStatic hc hb hp =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hp
    refine loop_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest => ?_
    step execForLoop [hc]
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    follow (h₂ fuel (by omega) rest)

theorem execBlock_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {stmts : List Stmt}
    {r : ExecResult} (h : ExecBlock cfg stele evm stmts r) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execBlock fuel scriptOracle (ω ++ rest) cfg stele evm stmts) r rest := by
  match h with
  | .nil => exact block_complete [] 0 fun _ _ _ => by step execBlock []; constructor
  | .consNormal hs hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    obtain ⟨ω₂, n₂, h₂⟩ := execBlock_complete hb
    refine block_complete (ω₁ ++ ω₂) (n₁ + n₂) fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel (by omega) (ω₂ ++ rest))
    exact h₂ fuel (by omega) rest
  | .consReturn hs =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    refine block_complete ω₁ n₁ fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel hf rest)
  | .consRevert hs =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    refine block_complete ω₁ n₁ fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel hf rest)
  | .consBreak hs =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    refine block_complete ω₁ n₁ fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel hf rest)
  | .consContinue hs =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    refine block_complete ω₁ n₁ fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel hf rest)
  | .consStatic hs =>
    obtain ⟨ω₁, n₁, h₁⟩ := execStmt_complete hs
    refine block_complete ω₁ n₁ fun fuel hf rest => ?_
    step execBlock []
    follow (h₁ fuel hf rest)

theorem execFuncBody_complete {cfg : Config} {stele : Frame} {evm : EVM.State} {body : List Stmt}
    {r : ExecResult} (h : ExecFuncBody cfg stele evm body r) :
    ∃ ω n, ∀ fuel, n ≤ fuel → ∀ rest,
      Reaches (execFuncBody fuel scriptOracle (ω ++ rest) cfg stele evm body) r rest := by
  match h with
  | .execBlockOK hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)
  | .execBlockRet hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)
  | .execBlockRevert hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)
  | .execBlockBreak hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)
  | .execBlockContinue hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)
  | .execBlockStatic hb =>
    obtain ⟨ω₁, n₁, h₁⟩ := execBlock_complete hb
    refine body_complete ω₁ n₁ fun fuel hf rest => ?_
    step execFuncBody []
    follow (h₁ fuel hf rest)

end

/-! ## Messages -/

/-- Equal `ByteArray`s under `==` have equal size (the twin of `Reasoning/Stepping.lean`, which
    cannot be imported here). -/
theorem size_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a.size = b.size :=
  congrArg ByteArray.size
    (ByteArray.ext (eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)))

/-- Empty calldata matches no selector: a selector has four bytes. -/
theorem selectorDispatchMsg_eq_none_of_size {contract : ContractDecl} {calldata : ByteArray}
    (h : calldata.size = 0) : selectorDispatchMsg contract calldata = none := by
  unfold selectorDispatchMsg
  simp only [List.map_map]
  rw [List.find?_eq_none.2]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨t, -, rfl⟩ := hx
  show ¬ ((KEC (transitionSigStr t).toByteArray).extract 0 4 == calldata.extract 0 4) = true
  intro heq
  have hs := size_eq_of_beq heq
  have h32 : (KEC (transitionSigStr t).toByteArray).size = 32 := Crypto.Keccak256.hash_size_eq_32 _
  rw [ByteArray.size_extract, ByteArray.size_extract, h, h32] at hs
  exact absurd hs (by decide)

theorem steleExecRun_complete {cfg : Config} {contract : ContractDecl} {immutables : Store}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {r : ExecResult}
    {rc : ReturnConvention} (h : steleExec cfg contract immutables σ σ₀ g A I r rc) :
    ∃ fuel ω p,
      steleExecRun fuel scriptOracle ω cfg contract immutables σ σ₀ g A I =
        (.ran p.1 rc, p.2) ∧ Reaches p r [] := by
  cases h with
  | noMatch hd =>
    unfold dispatchMsg at hd
    split at hd
    · cases hd
    · next hsel =>
      split at hd
      · cases hd
      · next hrecv =>
        refine ⟨0, [], (.result .noMatch, []), ?_, .hit⟩
        simp only [steleExecRun, hsel, hrecv, hd]
  | decodingFailed hsel hdec =>
    refine ⟨0, [], (.result .decodingFailed, []), ?_, .hit⟩
    simp only [steleExecRun, hsel, hdec]
  | intro hsel hsig hdec hevm hbody =>
    subst hsig hevm
    obtain ⟨ω, n, hn⟩ := execFuncBody_complete hbody
    refine ⟨n, ω, _, ?_, by simpa using hn n le_rfl []⟩
    simp only [steleExecRun, hsel, hdec, execTransitionBody]
    rfl
  | receive hrecv hp hr hevm hbody =>
    subst hevm
    have hsel : selectorDispatchMsg contract I.calldata = none := by
      apply selectorDispatchMsg_eq_none_of_size
      unfold receiveDispatchMsg at hrecv
      split at hrecv
      · assumption
      · cases hrecv
    obtain ⟨ω, n, hn⟩ := execFuncBody_complete hbody
    refine ⟨n, ω, _, ?_, by simpa using hn n le_rfl []⟩
    simp only [steleExecRun, hsel, hrecv, execTransitionBody]
    rw [if_pos (by simp [hp, hr])]
    rfl
  | fallback hsel hrecv hfb hargs hrc hevm hbody =>
    subst hevm
    obtain ⟨ω, n, hn⟩ := execFuncBody_complete hbody
    refine ⟨n, ω, _, ?_, by simpa using hn n le_rfl []⟩
    simp only [steleExecRun, hsel, hrecv, hfb, hargs, hrc, execTransitionBody]
    rfl

theorem steleCtorExecRun_complete {cfg : Config} {contract : ContractDecl} {args : List Value}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {r : ExecResult}
    (h : steleCtorExec cfg contract args σ σ₀ g A I r) :
    ∃ fuel ω p,
      steleCtorExecRun fuel scriptOracle ω cfg contract args σ σ₀ g A I = some p ∧
        Reaches p r [] := by
  cases h with
  | intro hevm hlen hstore hbody =>
    subst hevm hstore
    obtain ⟨ω, n, hn⟩ := execFuncBody_complete hbody
    refine ⟨n, ω, _, ?_, by simpa using hn n le_rfl []⟩
    simp only [steleCtorExecRun, hlen, if_true, execTransitionBody]
    rfl

end Stele.Interp
