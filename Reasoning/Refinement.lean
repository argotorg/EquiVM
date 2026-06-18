import Reasoning.Dispatch

/-!
# Refinement — proof-side bridges: straight-line EVM runs ⟹ the equivalence statements

Only `runtimeEquivalenceFor` lives in `Solm.Equiv`.  The *relational* per-block and per-function
judgments — `equivStmts` (the statement-level logic) and `equivTransition` (one function's EVM body
≈ its Solm body) — mention the EVM `RD`/`RDret`/`RDrev` discipline, so they live here, together with
the bridges up the ladder:

* segment rules (`nil`/`consNormal`/`consReturn`/`consRevert`/`consequence`) — discharge a
  straight-line statement segment by symbolic execution on both sides (`RD` + `ExecStmt`).
* `equivStmts.toTransition` — body-level logic ⟹ `equivTransition`.
* `equivTransition.toRuntime` — `equivTransition` + dispatch/decoding ⟹ `runtimeEquivalenceFor`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Refinement

/-- The persistent **world** carried by an EVM state: its created accounts and storage map.  This is
    the only part of the state the two executions are required to agree on (between external calls). -/
def worldOf (s : State) : Batteries.RBSet AccountAddress compare × AccountMap :=
  (s.createdAccounts, s.accountMap)

/-- A relation coupling an EVM reach-`Cursor` to the Solm execution state (frame + threaded EVM
    state).  It carries the *non-`pc`, non-world* part of the coupling — e.g. which stack/memory
    slots hold which locals — and is only constrained where it matters (call arguments, return
    value).  The structural rules are agnostic to what a `StateRel` actually says. -/
abbrev StateRel := Cursor → Frame → State → Prop

/-- **Statement-level equivalence** `{R} stmts ~ bytecode@pc {Q}`.

    From an entry cursor the run has reached (`cur.pc = pc`, `RDc`), with the world coupled
    (`cur.world = worldOf evm`) and the rest coupled by `R`, the Solm block *runs* (this is asserted,
    not assumed — both sides execute) to some `result`, and the bytecode lands in the matching place:
    * `.ok` (fall through) → some exit cursor still coupled by `Q`, worlds still agreeing;
    * `.returned rv` → the run `RETURN`s output `o` with the Solm world, `o` ABI-encoding `rv`;
    * `.reverted` → the run `REVERT`s;
    * `break`/`continue` out of a top-level block is rejected (`False`). -/
def equivStmts (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (returnType : Option ABIType)
    (pc : UInt256) (R : StateRel) (stmts : List Stmt) (Q : StateRel) : Prop :=
  ∀ cur k C frame evm,
    cur.pc = pc →
    RDc code ee g s0 cur k C →
    cur.world = worldOf evm →
    R cur frame evm →
    ∃ result, ExecBlock cfg frame evm stmts result ∧
      (match result with
       | .ok frame' evm' =>
           ∃ cur' k' C', RDc code ee g s0 cur' k' C' ∧ cur'.world = worldOf evm'
             ∧ Q cur' frame' evm'
       | .returned _ evm' rv =>
           ∃ o, RDret code g s0 (worldOf evm') o ∧ returnEquiv o rv returnType
       | .reverted =>
           RDrev code g s0
       | .break _ _ | .continue _ _ =>
           False)

/-! ### Structural rules — symbolic execution on both sides, statement by statement -/

/-- **nil** — the empty block keeps the cursor and the relation unchanged. -/
theorem equivStmts.nil {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc : UInt256} (R : StateRel) :
    equivStmts code ee g s0 cfg returnType pc R [] R := by
  intro cur k C frame evm _hpc hRD hw hR
  exact ⟨.ok frame evm, ExecBlock.nil, cur, k, C, hRD, hw, hR⟩

/-- **consNormal** — peel a fall-through head statement.  `hhead` runs the head in Solm
    (`ExecStmt … .ok`) and walks its bytecode (`RDc … cur'`, exit pc `pc'`), re-establishing the
    coupling `R'`; `hrest` is the advanced judgment for the tail.  This is "run some bytecode with
    `RD`, run a Solm statement, move to an advanced `equivStmts`." -/
theorem equivStmts.consNormal {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc pc' : UInt256} {R R' Q : StateRel}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm' cur' k' C',
          cur'.pc = pc' ∧
          ExecStmt cfg frame evm s (.ok frame' evm') ∧
          RDc code ee g s0 cur' k' C' ∧
          cur'.world = worldOf evm' ∧
          R' cur' frame' evm')
    (hrest : equivStmts code ee g s0 cfg returnType pc' R' rest Q) :
    equivStmts code ee g s0 cfg returnType pc R (s :: rest) Q := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', cur', k', C', hpc', hstmt, hRD', hw', hR'⟩ := hhead cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ := hrest cur' k' C' frame' evm' hpc' hRD' hw' hR'
  exact ⟨result, ExecBlock.consNormal hstmt hblock, hmatch⟩

/-- **consReturn** — the head statement `return`s.  Its bytecode `RETURN`s (`RDret`), matching the
    returned value; the tail is never reached. -/
theorem equivStmts.consReturn {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc : UInt256} {R Q : StateRel}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm' rv o,
          ExecStmt cfg frame evm s (.returned frame' evm' rv) ∧
          RDret code g s0 (worldOf evm') o ∧
          returnEquiv o rv returnType) :
    equivStmts code ee g s0 cfg returnType pc R (s :: rest) Q := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', rv, o, hstmt, hRDret, henc⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.returned frame' evm' rv, ExecBlock.consReturn hstmt, o, hRDret, henc⟩

/-- **consRevert** — the head statement `revert`s.  Its bytecode `REVERT`s (`RDrev`); the tail is
    never reached. -/
theorem equivStmts.consRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc : UInt256} {R Q : StateRel}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ExecStmt cfg frame evm s .reverted ∧ RDrev code g s0) :
    equivStmts code ee g s0 cfg returnType pc R (s :: rest) Q := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨hstmt, hrev⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.reverted, ExecBlock.consRevert hstmt, hrev⟩

/-- **external call (success / continue)** — peel a *successful* external call.  The bytecode's
    `CALL` (`RD.call`) and Solm's `externalCall` (`externalCallViaEVM`) invoke the **same** `Θ`, so
    the opaque result `(z, evm', out)` coincides on both sides by construction; `hcall` packages that
    bridged fact (obtained from `RD.call`) together with the post-`CALL` cursor.  On `z = true` with a
    decoding return, `retVar` binds the decoded `value` and execution continues at `pc'`.

    A call that **reverts** — `z = false`, or a return that does not decode — is *not* a new rule:
    it is `consRevert` with `ExecStmt.externalCallFailure` / `externalCallReturnDecodeRevert`.  Which
    branch fires is dictated by the (opaque, but deterministic) `Θ` result, exactly as the contract's
    post-`CALL` bytecode (`ISZERO …` / the return-size check) branches on it. -/
theorem equivStmts.externalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc pc' : UInt256} {R R' Q : StateRel}
    {receiver eth : Expr} {name : Ident} {args : List Expr} {retVar : Ident} {rest : List Stmt}
    (hcall : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ (target : EVM.Address) (sendVal : ℤ) (argVals : List Value) (evm' : State)
          (out : ByteArray) (value : Value) (cur' : Cursor) (k' C' : ℕ),
          evalExpr? cfg frame evm receiver = .ok (.address target) ∧
          evalExpr? cfg frame evm eth = .ok (.int sendVal) ∧
          evalExprs? cfg frame evm args = .ok argVals ∧
          externalCallViaEVM cfg evm (EVM.address target) name sendVal argVals (true, evm', out) ∧
          cfg.externalABI.decode? name out = some value ∧
          cur'.pc = pc' ∧
          RDc code ee g s0 cur' k' C' ∧
          cur'.world = worldOf evm' ∧
          R' cur' { frame with locals := frame.locals.insert retVar value } evm')
    (hrest : equivStmts code ee g s0 cfg returnType pc' R' rest Q) :
    equivStmts code ee g s0 cfg returnType pc R
      (.externalCall receiver name eth args retVar :: rest) Q := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨target, sendVal, argVals, evm', out, value, cur', k', C',
    hrec, heth, hargs, hcallEVM, hdec, hpc', hRD', hw', hR'⟩ := hcall cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ :=
    hrest cur' k' C' { frame with locals := frame.locals.insert retVar value } evm' hpc' hRD' hw' hR'
  exact ⟨result,
    ExecBlock.consNormal (ExecStmt.externalCallSuccess hrec heth hargs hcallEVM hdec) hblock, hmatch⟩

/-- **consequence (strengthen the precondition).** -/
theorem equivStmts.consequencePre {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc : UInt256} {R R' Q : StateRel} {stmts}
    (himp : ∀ cur frame evm, R' cur frame evm → R cur frame evm)
    (h : equivStmts code ee g s0 cfg returnType pc R stmts Q) :
    equivStmts code ee g s0 cfg returnType pc R' stmts Q := by
  intro cur k C frame evm hpc hRD hw hR'
  exact h cur k C frame evm hpc hRD hw (himp cur frame evm hR')

/-- **consequence (weaken the postcondition)** — only the fall-through case carries `Q`. -/
theorem equivStmts.consequencePost {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc : UInt256} {R Q Q' : StateRel} {stmts}
    (himp : ∀ cur frame evm, Q cur frame evm → Q' cur frame evm)
    (h : equivStmts code ee g s0 cfg returnType pc R stmts Q) :
    equivStmts code ee g s0 cfg returnType pc R stmts Q' := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ := h cur k C frame evm hpc hRD hw hR
  cases result with
  | ok frame' evm' =>
      obtain ⟨cur', k', C', hRD', hw', hQ⟩ := hmatch
      exact ⟨_, hblock, cur', k', C', hRD', hw', himp cur' frame' evm' hQ⟩
  | returned _ evm' rv => exact ⟨_, hblock, hmatch⟩
  | reverted => exact ⟨_, hblock, hmatch⟩
  | «break» _ _ => exact hmatch.elim
  | «continue» _ _ => exact hmatch.elim

/-! ### Sequencing (chunk composition) -/

/-- Append helper: if `s1` falls through to `(f1, e1)`, running `s2` from there is running `s1 ++ s2`. -/
theorem execBlock_append {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e f1 e1 r}, ExecBlock cfg f e s1 (.ok f1 e1) → ExecBlock cfg f1 e1 s2 r →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e f1 e1 r h1 h2; cases h1; exact h2
  | cons stmt rest ih =>
      intro f e f1 e1 r h1 h2
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest h2)

/-- Append helper: if `s1` *terminates* (any non-`.ok` result), `s1 ++ s2` terminates the same way —
    `s2` never runs. -/
theorem execBlock_append_term {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e r}, ExecBlock cfg f e s1 r → (∀ f' e', r ≠ .ok f' e') →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e r h1 hterm; cases h1; exact absurd rfl (hterm _ _)
  | cons stmt rest ih =>
      intro f e r h1 hterm
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest hterm)
      | consReturn hstmt => exact ExecBlock.consReturn hstmt
      | consRevert hstmt => exact ExecBlock.consRevert hstmt
      | consBreak hstmt => exact ExecBlock.consBreak hstmt
      | consContinue hstmt => exact ExecBlock.consContinue hstmt

/-- **seq (chunk composition).**  Glue two chunks at a chosen boundary `pcmid`: `s1` runs from `pc`
    to a fall-through coupled by `S` (which pins the seam pc, `hmid`), then `s2` runs from `pcmid` to
    `Q`.  If `s1` instead returns/reverts, that is already the whole block's result.  Composition needs
    no transitivity — the EVM facts (`RDc`/`RDret`/`RDrev`) are absolute from `s0`, so they carry
    through verbatim. -/
theorem equivStmts.seq {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {returnType : Option ABIType} {pc pcmid : UInt256} {R S Q : StateRel}
    {s1 s2 : List Stmt}
    (hmid : ∀ cur frame evm, S cur frame evm → cur.pc = pcmid)
    (h1 : equivStmts code ee g s0 cfg returnType pc R s1 S)
    (h2 : equivStmts code ee g s0 cfg returnType pcmid S s2 Q) :
    equivStmts code ee g s0 cfg returnType pc R (s1 ++ s2) Q := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨result1, hblock1, hmatch1⟩ := h1 cur k C frame evm hpc hRD hw hR
  cases result1 with
  | ok f1 e1 =>
      obtain ⟨cur1, k1, C1, hRD1, hw1, hS⟩ := hmatch1
      obtain ⟨result2, hblock2, hmatch2⟩ :=
        h2 cur1 k1 C1 f1 e1 (hmid cur1 f1 e1 hS) hRD1 hw1 hS
      exact ⟨result2, execBlock_append hblock1 hblock2, hmatch2⟩
  | returned f1 e1 rv =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | reverted =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | «break» f1 e1 => exact hmatch1.elim
  | «continue» f1 e1 => exact hmatch1.elim

/-! ### Up to the function and the contract -/

/-- Per-function equivalence: from `initState`, the EVM body and the Solm body `t.body` (run with
    `callargs`) reach a matching terminal result — both return ABI-coupled values with matching final
    world, or both revert. -/
inductive equivTransition (cfg : Config) (contract : ContractDecl) (t : TransitionDecl)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : Sat256)
    (code : ByteArray) (callargs : Store) : Prop where
  | returns {o : ByteArray} {cs : Frame} {retVal} {evm'' : State}
      {world : Batteries.RBSet AccountAddress compare × AccountMap} :
      RDret code g (initState cA gh bl σ σ₀ g A I) world o →
      ExecTransitionBody cfg contract (initState cA gh bl σ σ₀ g A I) callargs t.body
        (.returned cs evm'' retVal) →
      world = (evm''.createdAccounts, evm''.accountMap) →
      returnEquiv o retVal t.returnType →
      equivTransition cfg contract t cA gh bl σ σ₀ A I g code callargs
  | reverts :
      RDrev code g (initState cA gh bl σ σ₀ g A I) →
      ExecTransitionBody cfg contract (initState cA gh bl σ σ₀ g A I) callargs t.body .reverted →
      equivTransition cfg contract t cA gh bl σ σ₀ A I g code callargs

/-- `equivTransition` + the selector dispatches to `t` + its args decode ⟹ `runtimeEquivalenceFor`. -/
theorem equivTransition.toRuntime {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray} {callargs : Store}
    (hcode : I.code = code)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = some callargs)
    (h : equivTransition cfg contract t cA gh bl σ σ₀ A I g code callargs) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I := by
  cases h with
  | returns hret hbody hAcc henc => exact hret.reEquivExecutionGen hcode hd hdec hbody hAcc henc
  | reverts hrev hbody => exact hrev.reEquivExecutionRevert hcode hd hdec hbody

/-- **Bridge** — the body-level `equivStmts` ⟹ `equivTransition`.  The dispatcher reached the body
    entry (`hRD` at `pcEntry`) under the entry coupling (`hR`, `hworld`); `h` runs the body and reads
    off the matching EVM behaviour.  `.returned`/`.reverted` close directly; the `.ok` fall-through
    (body runs off the end → `ExecFuncBody.execBlockOK` gives an implicit `return none`) hands the
    post-body cursor to `hfall`, the epilogue's trailing `RETURN`. -/
theorem equivStmts.toTransition {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray} {callargs : Store} {R Q : StateRel}
    {pcEntry : UInt256} {entry : Cursor} {kE CE : ℕ}
    (hpc : entry.pc = pcEntry)
    (hRD : RDc code I g (initState cA gh bl σ σ₀ g A I) entry kE CE)
    (hworld : entry.world = worldOf (initState cA gh bl σ σ₀ g A I))
    (hR : R entry { contract := contract, locals := callargs } (initState cA gh bl σ σ₀ g A I))
    (h : equivStmts code I g (initState cA gh bl σ σ₀ g A I) cfg t.returnType pcEntry R t.body Q)
    (hfall : ∀ cur' k' C' frame' evm',
        RDc code I g (initState cA gh bl σ σ₀ g A I) cur' k' C' → cur'.world = worldOf evm' →
        Q cur' frame' evm' →
        ∃ o, RDret code g (initState cA gh bl σ σ₀ g A I) (worldOf evm') o
          ∧ returnEquiv o none t.returnType) :
    equivTransition cfg contract t cA gh bl σ σ₀ A I g code callargs := by
  obtain ⟨result, hbody, hmatch⟩ :=
    h entry kE CE { contract := contract, locals := callargs } (initState cA gh bl σ σ₀ g A I)
      hpc hRD hworld hR
  cases result with
  | ok frame' evm' =>
      obtain ⟨cur', k', C', hRD', hw', hQ⟩ := hmatch
      obtain ⟨o, hRDret, henc⟩ := hfall cur' k' C' frame' evm' hRD' hw' hQ
      exact .returns hRDret (ExecFuncBody.execBlockOK hbody) rfl henc
  | returned cs evm' rv =>
      obtain ⟨o, hRDret, henc⟩ := hmatch
      exact .returns hRDret (ExecFuncBody.execBlockRet hbody) rfl henc
  | reverted => exact .reverts hmatch (ExecFuncBody.execBlockRevert hbody)
  | «break» _ _ => exact hmatch.elim
  | «continue» _ _ => exact hmatch.elim

end Reasoning.Refinement
